`include "v/cache.vh"
import cache_pkg::*;

// REVISIT (11/2, verify expectation of word aligned accesses)
module cache #(
    parameter block_width_p,      // words per block
    parameter sets_p,            // number of sets
    parameter ways_p,            // number of ways
    parameter dma_data_width_p,  // bus transfer size in words

    localparam core_cache_pkt_width_lp = `core_cache_pkt_width,
    localparam cache_bus_pkt_width_lp  = `cache_bus_pkt_width(dma_data_width_p)
)(
    input  logic clk_i,
    input  logic nreset_i,

    // Core Cache Interface
    input  logic                               cc_valid_i,
    output logic                               cc_ready_o,
    input  logic [core_cache_pkt_width_lp-1:0] cc_pkt_i,

    output logic            cc_valid_o,
    output logic [31:0]     cc_rdata_o,

    // Cache Bus Interface
    output logic                              cb_valid_o,
    input  logic                              cb_yumi_i,
    output logic [cache_bus_pkt_width_lp-1:0] cb_pkt_o,

    input  logic                           cb_valid_i,
    input  logic [(dma_data_width_p*32)-1:0] cb_data_i

    // REVISIT SNOOP
    // input  logic [31:0] snp_addr_i,
    // input  logic        snp_valid_i,
    // input logic         snp_wr_i
);

    // For counting
    localparam num_blocks_lp    = sets_p * ways_p;
    localparam ways_size_lp     = $clog2(ways_p);
    localparam wr_mask_width_lp = dma_data_width_p << 2;

    // For indexing
    localparam offset_width_lp    = $clog2(block_width_p) + 2; // offset within block, add 2 because block size in words
    localparam index_width_lp     = $clog2(sets_p);
    localparam tag_width_lp       = 32 - offset_width_lp - index_width_lp;
    localparam state_width_lp     = $bits(block_state_t);
    localparam tag_state_width_lp = (ways_p * state_width_lp) + tag_width_lp;

    // Data transfer ratio
    localparam dma_blk_ratio_lp      = block_width_p / dma_data_width_p;
    localparam dma_blk_size_ratio_lp = $clog2(dma_blk_ratio_lp);
    localparam dma_data_size_lp      = $clog2(dma_data_width_p);
    localparam dma_byte_width_lp     = dma_data_width_p << 2;
    localparam dma_byte_size_lp      = $clog2(dma_byte_width_lp);
    localparam dma_bit_size_lp       = dma_data_size_lp + 5;

    `declare_cache_bus_pkt_t(dma_data_width_p);
    `declare_cache_block_t(tag_width_lp, block_width_p);

    core_cache_pkt_t cc_pkt, cc_pkt_r;
    assign cc_pkt = cc_pkt_i;

    cache_bus_pkt_t cb_pkt;
    assign cb_pkt_o = cb_pkt;

    logic [ways_p-1:0] [tag_width_lp-1:0]       mem_tag_rdata;
    logic [ways_p-1:0] [state_width_lp-1:0]     mem_state_rdata;
    logic [ways_p-1:0] [(dma_data_width_p*32)-1:0] mem_data_rdata;

    logic rst_seq_done;
    logic [index_width_lp:0] rst_count_r, rst_count_n;
    
    assign rst_seq_done = rst_count_r == sets_p;
    assign rst_count_n  = rst_count_r + {'0, ~rst_seq_done};

    always_ff @(posedge clk_i) begin
        if (~nreset_i) begin
            rst_count_r <= '0;
        end else begin
            rst_count_r <= rst_count_n;
        end
    end

    // Data loaded from cache on transition to s_lookup
    logic [ways_p-1:0] [tag_width_lp-1:0] set_tag_r, set_tag;
    block_state_t [ways_p-1:0] set_state_r, set_state;
    logic [ways_p-1:0] [(dma_data_width_p*32)-1:0] set_data_r, set_data;

    logic [index_width_lp-1:0] set_index, set_index_r;
    logic write_complete, cc_valid_ready, cc_valid_ready_r;

    logic [31:0] cc_rdata_src;
    logic [31:0] main_mem_rdata;

    typedef enum logic [2:0] {s_idle, s_lookup, s_alloc_wr, s_alloc_rd, s_alloc_rx} cache_control_t;
    cache_control_t cache_state_r, cache_state_n;

    assign cc_valid_ready = cc_valid_i & cc_ready_o;
    assign set_index = cc_valid_ready? cc_pkt.addr[offset_width_lp+:index_width_lp]: set_index_r;
    assign set_index_r = cc_pkt_r.addr[offset_width_lp+:index_width_lp];

    // Load block tag, state, data, and lru for all blocks in set upon receiving request
    always_comb begin
        for (int w = 0; w < ways_p; w++) begin
            set_tag[w]   = cc_valid_ready_r? mem_tag_rdata[w]: set_tag_r[w];
            set_state[w] = cc_valid_ready_r? block_state_t'(mem_state_rdata[w]): set_state_r[w];
            set_data[w]  = cc_valid_ready_r? mem_data_rdata[w]: set_data_r[w];
        end
    end

    // Pipe stage 1
    always_ff @(posedge clk_i) begin
        if (~nreset_i)
            cc_valid_ready_r <= 1'b0;
        else 
            cc_valid_ready_r <= cc_valid_ready;

        cc_pkt_r    <= cc_valid_ready? cc_pkt: cc_pkt_r;
        set_tag_r   <= set_tag;
        set_state_r <= set_state;
        set_data_r  <= set_data;
    end

    logic tx_done, rx_done, rx_start;
    logic read_write_miss, set_full, send_eviction;
    logic [ways_size_lp-1:0] way_index, way_index_n, way_index_r, block_hit_index;
    logic [ways_p-1:0] block_state_invalid, block_hit;
    logic [31:0] cb_addr_lo; //evict_block_address;

    always_comb begin
        read_write_miss = cc_valid_ready_r;
        set_full = 1'b1;

        for (int w = 0; w < ways_p; w++) begin
            block_state_invalid[w] = set_state[w] == s_invalid;
            block_hit[w] = ~block_state_invalid[w] & set_tag[w] == cc_pkt_r.addr[31-:tag_width_lp];

            // not a miss if any valid way holds a matching tag
            read_write_miss = read_write_miss & ~block_hit[w];
            set_full = set_full & ~block_state_invalid[w];
        end
    end

    // pseudo LRU tree
    logic [ways_size_lp-1:0] lru_way_index, open_way_index;
    genvar s, w;

    generate
        if (ways_p == 1) begin : gen_direct_mapped
            assign lru_way_index = 1'b0;
            assign open_way_index = 1'b0;
        end else begin : gen_associative
            logic cache_access;
            logic [sets_p-1:0] set_access;
            logic [sets_p-1:0] [ways_size_lp-1:0] lru_set_way_index;

            assign cache_access = rx_start | (cache_state_r == s_lookup & ~read_write_miss);

            always_comb begin                
                for (int s = 0; s < sets_p; s++) begin
                    set_access[s] = cache_access & set_index_r == index_width_lp'(s);
                end
                
                lru_way_index = lru_set_way_index[set_index_r]; 
            end

            // Generate an LRU block for each set
            for (s = 0; s < sets_p; s++) begin : gen_lru
                index_lru #(
                    .size_p(ways_size_lp)
                ) u_index_lru (
                    .clk_i, 
                    .nreset_i,
                    .valid_i(set_access[s]),
                    .index_i(way_index),
                    .index_o(lru_set_way_index[s])
                );
            end

            // 2-way pLRU guaruntees block will not be evicted unless set is full
            if (ways_p == 2) begin
                assign open_way_index = lru_way_index;
            end else begin
                always_comb begin // priority encoder
                    open_way_index = '0;
                    for (int w = 0; w < ways_p; w++) begin
                        open_way_index = block_state_invalid[w]? ways_size_lp'(w): open_way_index;
                    end
                end
            end
        end
    endgenerate

    // Since everything is a power of 2 this is equal to (cc_pkt_r / dma_data_width_p)
    // ib = intra-block
    logic [dma_blk_size_ratio_lp-1:0] cc_pkt_rx_addr, cc_pkt_rx_addr_r;
    logic [dma_data_size_lp+1:0] cc_pkt_ib_byte_offset_r;
    logic [dma_data_size_lp+4:0] cc_pkt_ib_bit_offset_r; // intra-block offset
    assign cc_pkt_ib_byte_offset_r = cc_pkt_r.addr[dma_data_size_lp+1:0];
    assign cc_pkt_ib_bit_offset_r  = cc_pkt_ib_byte_offset_r << 3;

    // if an open way exists, it will be at way_index so if way_index is modified then the set is full and we must evict 
    // check cc_pkt_rx_addr_r since we will only have the rd data ready this cycle if we read it based on the cc_pkt addr
    // REVISIT (check timing)
    assign send_eviction = (cache_state_r == s_lookup & read_write_miss & set_state[way_index] == s_modified & cc_pkt_rx_addr == '0) ||
        (cache_state_r == s_alloc_wr);

    // if not miss then matching index, else if miss but not full open index, else eviction index
    always_comb begin
        if (read_write_miss) begin
            way_index_n = set_full? lru_way_index: open_way_index;
        end else begin
            way_index_n = '0;
            for (int i = 0; i < ways_p; i++) begin
                way_index_n = way_index_n | ({ways_size_lp{block_hit[i]}} & ways_size_lp'(i));
            end
        end
    end

    // Cache State Logic
    always_comb begin
        case (cache_state_r)
            s_idle:     cache_state_n = cc_valid_ready? s_lookup: s_idle;

            s_lookup: begin
                if (read_write_miss) begin
                    if (set_state[way_index] == s_modified)
                        cache_state_n = tx_done? s_alloc_rd: s_alloc_wr;
                    else
                        cache_state_n = tx_done? s_alloc_rx: s_alloc_rd;
                end else begin
                    cache_state_n = s_idle;
                end
            end
            s_alloc_wr: cache_state_n = tx_done? s_alloc_rd: s_alloc_wr;
            s_alloc_rd: cache_state_n = tx_done? s_alloc_rx: s_alloc_rd;
            s_alloc_rx: cache_state_n = rx_done? s_idle: s_alloc_rx;
            default:    cache_state_n = s_idle;
        endcase
    end

    always_ff @(posedge clk_i) begin
        if (~nreset_i)
            cache_state_r <= s_idle;
        else
            cache_state_r <= cache_state_n;
    end

    logic cache_mem_write, write_dma_block, match_dma_block;
    logic [dma_blk_size_ratio_lp-1:0] rx_count_r, tx_count_r;

    assign cache_mem_write = cache_state_r == s_lookup & ~read_write_miss & cc_pkt_r.we;
    assign write_complete = cc_valid_o & cc_pkt_r.we;

    assign cc_ready_o = (cache_state_r == s_idle) & rst_seq_done;
    assign cc_valid_o = cache_state_r != s_idle & cache_state_n == s_idle;

    generate
        if (block_width_p != dma_data_width_p) begin : block_width_not_dma_data_width
            logic tx_count_incr;
            logic [dma_blk_size_ratio_lp-1:0] rx_count_n, tx_count_n;
            logic [offset_width_lp-1:0] tx_addr_offset;
            logic [31:0] main_mem_rdata_r;

            assign rx_done  = rx_count_r == '1 & cb_valid_i;
            assign rx_start = rx_count_r == '0 & cb_valid_i;
            assign tx_done  = (cb_valid_o & cb_yumi_i) & (tx_count_r == '1);
            assign tx_count_incr = cb_valid_o & cb_yumi_i;

            assign rx_count_n = rx_count_r + {'0, cb_valid_i};
            assign tx_count_n = tx_count_r + {'0, tx_count_incr};
            
            always_ff @(posedge clk_i) begin
                if (~nreset_i) begin
                    rx_count_r <= '0;
                    tx_count_r <= '0;
                end else begin
                    rx_count_r <= rx_count_n;
                    tx_count_r <= tx_count_n;
                end
            end
                        
            assign cc_pkt_rx_addr   = cc_pkt.addr[offset_width_lp-1 -: dma_blk_size_ratio_lp];
            assign cc_pkt_rx_addr_r = cc_pkt_r.addr[offset_width_lp-1 -: dma_blk_size_ratio_lp];

            assign tx_addr_offset = tx_count_r << (dma_data_size_lp + 2);

            assign match_dma_block = (rx_count_r == cc_pkt_rx_addr_r) & cb_valid_i;
            assign write_dma_block = cc_pkt_r.we & match_dma_block;
            
            assign cb_pkt.wdata = set_data[way_index];
            // assign evict_block_address = {set_tag[way_index], cc_pkt_r.addr[offset_width_lp+:index_width_lp], tx_addr_offset}; 
            assign cb_addr_lo = { send_eviction? set_tag[way_index]: cc_pkt_r.addr[31 -: tag_width_lp], cc_pkt_r.addr[offset_width_lp+:index_width_lp], tx_addr_offset};
            // rdata is the loaded block that matches, either from this cycle or previously
            assign main_mem_rdata = match_dma_block? cb_data_i[cc_pkt_ib_bit_offset_r +: 32]: main_mem_rdata_r;
            always_ff @(posedge clk_i) begin
                main_mem_rdata_r <= main_mem_rdata;
            end

        end else begin : block_size_eq_dma_data_width
            assign tx_done  = cb_yumi_i;
            assign rx_done  = cb_valid_i;
            assign rx_start = cb_valid_i; 
            assign rx_count_r = '0;
            assign tx_count_r = '0;
            
            assign cc_pkt_rx_addr   = '0;
            assign cc_pkt_rx_addr_r = '0;

            assign match_dma_block = cb_valid_i;
            assign write_dma_block = match_dma_block & cc_pkt_r.we;
            
            assign cb_pkt.wdata = set_data[way_index]; // eviction index stored in way_index
            assign main_mem_rdata = cb_data_i[cc_pkt_ib_bit_offset_r +: 32];
            // assign evict_block_address = {set_tag[way_index], cc_pkt_r.addr[offset_width_lp+:index_width_lp], offset_width_lp'(0)};
            assign cb_addr_lo = { send_eviction? set_tag[way_index]: cc_pkt_r.addr[31 -: tag_width_lp], cc_pkt_r.addr[offset_width_lp+:index_width_lp], offset_width_lp'(0)};
        end
    endgenerate    

    logic [(dma_data_width_p*32)-1:0] main_mem_wdata;

    always_comb begin
        main_mem_wdata = cb_data_i;

        if (cc_pkt_r.be[0] & write_dma_block)
            main_mem_wdata[cc_pkt_ib_bit_offset_r +:8] = cc_pkt_r.wdata[7:0];
        if (cc_pkt_r.be[1] & write_dma_block)
            main_mem_wdata[cc_pkt_ib_bit_offset_r+8 +:8] = cc_pkt_r.wdata[15:8];
        if (cc_pkt_r.be[2] & write_dma_block)
            main_mem_wdata[cc_pkt_ib_bit_offset_r+16 +:8] = cc_pkt_r.wdata[23:16];
        if (cc_pkt_r.be[3] & write_dma_block)
            main_mem_wdata[cc_pkt_ib_bit_offset_r+24 +:8] = cc_pkt_r.wdata[31:24];
    end

    logic reset, mem_ways_rd;
    assign reset = ~nreset_i;
    
    logic [ways_p-1:0] mem_tag_wr, mem_tag_valid;
    logic [tag_width_lp-1:0] mem_tag_n;

    logic mem_state_wr_any_way;
    logic [index_width_lp-1:0] mem_state_addr;
    logic [ways_p-1:0] mem_state_wr, mem_state_valid;
    logic [state_width_lp-1:0] mem_state_n, mem_state_non_rst_n;

    logic mem_tag_state_valid, mem_tag_state_wr;
    logic [(state_width_lp*ways_p)-1:0] mem_state_wmask;
    logic [tag_state_width_lp-1:0] mem_tag_state_rdata, mem_tag_state_n, mem_tag_state_wmask;

    logic mem_data_wr_any_way;
    logic [ways_p-1:0] mem_data_wr, mem_data_valid;
    logic [wr_mask_width_lp-1:0] mem_data_wmask;
    logic [offset_width_lp+2:0] mem_wdata_shamt;
    logic [offset_width_lp-1:0] mem_data_wmask_shamt;
    logic [(dma_data_width_p*32)-1:0] mem_wdata_base;
    logic [(dma_data_width_p*32)-1:0] mem_data_n;
    logic [dma_byte_width_lp-1:0] mem_data_wmask_base;
    logic [$clog2(sets_p * dma_blk_ratio_lp)-1:0] mem_data_addr, mem_data_addr_offset;

    // Pipe stage 2
    always_ff @(posedge clk_i) begin
        way_index_r <= cc_valid_ready_r? way_index_n: way_index_r;
    end
    
    assign way_index = cc_valid_ready_r? way_index_n: way_index_r;
    assign cc_rdata_src = (cache_state_r == s_alloc_rx | cache_state_r == s_alloc_rd)? main_mem_rdata: set_data[way_index][cc_pkt_ib_bit_offset_r +: 32];
    assign cc_rdata_o   = cc_rdata_src & {32{~write_complete}};

    assign cb_pkt.we   = send_eviction;
    assign cb_pkt.addr = cb_addr_lo; // send_eviction? evict_block_address: {cc_pkt_r.addr[31:offset_width_lp], offset_width_lp'(0)};
    assign cb_valid_o  = send_eviction || cache_state_r == s_alloc_rd || (cache_state_r == s_lookup & read_write_miss);

    always_comb begin
        // Read every way of the selected set upon transition into s_lookup
        mem_ways_rd = (cache_state_n == s_lookup);

        mem_tag_n = cc_pkt_r.addr[31-:tag_width_lp];
        for (int w = 0; w < ways_p; w++) begin
            mem_tag_wr[w] = cb_valid_i & rx_start & (way_index == tag_width_lp'(w));
            mem_tag_valid[w] = mem_tag_wr[w] | mem_ways_rd;
        end

        mem_state_addr = rst_seq_done? set_index: rst_count_r;
        mem_state_non_rst_n = (cache_mem_write | cc_pkt_r.we)? block_state_t'(s_modified): block_state_t'(s_shared); // REVISIT (snooping)
        mem_state_n = rst_seq_done? mem_state_non_rst_n: block_state_t'(s_invalid); // reset all blocks to empty
        
        mem_state_wr_any_way = (cb_valid_i & rx_start) | cache_mem_write;
        for (int w = 0; w < ways_p; w++) begin
            mem_state_wr[w] = ~rst_seq_done | (mem_state_wr_any_way & (way_index == tag_width_lp'(w)));
            mem_state_valid[w] = mem_state_wr[w] | mem_ways_rd;
        end
        
        for (int w = 0; w < ways_p; w++) begin
            mem_state_wmask[state_width_lp*w +: state_width_lp] = {state_width_lp{mem_state_wr[w]}};
        end

        mem_tag_state_wmask = { mem_state_wmask, {tag_width_lp{mem_tag_wr[0]}} }; // bit mask
        mem_tag_state_n = { {ways_p{mem_state_n}}, mem_tag_n};
        mem_tag_state_valid = |{mem_state_valid, mem_tag_valid[0]};
        mem_tag_state_wr = |{mem_state_wr, mem_tag_wr[0]};

        /* mem_data */
        mem_data_wr_any_way = cb_valid_i | cache_mem_write;
        for (int w = 0; w < ways_p; w++) begin
            mem_data_wr[w] = mem_data_wr_any_way & (way_index == tag_width_lp'(w));
            mem_data_valid[w] = mem_data_wr[w] | mem_ways_rd;
        end

        mem_data_n = cb_valid_i? main_mem_wdata: (cc_pkt_r.wdata << cc_pkt_ib_bit_offset_r);
        mem_data_wmask = cb_valid_i? '1: {'0, cc_pkt_r.be} << cc_pkt_ib_byte_offset_r;
        
        if (send_eviction)
            mem_data_addr_offset = tx_count_r;
        else if (cache_state_r == s_alloc_rx || cache_state_r == s_alloc_rd)
            mem_data_addr_offset = rx_count_r;
        else if (cache_state_r == s_lookup)
            mem_data_addr_offset = cc_pkt_rx_addr_r;
        else
            mem_data_addr_offset = cc_pkt_rx_addr;

        mem_data_addr = (set_index << dma_blk_size_ratio_lp) + mem_data_addr_offset;
    end
    
    // Convert RAM0 {state, tag} structure - this exists because state only SRAM is too skinny
    // could alternatively distribute state across each way SRAM but then all require bit mask
    always_comb begin
        mem_tag_rdata[0] = mem_tag_state_rdata[tag_width_lp-1:0];
        for (int w = 0; w < ways_p; w++) begin
            mem_state_rdata[w] = mem_tag_state_rdata[tag_width_lp+(w*state_width_lp) +: state_width_lp];
        end
    end

    generate
        for (w = 0; w < ways_p; w++) begin : gen_ram

            if (w == 0) begin : gen_tag_state_ram

                bsg_mem_1rw_sync_mask_write_bit #(
                    .width_p(tag_state_width_lp),
                    .els_p(sets_p)
                ) u_mem_tag_state (
                    .clk_i,
                    .reset_i(reset),
                    .data_i(mem_tag_state_n),
                    .addr_i(mem_state_addr),
                    .v_i(mem_tag_state_valid),
                    .w_i(mem_tag_state_wr),
                    .w_mask_i(mem_tag_state_wmask),
                    .data_o(mem_tag_state_rdata)
                );

            end else begin

                bsg_mem_1rw_sync #(
                    .width_p(tag_width_lp),
                    .els_p(sets_p)
                ) u_mem_tag (
                    .clk_i,
                    .reset_i(reset),
                    .data_i(mem_tag_n),
                    .addr_i(set_index),
                    .v_i(mem_tag_valid[w]),
                    .w_i(mem_tag_wr[w]),
                    .data_o(mem_tag_rdata[w])
                );
                
            end

            // Memory is structured so that each address hold dma_data_width_p words
            // If a block is split between multiple addresses they are contiguous
            bsg_mem_1rw_sync_mask_write_byte #(
                .data_width_p(dma_data_width_p * 32),
                .els_p(sets_p * dma_blk_ratio_lp)
            ) u_mem_data (
                .clk_i,
                .reset_i(reset),
                .data_i(mem_data_n),
                .addr_i(mem_data_addr),
                .v_i(mem_data_valid[w]),
                .w_i(mem_data_wr[w]),
                .write_mask_i(mem_data_wmask),
                .data_o(mem_data_rdata[w])
            );

        end
    endgenerate

    // Embedded SVAs
    `ifndef DISABLE_TESTING
        
        // Signals for viewing Verdi (structs not supported)
        logic cc_pkt_we_i;
        logic [3:0] cc_pkt_be_i;
        logic [31:0] cc_pkt_addr_i, cc_pkt_wdata_i;

        assign cc_pkt_we_i = cc_pkt.we;
        assign cc_pkt_be_i = cc_pkt.be;
        assign cc_pkt_addr_i = cc_pkt.addr;
        assign cc_pkt_wdata_i = cc_pkt.wdata;

        logic cc_pkt_we_r;
        logic [3:0] cc_pkt_be_r;
        logic [31:0] cc_pkt_addr_r, cc_pkt_wdata_r;

        assign cc_pkt_we_r = cc_pkt_r.we;
        assign cc_pkt_be_r = cc_pkt_r.be;
        assign cc_pkt_addr_r = cc_pkt_r.addr;
        assign cc_pkt_wdata_r = cc_pkt_r.wdata;

        logic cb_pkt_we_o;
        logic [31:0] cb_pkt_addr_o;
        logic [(dma_data_width_p*32)-1:0] cb_pkt_wdata_o;

        assign cb_pkt_we_o = cb_pkt.we;
        assign cb_pkt_addr_o = cb_pkt.addr;
        assign cb_pkt_wdata_o = cb_pkt.wdata;

        // Auxilliary testing code
        logic be_non_contig, cc_valid_ready_latch, cc_valid_ready_latch_r;
        always_comb begin
            case (cc_pkt.be)
                4'b1111: be_non_contig = 1'b0;
                4'b1100: be_non_contig = 1'b0;
                4'b0110: be_non_contig = 1'b0;
                4'b0011: be_non_contig = 1'b0;
                4'b1000: be_non_contig = 1'b0;
                4'b0100: be_non_contig = 1'b0;
                4'b0010: be_non_contig = 1'b0;
                4'b0001: be_non_contig = 1'b0;
                4'b0000: be_non_contig = 1'b0;
                default: be_non_contig = 1'b1;
            endcase
        end

        always_ff @(posedge clk_i) begin
            if (~nreset_i)
                cc_valid_ready_latch_r <= ~nreset_i? 1'b0: (cc_valid_ready_latch_r | cc_valid_ready);
        end

        assign cc_valid_ready_latch = cc_valid_ready_latch_r | cc_valid_ready;

        // Properties
        property p_main_mem_rx;
            @(posedge clk_i) if (nreset_i)
                cb_valid_i |-> cache_state_r == s_alloc_rx || cache_state_r == s_alloc_rd;
        endproperty

        property p_be_contiguous;
            @(posedge clk_i) if (nreset_i)
                cc_valid_i & cc_pkt.we |-> ~be_non_contig;
        endproperty

        property p_s_lookup_self_loop;
            @(posedge clk_i) if (nreset_i)
                cache_state_r == s_lookup |=> cache_state_r != s_lookup;
        endproperty
        
        property p_s_alloc_rx;
            @(posedge clk_i) if (nreset_i)
                (cache_state_r == s_alloc_rx) & rx_done |=> cache_state_r != s_alloc_rx;
        endproperty

        property p_s_alloc_wr;
            @(posedge clk_i) if (nreset_i)
                (cache_state_r == s_alloc_wr) & tx_done |=> cache_state_r != s_alloc_wr;
        endproperty

        property p_cc_ways_index_latch;
            @(posedge clk_i) if (nreset_i & $past(nreset_i) & cc_valid_ready_latch)
                (cache_state_r != s_lookup) |-> way_index == $past(way_index);
        endproperty

        property p_set_full_latch;
            @(posedge clk_i) if (nreset_i & $past(nreset_i) & cc_valid_ready_latch)
                (cache_state_r != s_lookup) |-> set_full == $past(set_full);
        endproperty

        property p_set_index_latch;
            @(posedge clk_i) if (nreset_i & cc_valid_ready_latch)
                (cache_state_r != s_idle) |-> set_index == $past(set_index);
        endproperty

        property p_s_lookup_latch;
            @(posedge clk_i) p_set_full_latch and p_cc_ways_index_latch;
        endproperty

        // logic [sets_p-1:0] [ways_p-1:0] [tag_width_lp-1:0] cache_mem_tag_r;
        // always_comb begin
        //     for (int s = 0; s < sets_p; s++) begin
        //         for (int w = 0; w < ways_p; w++) begin
        //             cache_mem_tag_r[s][w] = cache_mem_r[s][w].tag; 
        //         end
        //     end
        // end

        // property p_block_tag_latch;
        //     @(posedge clk_i) if (nreset_i) ~rx_start |=> cache_mem_tag_r == $past(cache_mem_tag_r);
        // endproperty

        property p_block_hit_one_hot;
            @(posedge clk_i) if (nreset_i) $onehot0(block_hit);
        endproperty

        property p_set_access_one_hot;
            @(posedge clk_i) if (nreset_i) $onehot0(gen_associative.set_access);
        endproperty

        logic match_dma_block_latch, match_dma_block_latch_n;
        assign match_dma_block_latch_n = (match_dma_block_latch & (cache_state_n == s_alloc_rx || cache_state_n == s_alloc_rd)) | match_dma_block;

        always_ff @(posedge clk_i) begin
            match_dma_block_latch <= ~nreset_i? 1'b0: match_dma_block_latch_n;
        end

        // If we've already written a block we can't again in this s_alloc_rx loop
        property p_match_dma_block_force_stay;
            @(posedge clk_i) if (nreset_i) (cache_state_r == s_alloc_rx || cache_state_r == s_alloc_rd) & ~(match_dma_block_latch | match_dma_block) |=>
                (cache_state_r == s_alloc_rx || cache_state_r == s_alloc_rd);
        endproperty

        // If we haven't written yet and we're not this cycle, we have to stay in s_alloc_rx
        property p_match_dma_block_at_most_once;
            @(posedge clk_i) if (nreset_i) (cache_state_r == s_alloc_rx || cache_state_r == s_alloc_rd) & match_dma_block_latch |=> ~match_dma_block;
        endproperty

        // We must match_dma_block exactly once per s_alloc_rx loop
        property p_match_dma_block_once;
            @(posedge clk_i) p_match_dma_block_at_most_once and p_match_dma_block_force_stay;
        endproperty

        // No eviction should be sent when the set is not full
        property p_no_eviction_when_set_not_full;
            @(posedge clk_i) if (nreset_i) send_eviction |-> set_full;
        endproperty

        property p_parameters_pow2;
            @(posedge clk_i) $onehot(dma_data_width_p) and $onehot(block_width_p) and $onehot(ways_p) and $onehot(sets_p);
        endproperty

        property p_dma_data_width_max;
            @(posedge clk_i) dma_data_width_p <= block_width_p;
        endproperty


        generate
            if (block_width_p != dma_data_width_p) begin
                // Assertions for block_width_not_dma_data_width

                property p_rx_count_empty;
                    @(posedge clk_i) if (nreset_i) rx_count_r != '0 |-> cache_state_r == s_alloc_rx || cache_state_r == s_alloc_rd;
                endproperty

                property p_tx_count_empty;
                    @(posedge clk_i) if (nreset_i) tx_count_r != '0 |-> cache_state_r == s_alloc_wr || cache_state_r == s_alloc_rd;
                endproperty

                a_rx_count_empty: assert property (p_rx_count_empty)
                    else $error("Assertion failure: RX counter must be empty when not in s_alloc_rx or s_alloc_rd.");

                a_tx_count_empty: assert property (p_tx_count_empty)
                    else $error("Assertion failure: TX counter must be empty when not in s_alloc_wr or s_alloc_rd.");
            end
        endgenerate
        
        // Property assertions
        a_main_mem_rx: assert property (p_main_mem_rx)
            else $error("Assertion failure: Cannot receive memory response unless in s_alloc_rx or s_alloc_rd.");

        a_be_contiguous: assert property (p_be_contiguous)
            else $error("Assertion failure: Byte enable must be contiguous.");

        a_s_lookup_latch: assert property (p_s_lookup_latch)
            else $error("Assertion failure: Status signals must only change on transition to s_lookup.");

        a_set_index_latch: assert property (p_set_index_latch)
            else $error("Assertion failure: Set index must only change during s_idle.");

        a_s_lookup_self_loop: assert property (p_s_lookup_self_loop)
            else $error("Assertion failure: State cannot stay in s_lookup for more than a cycle.");

        a_s_alloc_rx: assert property (p_s_alloc_rx)
            else $error("Assertion failure: State cannot stay in s_alloc_rx after tx_done.");

        a_s_alloc_wr: assert property (p_s_alloc_wr)
            else $error("Assertion failure: State cannot stay in s_alloc_wr after tx_done.");

        // a_tag_latch: assert property (p_block_tag_latch)
        //     else $error("Assertion failure: Block tag can only change on miss completion.");

        a_block_hit_one_hot: assert property (p_block_hit_one_hot)
            else $error("Assertion failure: Only one block can be triggered hit at once.");

        a_set_access_one_hot: assert property (p_set_access_one_hot)
            else $error("Assertion failure: Only one set can be triggered hit at once.");

        a_match_dma_block_once: assert property (p_match_dma_block_once)
            else $error("Assertion failure: Must match_dma_block exactly once per s_alloc_rx loop.");

        a_no_eviction_when_set_not_full: assert property (p_no_eviction_when_set_not_full)
            else $error("Assertion failure: No eviction should be sent when the set isn't full.");

        a_parameters_pow2: assert property (p_parameters_pow2)
            else $error("Assertion failure: Given parameters must be a power of 2.");

        a_dma_data_width_max: assert property (p_dma_data_width_max)
            else $error("Assertion failure: dma_data_width_p cannot be larger than block_width_p.");

        // REVISIT (11/6, COV) -- how to view results without URG?
        covergroup cg_cache_state @(posedge clk_i);
            coverpoint cache_state_r {
                bins state_coverage[] = { s_idle, s_lookup, s_alloc_rd, s_alloc_rx, s_alloc_wr };
                bins valid_transitions = 
                                      (s_lookup, s_alloc_rd, s_alloc_rx, s_alloc_wr => s_idle),
                                      (s_idle => s_lookup), 
                                      (s_lookup => s_alloc_rd),
                                      (s_lookup => s_alloc_rx),
                                      (s_lookup => s_alloc_wr),
                                      (s_alloc_wr => s_alloc_rd),
                                      (s_alloc_wr => s_alloc_wr),
                                      (s_alloc_rd => s_alloc_rx),
                                      (s_alloc_rx => s_idle);
            }
        endgroup

        cg_cache_state cgi_cache_state = new;
    `endif
    
endmodule
