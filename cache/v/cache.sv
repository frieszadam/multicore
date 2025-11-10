`include "v/cache.svh"

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

    // For indexing
    localparam offset_width_lp   = $clog2(block_width_p) + 2; // offset within block, add 2 because block size in words
    localparam index_width_lp    = $clog2(sets_p);
    localparam tag_width_lp      = 32 - offset_width_lp - index_width_lp;

    // Data transfer ratio
    localparam dma_blk_ratio_lp   = $clog2(block_width_p/dma_data_width_p);
    localparam dma_data_size_lp   = $clog2(dma_data_width_p);
    localparam dma_offset_incr_lp = dma_data_size_lp + 5;

    `declare_cache_bus_pkt_t(dma_data_width_p)
    `declare_cache_block_t(tag_width_lp, block_width_p)

    core_cache_pkt_t cc_pkt, cc_pkt_r;
    assign cc_pkt = cc_pkt_i;

    cache_bus_pkt_t cb_pkt;
    assign cb_pkt_o = cb_pkt;

    // lru, block_state, tag, data 
    cache_block_t [sets_p-1:0] [ways_p-1:0] cache_mem_r, cache_mem_n;
    logic [ways_p-1:0] [tag_width_lp-1:0] block_tag_r, block_tag_n;
    block_state_t [ways_p-1:0] block_state_r, block_state_n;
    // REVISIT (11/4, we load entire block as we may read or evict and these could be from different addresses) 
    logic [ways_p-1:0] [(block_width_p*32)-1:0] block_data_r, block_data_n;

    logic [tag_width_lp-1:0] cc_pkt_addr_dly1;
    logic [index_width_lp-1:0] set_index;
    logic write_complete, read_complete, cc_valid_ready, cc_valid_ready_r;

    logic [31:0] cc_rdata_src;
    logic [31:0] main_mem_rdata;

    typedef enum logic [2:0] {s_idle, s_lookup, s_alloc_tx, s_alloc_req, s_alloc_rx} cache_control_t;
    cache_control_t cache_state_r, cache_state_n;

    assign cc_valid_ready = cc_valid_i & cc_ready_o;
    assign set_index = cc_valid_ready? cc_pkt.addr[offset_width_lp+:index_width_lp]: cc_pkt_r.addr[offset_width_lp+:index_width_lp];

    // Load block tag, state, data, and lru for all blocks in set upon receiving request
    always_comb begin
        for (int i = 0; i < ways_p; i++) begin
            block_tag_n[i] = cc_valid_ready? cache_mem_r[set_index][i].tag: block_tag_r[i];
            block_state_n[i] = cc_valid_ready? cache_mem_r[set_index][i].block_state: block_state_r[i];
            block_data_n[i] = cc_valid_ready? cache_mem_r[set_index][i].data: block_data_r[i];
        end
    end

    // Pipe stage 1
    always_ff @(posedge clk_i) begin
        if (~nreset_i)
            cc_valid_ready_r <= 1'b0;
        else 
            cc_valid_ready_r <= cc_valid_ready;

        cc_pkt_r      <= cc_valid_ready? cc_pkt: cc_pkt_r;
        block_tag_r   <= block_tag_n;
        block_state_r <= block_state_n;
        block_data_r  <= block_data_n;
    end

    logic tx_done, rx_done, rx_start;
    logic read_write_miss, set_full, send_eviction;
    logic [offset_width_lp+2:0] cc_pkt_r_offset; // because we left shift by three to convert byte to bit 
    logic [ways_size_lp-1:0] way_index, way_index_n, way_index_r, block_hit_index;
    logic [ways_p-1:0] block_state_invalid, block_hit;
    logic [31:0] evict_block_address;

    assign cc_pkt_r_offset = cc_pkt_r.addr[offset_width_lp-1:0] <<< 3;

    always_comb begin
        read_write_miss = cc_valid_ready_r;
        set_full = 1'b1;

        for (int w = 0; w < ways_p; w++) begin
            block_state_invalid[w] = block_state_r[w] == s_invalid;
            block_hit[w] = ~block_state_invalid[w] & block_tag_r[w] == cc_pkt_r.addr[31-:tag_width_lp];

            // not a miss if any valid way holds a matching tag
            read_write_miss = read_write_miss & ~block_hit[w];
            set_full = set_full & ~block_state_invalid[w];
        end
    end
    

    // pseudo LRU tree
    logic [ways_size_lp-1:0] lru_way_index, open_way_index;
    genvar s;

    generate
        if (ways_p == 1) begin : gen_direct_mapped
            assign lru_way_index = 1'b0;
            assign open_way_index = 1'b0;
        end else begin : gen_associative
            logic cache_access;
            logic [sets_p-1:0] set_access;
            logic [ways_p-1:0] way_access;

            assign cache_access = rx_start | (cache_state_r == s_lookup & ~read_write_miss);
            
            logic [sets_p-1:0] [ways_p-2:0] lru_flag_r, lru_flag_n;
            logic [sets_p-1:0] [ways_size_lp-1:0] lru_set_way_index;

            always_comb begin                
                for (int s = 0; s < sets_p; s++) begin
                    set_access[s] = cache_access & set_index == index_width_lp'(s);
                end
                for (int w = 0; w < ways_p; w++) begin
                    way_access[w] = way_index == ways_size_lp'(w);
                end
                
                lru_way_index = lru_set_way_index[set_index]; 
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
                    for (int w = 0; w < ways_p; w++) begin
                        open_way_index = block_state_invalid[w]? ways_size_lp'(w): open_way_index;
                    end
                end
            end

            always_ff @(posedge clk_i) begin
                if (~nreset_i) begin
                    for (int s = 0; s < sets_p; s++) begin
                        lru_flag_r[s] <= '0;
                    end
                end else
                    lru_flag_r <= lru_flag_n;
            end
        end
    endgenerate

    // if an open way exists, it will be at way_index so if way_index is modified then the set is full and we must evict 
    assign send_eviction = (cache_state_r == s_lookup & read_write_miss & block_state_r[way_index] == s_modified) || (cache_state_r == s_alloc_tx);

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
                    if (block_state_r[way_index] == s_modified)
                        cache_state_n = tx_done? s_alloc_req: s_alloc_tx;
                    else
                        cache_state_n = cb_yumi_i? s_alloc_rx: s_alloc_req;
                end else begin
                    cache_state_n = s_idle;
                end
            end
            s_alloc_tx:  cache_state_n = tx_done? s_alloc_req: s_alloc_tx;
            s_alloc_req: cache_state_n = cb_yumi_i? s_alloc_rx: s_alloc_req;
            s_alloc_rx:  cache_state_n = rx_done? s_idle: s_alloc_rx;
            default:     cache_state_n = s_idle;
        endcase
    end

    always_ff @(posedge clk_i) begin
        if (~nreset_i)
            cache_state_r <= s_idle;
        else
            cache_state_r <= cache_state_n;
    end

    logic cache_mem_write, write_dma_block, match_dma_block;
    logic [offset_width_lp+2:0] rx_offset_r, wdata_offset;

    assign cache_mem_write = cache_state_r == s_lookup & ~read_write_miss & cc_pkt_r.we;

    assign write_complete = cc_valid_o & cc_pkt_r.we;
    assign read_complete  = cc_valid_o & ~cc_pkt_r.we;

    assign cc_ready_o = cache_state_r == s_idle;
    assign cc_valid_o = cache_state_r != s_idle & cache_state_n == s_idle;


    generate
        if (block_width_p != dma_data_width_p) begin : block_width_not_dma_data_width
            logic tx_count_incr;
            logic [dma_blk_ratio_lp-1:0] rx_count_r, rx_count_n, tx_count_r, tx_count_n;
            logic [offset_width_lp+2:0] tx_offset_r, rx_offset_n;
            logic [offset_width_lp-1:0] tx_addr_offset;
            logic [31:0] main_mem_rdata_r; // REVISIT (PPA, could condense to 32 bits)
            logic [offset_width_lp-(dma_data_size_lp+2)-1:0] cc_pkt_rx_addr;

            assign rx_done  = rx_count_r == '1 & cb_valid_i;
            assign rx_start = rx_count_r == '0 & cb_valid_i;
            assign tx_done  = (cb_valid_o & cb_yumi_i) & (~cb_pkt.we | (tx_count_r == '1));
            assign tx_count_incr = cb_valid_o & cb_yumi_i & cb_pkt.we;

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
            
            assign rx_offset_r = rx_count_r << dma_offset_incr_lp;
            assign rx_offset_n = ((rx_count_r + dma_blk_ratio_lp'(1)) << dma_offset_incr_lp) - offset_width_lp+3'(1);
            assign tx_offset_r = tx_count_r << dma_offset_incr_lp;
            assign tx_addr_offset = tx_count_r << (dma_data_size_lp + 2);

            // compare upper bits of offset region, valid as dma_data_width_p must be a power of 2
            assign cc_pkt_rx_addr = cc_pkt_r.addr[offset_width_lp-1:dma_data_size_lp+2];
            assign match_dma_block = (rx_count_r == cc_pkt_rx_addr) & cb_valid_i;
            assign write_dma_block = cc_pkt_r.we & match_dma_block;
            
            assign cb_pkt.wdata = block_data_r[way_index][tx_offset_r +: (1 << dma_offset_incr_lp)];
            assign evict_block_address = {block_tag_r[way_index], cc_pkt_r.addr[offset_width_lp+:index_width_lp], tx_addr_offset}; 
            
            // rdata is the loaded block that matches, either from this cycle or previously
            assign main_mem_rdata = match_dma_block? cb_data_i[wdata_offset +: 32]: main_mem_rdata_r;
            always_ff @(posedge clk_i) begin
                main_mem_rdata_r <= main_mem_rdata;
            end

        end else begin : block_size_eq_dma_data_width
            assign tx_done  = cb_yumi_i;
            assign rx_done  = cb_valid_i;
            assign rx_start = cb_valid_i; 
            assign rx_offset_r = '0;

            assign match_dma_block = cb_valid_i;
            assign write_dma_block = match_dma_block & cc_pkt_r.we;
            
            assign cb_pkt.wdata = block_data_r[way_index]; // eviction index stored in way_index
            assign main_mem_rdata = cb_data_i[cc_pkt_r_offset +: 32];
            assign evict_block_address = {block_tag_r[way_index], cc_pkt_r.addr[offset_width_lp+:index_width_lp], offset_width_lp'(0)};
        end
    endgenerate    

    logic [(dma_data_width_p*32)-1:0] main_mem_wdata;

    always_comb begin
        main_mem_wdata = cb_data_i;
        wdata_offset = cc_pkt_r_offset - rx_offset_r;

        if (cc_pkt_r.be[0] & write_dma_block)
            main_mem_wdata[wdata_offset +:8] = cc_pkt_r.wdata[7:0];
        if (cc_pkt_r.be[1] & write_dma_block)
            main_mem_wdata[wdata_offset+8 +:8] = cc_pkt_r.wdata[15:8];
        if (cc_pkt_r.be[2] & write_dma_block)
            main_mem_wdata[wdata_offset+16 +:8] = cc_pkt_r.wdata[23:16];
        if (cc_pkt_r.be[3] & write_dma_block)
            main_mem_wdata[wdata_offset+24 +:8] = cc_pkt_r.wdata[31:24];
    end

    always_comb begin
        cache_mem_n = cache_mem_r;
        
        // REVISIT PPA
        if (~nreset_i) begin
            for (int set_idx = 0; set_idx < sets_p; set_idx++) begin
                // Iterate over all ways (columns)
                for (int way_idx = 0; way_idx < ways_p; way_idx++) begin
                    // Conditionally set the block_state field of every cache line to s_invalid
                    cache_mem_n[set_idx][way_idx].block_state = s_invalid;
                    `ifndef DISABLE_TESTING
                    // reset to enable tag equivalence checking (not required for operation)
                    cache_mem_n[set_idx][way_idx].tag = '0;
                    `endif
                end
            end
        end

        // Update block state, data, tag, and LRU on allocation
        else if (cb_valid_i) begin
            cache_mem_n[set_index][way_index].data[rx_offset_r +: (1 << dma_offset_incr_lp)] = main_mem_wdata;

            if (rx_start) begin
                cache_mem_n[set_index][way_index].block_state = cc_pkt_r.we? s_modified: s_shared; // REVISIT SNOOP (s_exclusive)
                cache_mem_n[set_index][way_index].tag = cc_pkt_r.addr[31-:tag_width_lp]; // REVISIT PIPE
            end
        end

        // Upon a non-miss write, update the data and LRU fields
        else if (cache_mem_write) begin
            cache_mem_n[set_index][way_index].block_state = s_modified;

            if (cc_pkt_r.be[0])
                cache_mem_n[set_index][way_index].data[cc_pkt_r_offset +:8] = cc_pkt_r.wdata[7:0];
            if (cc_pkt_r.be[1])
                cache_mem_n[set_index][way_index].data[cc_pkt_r_offset+8 +:8] = cc_pkt_r.wdata[15:8];
            if (cc_pkt_r.be[2])
                cache_mem_n[set_index][way_index].data[cc_pkt_r_offset+16 +:8] = cc_pkt_r.wdata[23:16];
            if (cc_pkt_r.be[3])
                cache_mem_n[set_index][way_index].data[cc_pkt_r_offset+24 +:8] = cc_pkt_r.wdata[31:24];

        end
    end

    // Pipe stage 2
    always_ff @(posedge clk_i) begin
        cache_mem_r <= cache_mem_n;
        way_index_r <= cc_valid_ready_r? way_index_n: way_index_r;
    end
    
    assign way_index = cc_valid_ready_r? way_index_n: way_index_r;

    assign cc_rdata_src = (cache_state_r == s_alloc_rx)? main_mem_rdata: block_data_r[way_index][cc_pkt_r_offset +: 32];
    assign cc_rdata_o = cc_rdata_src & {32{~write_complete}};

    assign cb_pkt.we = send_eviction;
    assign cb_pkt.addr = send_eviction? evict_block_address: {cc_pkt_r.addr[31:offset_width_lp], offset_width_lp'(0)};
    assign cb_valid_o = send_eviction || cache_state_r == s_alloc_req || (cache_state_r == s_lookup & read_write_miss);

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

        logic [(block_width_p*32)-1:0] cache_mem_data_n, cache_mem_data_r;
        assign cache_mem_data_n = cache_mem_n[set_index][way_index].data;
        assign cache_mem_data_r = cache_mem_r[set_index][way_index].data;

        logic [tag_width_lp-1:0] cc_ways_cache_mem_tag_n, cc_ways_cache_mem_tag_r;
        assign cc_ways_cache_mem_tag_n = cache_mem_n[set_index][way_index].tag;
        assign cc_ways_cache_mem_tag_r = cache_mem_r[set_index][way_index].tag;

        logic [(block_width_p*32)-1:0] cache_mem_data_20_r, cache_mem_data_20_n;
        assign cache_mem_data_20_r = cache_mem_r[2][0].data;
        assign cache_mem_data_20_n = cache_mem_n[2][0].data;

        block_state_t cache_mem_state_20_r, cache_mem_state_20_n;
        assign cache_mem_state_20_r = cache_mem_r[2][0].block_state;
        assign cache_mem_state_20_n = cache_mem_n[2][0].block_state;

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
                cb_valid_i |-> cache_state_r == s_alloc_rx;
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

        property p_s_alloc_tx;
            @(posedge clk_i) if (nreset_i)
                (cache_state_r == s_alloc_tx) & tx_done |=> cache_state_r != s_alloc_tx;
        endproperty

        property p_cc_ways_index_latch;
            @(posedge clk_i) if (nreset_i & $past(nreset_i) & cc_valid_ready_latch)
                (cache_state_r != s_lookup) |-> way_index == $past(way_index);
        endproperty

        property p_set_full_latch;
            @(posedge clk_i) if (nreset_i & $past(nreset_i))
                (cache_state_r != s_lookup) |-> set_full == $past(set_full);
        endproperty

        property p_set_index_latch;
            @(posedge clk_i) if (nreset_i & cc_valid_ready_latch)
                (cache_state_r != s_idle) |-> set_index == $past(set_index);
        endproperty

        property p_s_lookup_latch;
            @(posedge clk_i) p_set_full_latch and p_cc_ways_index_latch;
        endproperty

        logic [sets_p-1:0] [ways_p-1:0] [tag_width_lp-1:0] cache_mem_tag_r;
        always_comb begin
            for (int s = 0; s < sets_p; s++) begin
                for (int w = 0; w < ways_p; w++) begin
                    cache_mem_tag_r[s][w] = cache_mem_r[s][w].tag; 
                end
            end
        end

        property p_block_tag_latch;
            @(posedge clk_i) if (nreset_i) ~rx_start |=> cache_mem_tag_r == $past(cache_mem_tag_r);
        endproperty

        property p_block_hit_one_hot;
            @(posedge clk_i) if (nreset_i) $onehot0(block_hit);
        endproperty

        property p_set_way_access_one_hot;
            @(posedge clk_i) if (nreset_i) $onehot0(gen_associative.set_access) & $onehot0(gen_associative.way_access);
        endproperty

        logic match_dma_block_latch, match_dma_block_latch_n;
        assign match_dma_block_latch_n = (match_dma_block_latch & cache_state_n == s_alloc_rx) | match_dma_block;

        always_ff @(posedge clk_i) begin
            match_dma_block_latch <= ~nreset_i? 1'b0: match_dma_block_latch_n;
        end

        // If we've already written a block we can't again in this s_alloc_rx loop
        property p_match_dma_block_force_stay;
            @(posedge clk_i) if (nreset_i) (cache_state_r == s_alloc_rx) & ~(match_dma_block_latch | match_dma_block) |=>
                cache_state_r == s_alloc_rx;
        endproperty

        // If we haven't written yet and we're not this cycle, we have to stay in s_alloc_rx
        property p_match_dma_block_at_most_once;
            @(posedge clk_i) if (nreset_i) (cache_state_r == s_alloc_rx) & match_dma_block_latch |=> ~match_dma_block;
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
                    @(posedge clk_i) if (nreset_i) block_width_not_dma_data_width.rx_count_r != '0 |-> cache_state_r == s_alloc_rx;
                endproperty

                property p_tx_count_empty;
                    @(posedge clk_i) if (nreset_i) block_width_not_dma_data_width.tx_count_r != '0 |-> cache_state_r == s_alloc_tx;
                endproperty

                a_rx_count_empty: assert property (p_rx_count_empty)
                    else $error("Assertion failure: RX counter must be empty when not in s_alloc_rx.");

                a_tx_count_empty: assert property (p_tx_count_empty)
                    else $error("Assertion failure: TX counter must be empty when not in s_alloc_tx.");
            end
        endgenerate
        
        // Property assertions
        a_main_mem_rx: assert property (p_main_mem_rx)
            else $error("Assertion failure: Cannot receive memory response unless in s_alloc_rx.");

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

        a_s_alloc_tx: assert property (p_s_alloc_tx)
            else $error("Assertion failure: State cannot stay in s_alloc_tx after tx_done.");

        a_tag_latch: assert property (p_block_tag_latch)
            else $error("Assertion failure: Block tag can only change on miss completion.");

        a_block_hit_one_hot: assert property (p_block_hit_one_hot)
            else $error("Assertion failure: Only one block can be triggered hit at once.");

        a_set_way_access_one_hot: assert property (p_set_way_access_one_hot)
            else $error("Assertion failure: Only one set/way can be triggered hit at once.");

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
                bins state_coverage[] = { s_idle, s_lookup, s_alloc_req, s_alloc_rx, s_alloc_tx };
                bins valid_transitions = 
                                      (s_lookup, s_alloc_req, s_alloc_rx, s_alloc_tx => s_idle),
                                      (s_idle => s_lookup), 
                                      (s_lookup => s_alloc_req),
                                      (s_lookup => s_alloc_rx),
                                      (s_lookup => s_alloc_tx),
                                      (s_alloc_tx => s_alloc_req),
                                      (s_alloc_tx => s_alloc_tx),
                                      (s_alloc_req => s_alloc_rx),
                                      (s_alloc_rx => s_idle);
            }
        endgroup

        cg_cache_state cgi_cache_state = new;
    `endif
    
endmodule
