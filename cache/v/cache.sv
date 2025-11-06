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
    localparam dma_offset_incr_lp = $clog2(dma_data_width_p) + 5;

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

    logic [(block_width_p*32)-1:0] cc_rdata_src;
    logic [(dma_data_width_p*32)-1:0] main_mem_rdata;

    typedef enum logic [2:0] {s_idle, s_lookup, s_tx_evict, s_allocate_req, s_allocate_rx} cache_control_t;
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
    logic [ways_size_lp-1:0] cc_ways_index, cc_ways_index_n, cc_ways_index_r, block_hit_index;
    logic [ways_p-1:0] block_state_invalid, block_hit;
    logic [31:0] evict_block_address;

    assign cc_pkt_r_offset = cc_pkt_r.addr[offset_width_lp-1:0] <<< 3;

    always_comb begin
        read_write_miss = cc_valid_ready_r;
        set_full = 1'b1;

        for (int i = 0; i < ways_p; i++) begin
            block_state_invalid[i] = block_state_r[i] == s_invalid;
            block_hit[i] = ~block_state_invalid[i] & block_tag_r[i] == cc_pkt_r.addr[31-:tag_width_lp];

            // not a miss if any valid way holds a matching tag
            read_write_miss = read_write_miss & ~block_hit[i];
            set_full = set_full & ~block_state_invalid[i];
        end
    end
    

    // pseudo LRU tree
    logic [ways_size_lp-1:0] lru_way_index;

    generate
        if (ways_p == 1) begin : gen_direct_mapped
            assign lru_way_index = 1'b0;
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
                    way_access[w] = cc_ways_index == ways_size_lp'(w);
                end
                
                lru_way_index = lru_set_way_index[set_index]; 
            end

            // REVISIT (11/3, parameterize LRU for all valid ways_p)
            if (ways_p == 4) begin
                always_comb begin
                    for (int s = 0; s < sets_p; s++) begin
                        lru_set_way_index[s] = (lru_flag_r[s][0] << 1) | (lru_flag_r[s][0]? lru_flag_r[s][2]: lru_flag_r[s][1]);
                        
                        lru_flag_n[s][0] =  (set_access[s])?                     ~cc_ways_index[1]: lru_flag_r[s][0];
                        lru_flag_n[s][1] =  (set_access[s] & ~cc_ways_index[1])? ~cc_ways_index[0]: lru_flag_r[s][1];
                        lru_flag_n[s][2] =  (set_access[s] &  cc_ways_index[1])? ~cc_ways_index[0]: lru_flag_r[s][2];
                    end
                end
            end

            else if (ways_p == 8) begin
                always_comb begin
                    for (int s = 0; s < sets_p; s++) begin
                        // lru_set_way_index[s] = lru_flag_r[s][0] << (ways_size_lp-1);
                        // for (int l = 0; ; < ways_size_lp; l++) begin
                        //     layer_index[s][l] = {'0, lru_set_way_index[s][ways_size_lp-1 -: l] << l};
                        //     lru_set_way_index[s] = lru_set_way_index[s] | (lru_flag_r[s][lru_set_way_index[ways_size_lp-1]] << (ways_size_lp-2))
                        // end
                        
                        // Decoding of lru flags into index of LRU way in each set
                        lru_set_way_index[s] = ways_size_lp'(lru_flag_r[s][0] << (ways_size_lp-1));
                        if (lru_flag_r[s][0]) begin
                            lru_set_way_index[s] = lru_set_way_index[s] | (lru_flag_r[s][2] << (ways_size_lp-2));
                            if (lru_flag_r[s][2])
                                lru_set_way_index[s] = lru_set_way_index[s] | (lru_flag_r[s][6] << (ways_size_lp-3));
                            else
                                lru_set_way_index[s] = lru_set_way_index[s] | (lru_flag_r[s][5] << (ways_size_lp-3));
                        end else begin
                            lru_set_way_index[s] = lru_set_way_index[s] | (lru_flag_r[s][1] << (ways_size_lp-2));
                            if (lru_flag_r[s][1])
                                lru_set_way_index[s] = lru_set_way_index[s] | (lru_flag_r[s][4] << (ways_size_lp-3));
                            else
                                lru_set_way_index[s] = lru_set_way_index[s] | (lru_flag_r[s][3] << (ways_size_lp-3));
                        end

                        // Update of each lru flag bit in the accessed set
                        lru_flag_n[s][0] =  (set_access[s])? ~cc_ways_index[ways_size_lp-1]: lru_flag_r[s][0];

                        lru_flag_n[s][1] =  (set_access[s] & ~cc_ways_index[ways_size_lp-1])? ~cc_ways_index[ways_size_lp-2]: lru_flag_r[s][1];
                        lru_flag_n[s][2] =  (set_access[s] &  cc_ways_index[ways_size_lp-1])? ~cc_ways_index[ways_size_lp-2]: lru_flag_r[s][2];

                        lru_flag_n[s][3] =  (set_access[s] & ~cc_ways_index[ways_size_lp-1] & ~cc_ways_index[ways_size_lp-2])? ~cc_ways_index[ways_size_lp-3]: lru_flag_r[s][3];
                        lru_flag_n[s][4] =  (set_access[s] & ~cc_ways_index[ways_size_lp-1] &  cc_ways_index[ways_size_lp-2])? ~cc_ways_index[ways_size_lp-3]: lru_flag_r[s][4];
                        lru_flag_n[s][5] =  (set_access[s] &  cc_ways_index[ways_size_lp-1] & ~cc_ways_index[ways_size_lp-2])? ~cc_ways_index[ways_size_lp-3]: lru_flag_r[s][5];
                        lru_flag_n[s][6] =  (set_access[s] &  cc_ways_index[ways_size_lp-1] &  cc_ways_index[ways_size_lp-2])? ~cc_ways_index[ways_size_lp-3]: lru_flag_r[s][6];
                    end
                end
            end

            always_ff @(posedge clk_i) begin
                if (~nreset_i)
                    lru_flag_r <= '0;
                else
                    lru_flag_r <= lru_flag_n;
            end
        end
    endgenerate

    // cc_ways_index is used since it is registered, saved beyond s_lookup
    assign evict_block_address = {block_tag_r[cc_ways_index], cc_pkt_r.addr[offset_width_lp+:index_width_lp], offset_width_lp'(0)};
    assign send_eviction = (cache_state_r == s_lookup & read_write_miss & set_full & block_state_r[cc_ways_index] == s_modified) || (cache_state_r == s_tx_evict);

    // if not miss then matching index, else if miss but not full open index, else eviction index
    always_comb begin
        if (read_write_miss) begin
            cc_ways_index_n = lru_way_index;
        end else begin
            cc_ways_index_n = '0;
            for (int i = 0; i < ways_p; i++) begin
                cc_ways_index_n = cc_ways_index_n | ({ways_size_lp{block_hit[i]}} & ways_size_lp'(i));
            end
        end
    end


    // Cache State Logic
    always_comb begin
        case (cache_state_r)
            s_idle:     cache_state_n = cc_valid_ready? s_lookup: s_idle;

            s_lookup: begin
                if (read_write_miss) begin
                    if (set_full & block_state_r[lru_way_index] == s_modified)
                        cache_state_n = tx_done? s_allocate_req: s_tx_evict;
                    else
                        cache_state_n = cb_yumi_i? s_allocate_rx: s_allocate_req;
                end else begin
                    cache_state_n = s_idle;
                end
            end
            s_tx_evict: cache_state_n = tx_done? s_allocate_req: s_tx_evict;
            s_allocate_req: cache_state_n = cb_yumi_i? s_allocate_rx: s_allocate_req;
            s_allocate_rx:  cache_state_n = rx_done? s_idle: s_allocate_rx; // in case of mm load then write, we do 1 write of combined value and we directly forward read data to output and assert valid
        endcase
    end

    always_ff @(posedge clk_i) begin
        if (~nreset_i)
            cache_state_r <= s_idle;
        else
            cache_state_r <= cache_state_n;
    end

    logic cache_mem_write, write_dma_block;
    logic [offset_width_lp+2:0] rx_offset_r;

    assign cache_mem_write = cache_state_r == s_lookup & ~read_write_miss & cc_pkt_r.we;

    assign write_complete = cc_valid_o & cc_pkt_r.we;
    assign read_complete  = cc_valid_o & ~cc_pkt_r.we;

    assign cc_ready_o = cache_state_r == s_idle;
    assign cc_valid_o = cache_state_r != s_idle & cache_state_n == s_idle;


    generate
        if (block_width_p != dma_data_width_p) begin : block_size_not_dma_data_width
            logic tx_count_incr;
            logic [dma_blk_ratio_lp-1:0] rx_count_r, rx_count_n, tx_count_r, tx_count_n;
            logic [offset_width_lp+2:0] tx_offset_r, rx_offset_n;

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
            
            assign rx_offset_r = rx_count_r << (dma_offset_incr_lp);
            assign rx_offset_n = ((rx_count_r + dma_blk_ratio_lp'(1)) << (dma_offset_incr_lp)) - 1;
            assign tx_offset_r = tx_count_r << (dma_offset_incr_lp);
            
            // REVISIT (11/5, simplify and structuralize)
            assign write_dma_block = (cc_pkt_r_offset >= rx_offset_r) & (cc_pkt_r_offset <= rx_offset_n);
            
            assign cb_pkt.wdata = block_data_r[cc_ways_index][tx_offset_r +: (1 << dma_offset_incr_lp)];
            assign main_mem_rdata = cb_data_i;
        end else begin : block_size_eq_dma_data_width
            assign tx_done  = cb_yumi_i;
            assign rx_done  = cb_valid_i;
            assign rx_start = cb_valid_i; 
            assign write_dma_block = 1'b1;

            assign cb_pkt.wdata = block_data_r[cc_ways_index]; // eviction index stored in cc_ways_index
            assign main_mem_rdata = cb_data_i;
            assign rx_offset_r = '0;
        end
    endgenerate    

    logic [(dma_data_width_p*32)-1:0] main_mem_wdata;
    logic [offset_width_lp+2:0] wdata_offset;

    always_comb begin
        main_mem_wdata = main_mem_rdata;
        wdata_offset = cc_pkt_r_offset - rx_offset_r;

        if (cc_pkt_r.be[0] & cc_pkt_r.we & write_dma_block)
            main_mem_wdata[wdata_offset +:8] = cc_pkt_r.wdata[7:0];
        if (cc_pkt_r.be[1] & cc_pkt_r.we & write_dma_block)
            main_mem_wdata[wdata_offset+8 +:8] = cc_pkt_r.wdata[15:8];
        if (cc_pkt_r.be[2] & cc_pkt_r.we & write_dma_block)
            main_mem_wdata[wdata_offset+16 +:8] = cc_pkt_r.wdata[23:16];
        if (cc_pkt_r.be[3] & cc_pkt_r.we & write_dma_block)
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
            cache_mem_n[set_index][cc_ways_index].data[rx_offset_r +: (1 << dma_offset_incr_lp)] = main_mem_wdata;

            if (rx_start) begin
                cache_mem_n[set_index][cc_ways_index].block_state = cc_pkt_r.we? s_modified: s_shared; // REVISIT SNOOP (s_exclusive)
                cache_mem_n[set_index][cc_ways_index].tag = cc_pkt_r.addr[31-:tag_width_lp]; // REVISIT PIPE
            end
        end

        // Upon a non-miss write, update the data and LRU fields
        else if (cache_mem_write) begin
            cache_mem_n[set_index][cc_ways_index].block_state = s_modified;

            if (cc_pkt_r.be[0])
                cache_mem_n[set_index][cc_ways_index].data[cc_pkt_r_offset +:8] = cc_pkt_r.wdata[7:0];
            if (cc_pkt_r.be[1])
                cache_mem_n[set_index][cc_ways_index].data[cc_pkt_r_offset+8 +:8] = cc_pkt_r.wdata[15:8];
            if (cc_pkt_r.be[2])
                cache_mem_n[set_index][cc_ways_index].data[cc_pkt_r_offset+16 +:8] = cc_pkt_r.wdata[23:16];
            if (cc_pkt_r.be[3])
                cache_mem_n[set_index][cc_ways_index].data[cc_pkt_r_offset+24 +:8] = cc_pkt_r.wdata[31:24];

        end
    end

    // Pipe stage 2
    always_ff @(posedge clk_i) begin
        cache_mem_r <= cache_mem_n;
        cc_ways_index_r <= cc_valid_ready_r? cc_ways_index_n: cc_ways_index_r;
    end
    
    assign cc_ways_index = cc_valid_ready_r? cc_ways_index_n: cc_ways_index_r;

    assign cc_rdata_src = (cache_state_r == s_allocate_rx)? main_mem_rdata: block_data_r[cc_ways_index];
    assign cc_rdata_o = cc_rdata_src[cc_pkt_r_offset +: 32] & {32{~write_complete}};

    assign cb_pkt.we = send_eviction;
    assign cb_pkt.addr = send_eviction? evict_block_address: {cc_pkt_r.addr[31:offset_width_lp], offset_width_lp'(0)};
    assign cb_valid_o = send_eviction || cache_state_r == s_allocate_req || (cache_state_r == s_lookup & read_write_miss);

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
        assign cache_mem_data_n = cache_mem_n[set_index][cc_ways_index].data;
        assign cache_mem_data_r = cache_mem_r[set_index][cc_ways_index].data;

        logic [tag_width_lp-1:0] cc_ways_cache_mem_tag_n, cc_ways_cache_mem_tag_r;
        assign cc_ways_cache_mem_tag_n = cache_mem_n[set_index][cc_ways_index].tag;
        assign cc_ways_cache_mem_tag_r = cache_mem_r[set_index][cc_ways_index].tag;

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
                cb_valid_i |-> cache_state_r == s_allocate_rx;
        endproperty

        property p_be_contiguous;
            @(posedge clk_i) if (nreset_i)
                cc_valid_i & cc_pkt.we |-> ~be_non_contig;
        endproperty

        // REVISIT (11/5, bolster state transition assertions)
        property p_s_lookup_self_loop;
            @(posedge clk_i) if (nreset_i)
                cache_state_r == s_lookup |=> cache_state_r != s_lookup;
        endproperty
        
        property p_cc_ways_index_latch;
            @(posedge clk_i) if (nreset_i & $past(nreset_i) & cc_valid_ready_latch)
                (cache_state_r != s_lookup) |-> cc_ways_index == $past(cc_ways_index);
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

        property p_set_not_full_lru_index_empty;
            @(posedge clk_i) if (nreset_i) ~set_full |-> cache_mem_r[set_index][lru_way_index].block_state == s_invalid;
        endproperty

        generate
            if (block_width_p != dma_data_width_p) begin
                // Assertions for block_size_not_dma_data_width

                property p_rx_count_empty;
                    @(posedge clk_i) if (nreset_i) block_size_not_dma_data_width.rx_count_r != '0 |-> cache_state_r == s_allocate_rx;
                endproperty

                property p_tx_count_empty;
                    @(posedge clk_i) if (nreset_i) block_size_not_dma_data_width.tx_count_r != '0 |-> cache_state_r == s_tx_evict;
                endproperty

                a_rx_count_empty: assert property (p_rx_count_empty)
                    else $error("Assertion failure: RX counter must be empty when not in s_allocate_rx.");

                a_tx_count_empty: assert property (p_tx_count_empty)
                    else $error("Assertion failure: TX counter must be empty when not in s_tx_evict.");
            end
        endgenerate
        
        // Property assertions
        a_main_mem_rx: assert property (p_main_mem_rx)
            else $error("Assertion failure: Cannot receive memory response unless in s_allocate_rx.");

        a_be_contiguous: assert property (p_be_contiguous)
            else $error("Assertion failure: Byte enable must be contiguous.");

        a_s_lookup_latch: assert property (p_s_lookup_latch)
            else $error("Assertion failure: Status signals must only change on transition to s_lookup.");

        a_set_index_latch: assert property (p_set_index_latch)
            else $error("Assertion failure: Set index must only change during s_idle.");

        a_s_lookup_self_loop: assert property (p_s_lookup_self_loop)
            else $error("Assertion failure: State cannot stay in s_lookup for more than a cycle.");

        a_tag_latch: assert property (p_block_tag_latch)
            else $error("Assertion failure: Block tag can only change on miss completion.");

        a_block_hit_one_hot: assert property (p_block_hit_one_hot)
            else $error("Assertion failure: Only one block can be triggered hit at once.");

        a_set_way_access_one_hot: assert property (p_set_way_access_one_hot)
            else $error("Assertion failure: Only one set/way can be triggered hit at once.");

        a_set_not_full_lru_index_empty: assert property (p_set_not_full_lru_index_empty)
            else $error("Assertion failure: If set is not full, LRU should point to empty index.");

        // REVISIT (coverage)


    `endif

    // END block state logic

    // REVISIT PIPE
    // two-fifo holding outstanding core cache packets
    // allows simultaneous enqueue and dequeue on full
    // core_cache_pkt_t [1:0] fifo_mem_r, fifo_mem_n;
    // core_cache_pkt_t fifo_rd_pkt_lo;

    // logic fifo_empty_r, fifo_empty_n, fifo_full_r, fifo_full_n, fifo_enq, fifo_deq;
    // logic fifo_rd_ptr_r, fifo_rd_ptr_n, fifo_wr_ptr_r, fifo_wr_ptr_n;

    // assign fifo_enq = cc_valid_i & cc_ready_o;
    // assign fifo_deq = fifo_mem_r[fifo_ptr_r].we & write_complete || ~fifo_mem_r[fifo_ptr_r].we & read_complete;

    // assign fifo_empty_n = (fifo_empty_r & ~fifo_enq) || (~fifo_full_r & fifo_enq & fifo_deq);
    // assign fifo_full_n = (fifo_full_r & ~(fifo_deq & ~fifo_enq) || ~fifo_empty_r & fifo_enq & ~fifo_deq;

    // assign fifo_rd_ptr_n =  fifo_rd_ptr_r ^ fifo_deq; // fifo_deq? ~fifo_rd_ptr_r: fifo_rd_ptr_r;
    // assign fifo_wr_ptr_n =  fifo_wr_ptr_r ^ fifo_enq;

    // assign fifo_rd_pkt_lo = fifo_empty_r? '0: fifo_mem_r[fifo_rd_ptr_r];
    // assign cc_pkt_addr_tag_dly1 = {tag_width_lp{cc_valid_ready_r}} & fifo_mem_r[~fifo_wr_ptr_r].addr[31-:tag_width_lp];

    // always_comb begin
    //     fifo_mem_n = fifo_mem_r;
    //     if (fifo_enq)
    //         fifo_mem_r[fifo_wr_ptr_r] = cc_pkt;
    // end

    // always_ff @(posedge clk_i) begin
    //     if (~nreset_i) begin
    //         fifo_empty_r <= 1'b1;
    //         fifo_full_r <= 1'b0;
    //         fifo_rd_ptr_r <= 1'b0;
    //         fifo_wr_ptr_r <= 1'b0;
    //     end else begin
    //         fifo_empty_r <= fifo_empty_n;
    //         fifo_full_r <= fifo_full_n;
    //         fifo_rd_ptr_r <= fifo_rd_ptr_n;
    //         fifo_wr_ptr_r <= fifo_wr_ptr_n;
    //     end

    //     fifo_mem_r <= fifo_mem_n;
    // end


    // `ifndef DISABLE_TESTING
    //     always_ff @(posedge clk_i) begin
    //         if (nreset_i) begin
    //             assert(~(fifo_empty_r & fifo_full_r))
    //                 else $error("FIFO cannot be full and empty at same time");

    //             assert(~(fifo_empty_r & fifo_deq))
    //                 else $error("FIFO cannot be empty and dequeued");

    //             assert(~(fifo_full_r & fifo_enq & ~fifo_deq_r))
    //                 else $error("FIFO cannot be full and enqueued without dequeued");
    //         end
    //     end
    // `endif

    
endmodule


// Q: Can main memory accept a new request while servicing another and transferring data? 
// if so we need separate input channels from the snoop in vs the transfer in
// essentially can imagine we 
