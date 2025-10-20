`include "cache.svh"

module cache #(
    parameter block_size_p,      // words per block
    parameter sets_p,            // number of sets
    parameter ways_p,            // number of ways
    parameter dma_data_width_p   // bus transfer size in words
)(
    input  logic clk_i,
    input  logic reset_i,

    // Core Cache Interface
    input  logic            cc_valid_i,
    output logic            cc_ready_o,
    input  core_cache_pkt_t cc_pkt_i,

    output logic            cc_valid_o,
    input  logic            cc_yumi_i,
    output logic [31:0]     cc_rdata_o,

    // Cache Bus Interface
    output logic cb_valid_o,
    input  logic cb_yumi_i,
    output cache_bus_pkt_t cb_pkt_o,

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
    localparam offset_size_lp   = $clog2(block_size_p / 8);
    localparam index_size_lp    = $clog2(sets_p);
    localparam tag_size_lp      = 32 - offset_size_lp - index_size_lp;

    // Data transfer ratio
    localparam dma_blk_ratio_lp = $clog(dma_data_width_p/block_size_p);

    // lru, block_state, tag, data 
    cache_block_t [sets_p-1:0] [ways_p-1:0] cache_mem_r, cache_mem_n;
    logic [ways_p-1:0] [tag_size_lp-1:0] block_tag_r, block_tag_n;
    block_state_t [ways_p-1:0] block_state_r, block_state_n;

    core_cache_pkt_t cc_pkt_r;
    logic [tag_size_lp-1:0] cc_pkt_addr_dly1;
    logic [index_size_lp-1:0] set_index;
    logic write_complete, read_complete, cc_valid_ready, cc_valid_r;
    assign cc_valid_ready = cc_valid_i & cc_ready_o;

    assign set_index = cc_valid_ready? cc_pkt_i.addr[offset_size_lp+:index_size_lp]: cc_pkt_r.addr[offset_size_lp+:index_size_lp];

    always_comb begin
        for (int i = 0; i < ways_p; i++) begin
            block_tag_n[i] = cc_valid_ready? cache_mem_r[set_index][i].tag: block_tag_r[i];
            block_state_n[i] = cc_valid_ready? cache_mem_r[set_index][i].block_state: block_state_r[i];
        end
    end

    // Pipe stage 1
    always_ff @(posedge clk_i) begin
        if (~nreset_i)
            cc_valid_r <= 1'b0;
        else 
            cc_valid_r <= cc_valid_ready;

        cc_pkt_r <= cc_valid_ready? cc_pkt_i: cc_pkt_r;
        block_tag_r <= block_tag_n;
        block_state_r <= block_state_n;
    end

    logic tx_done, rx_done;
    logic read_write_miss, set_full, send_eviction;
    logic [offset_size_lp] cc_pkt_r_offset;
    logic [ways_size_lp-1:0] cc_ways_index, evict_block_way_index, evict_block_way_index_r, open_block_way_index;
    logic [31:0] evict_block_address;
    logic [(block_size_p*32)-1:0] cache_mem_rd_data_r, cache_mem_rd_data_n;

    assign cc_pkt_r_offset = cc_pkt_r.addr[offset_size_lp-1:0] << 3;

    always_comb begin
        read_write_miss = cc_valid_r;
        for (int i = 0; i < ways_p; i++) begin
            read_write_miss = read_write_miss & (block_tag_r[i] != cc_pkt_r.addr[31-:tag_size_lp]);
        end

        set_full = 1;
        for (int i = 0; i < ways_p; i++) begin
            set_full = set_full & (block_state_r[i] != s_invalid);
        end

        open_block_way_index = '0;
        for (int i = 0; i < ways_p; i++) begin
            open_block_way_index = open_block_way_index || {ways_size_lp{block_state_r[i] == s_invalid}} & ways_size_lp'(i);
        end
    end
    
    // REVISIT LRU
    assign evict_block_way_index = '0;
    assign evict_block_address = {block_tag_r[evict_block_way_index], cc_pkt_r.addr[offset_size_lp+:index_size_lp], offset_size_lp'0};

    assign send_eviction = read_write_miss & set_full & block_state_r[evict_block_way_index] == s_modified;

    // if not miss then matching index, else if miss but not full open index, else eviction index
    always_comb begin
        cc_ways_index = {ways_size_lp{read_write_miss}} & (open_block_way_index | ({ways_size_lp{set_full}} & evict_block_way_index));
        for (int i = 0; i < ways_p; i++) begin
            cc_ways_index = cc_ways_index | ({ways_size_lp{block_tag_r[i] == cc_pkt_r.addr[31-:tag_size_lp]}} & ways_size_lp'(i));
        end
    end

    assign cache_mem_rd_data_n = cache_mem_r[set_index][cc_ways_index].data;
    
    // Cache State Logic
    typedef enum {s_idle, s_lookup, s_evict, s_allocate_req, s_allocate_rx, s_write, s_valid} cache_control_t;
    cache_control_t cache_state_r, cache_state_n;

    always_comb begin
        case (cache_state_r)
            s_idle:     cache_state_n = cc_valid_ready? s_lookup: s_idle;

            s_lookup: begin
                if (read_write_miss) begin
                    if (set_full & block_state_r[evict_block_way_index] == s_modified)
                        cache_state_n = s_evict;
                    else
                        cache_state_n = cb_yumi_i? s_allocate_rx: s_allocate_req;
                end else if (~cc_pkt_r.we) begin
                    cache_state_n = s_valid;
                end else begin
                    cache_state_n = s_idle;
                end
            end

            s_evict:        cache_state_n = tx_done? s_allocate_req: s_evict;
            s_allocate_req: cache_state_n = cb_yumi_i? s_allocate_rx: s_allocate_req;
            s_allocate_rx:  cache_state_n = rx_done? (cc_pkt_r.we? s_write: s_valid): s_allocate_rx;

            s_write:        cache_state_n = s_idle;
            s_valid:        cache_state_n = cc_yumi_i? s_idle: s_valid;
        endcase
    end

    always_ff @(posedge clk_i) begin
        if (~nreset_i)
            cache_state_r <= s_idle;
        else
            cache_state_r <= cache_state_n;
    end

    // status signals
    assign write_complete = cache_state_r == s_write;
    assign read_complete = cache_state_r == s_valid;

    assign cc_ready_o = cache_state_r == s_idle;
    assign cc_valid_o = cache_state_r == s_valid;

    generate
        if (block_size_p != dma_data_width_p) begin : block_size_not_dma_data_width
            logic tx_start, rx_start;
            logic [dma_blk_ratio_lp-1:0] rx_count_r, rx_count_n, tx_count_r, tx_count_n;
            
            assign tx_done = tx_count_r == '1;
            assign rx_done = rx_count_r == '1;
            
            // REVISIT DMA TX SIZE

        end else begin : block_size_eq_dma_data_width
            assign tx_done = cb_yumi_i;
            assign rx_done = cb_valid_i;

            assign cb_pkt_o.wdata = cache_mem_rd_data_r;
        end
    endgenerate    

    always_comb begin
        cache_mem_n = cache_mem_r;
        
        // REVISIT PPA
        if (~nreset_i) begin
            for (int set_idx = 0; set_idx < sets_p; set_idx++) begin
                // Iterate over all ways (columns)
                for (int way_idx = 0; way_idx < ways_p; way_idx++) begin
                    // Conditionally set the block_state field of every cache line to s_invalid
                    cache_mem_n[set_idx][way_idx].block_state = s_invalid;
                end
            end
        end

        // Update block state on eviction
        if (send_eviction) begin
            cache_mem_n[set_index][evict_block_way_index].block_state = s_invalid;
        end

        // Update block state, data, tag, and LRU on allocation
        if (cb_valid_i) begin
            // REVISIT DMA TX SIZE
            cache_mem_n[set_index][cc_ways_index].block_state = s_shared; // REVISIT SNOOP (s_exclusive)
            cache_mem_n[set_index][cc_ways_index].data = cb_data_i;
            cache_mem_n[set_index][cc_ways_index].tag = cc_pkt_r.addr[31-:tag_size_lp]; // REVISIT PIPE
            cache_mem_n[set_index][cc_ways_index].lru = 1'b0; // REVISIT LRU
        end

        // Upon a write, update the data and LRU fields
        if (cache_state_r == s_write || (cache_state_r == s_lookup & ~read_write_miss & cc_pkt_r.we)) begin
            cache_mem_n[set_index][cc_ways_index].block_state = s_modified;
            cache_mem_n[set_index][cc_ways_index].lru = 1'b0; // REVISIT LRU

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
        cache_mem_r <= cache_mem_n; // REVISIT add reset back to invalid for block state
        cache_mem_rd_data_r <= cache_mem_rd_data_n;
        evict_block_way_index_r <= send_eviction? evict_block_way_index: evict_block_way_index_r;
    end
    
    assign cc_rdata_o = cache_mem_rd_data_r;
    assign cb_pkt_o.we = cache_state_r == s_evict;
    assign cb_pkt_o.addr = cache_state_r == s_evict? evict_block_address: {cc_pkt_r.addr[31:offset_size_lp], offset_size_lp'0};
    assign cb_valid_o = cache_state_r == s_evict || cache_state_r == s_allocate_req || read_write_miss & ~set_full ;

    // Embedded SVAs
    `ifndef DISABLE_TESTING
        logic be_non_contig;
        always_comb begin
            case (cc_pkt_i.be)
                4'b1111: be_non_contig = 1'b0;
                4'b1100: be_non_contig = 1'b0;
                4'b0110: be_non_contig = 1'b0;
                4'b0011: be_non_contig = 1'b0;
                4'b1000: be_non_contig = 1'b0;
                4'b0100: be_non_contig = 1'b0;
                4'b0010: be_non_contig = 1'b0;
                4'b0001: be_non_contig = 1'b0;
                default: be_non_contig = 1'b1;
            endcase
        end

        always_ff @(posedge clk_i) begin
            if (nreset_i) begin
                assert(~(cc_valid_i & be_non_contig))
                    else $error("Byte enable cannot have non-contiguous 1s");

                assert(~(cache_state_r == s_lookup & $past(cache_state_r) == s_lookup))
                        else $error("Cache cannot stay in s_lookup for multiple cycles");

                assert(~(cb_valid_i && cache_state_r != s_allocate_rx))
                        else $error("Should only receive main memory tx when expected");

                // Latching of status signals should only occur in s_lookup stage
                if (cache_state_r != s_lookup) begin
                    assert(cc_ways_index == $past(cc_ways_index_r))
                        else $error("cc_ways_index cannot change during processing");
                        
                    assert(read_write_miss == $past(read_write_miss))
                        else $error("read_write_miss cannot change during processing");

                    assert(set_full == $past(set_full))
                        else $error("set_full cannot change during processing");
                end

                if ($past(cache_state_r) != s_lookup && ~($past(cache_state_r) == s_allocate_rx && cache_state_r == s_valid)) begin
                    assert(cache_mem_rd_data_r == $past(cache_mem_rd_data_r))
                        else $error("cache_mem_rd_data_r cannot change unless after initial read or last process");
                end

                // block size and transfer size must be evenly divisible
            end
        end
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
    // assign cc_pkt_addr_tag_dly1 = {tag_size_lp{cc_valid_r}} & fifo_mem_r[~fifo_wr_ptr_r].addr[31-:tag_size_lp];

    // always_comb begin
    //     fifo_mem_n = fifo_mem_r;
    //     if (fifo_enq)
    //         fifo_mem_r[fifo_wr_ptr_r] = cc_pkt_i;
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
