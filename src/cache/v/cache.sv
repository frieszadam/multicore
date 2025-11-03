`include "v/cache.svh"

// REVISIT (11/2, works under expectation off word aligned accesses - verify in spec)
module cache #(
    parameter block_width_p,      // words per block
    parameter sets_p,            // number of sets
    parameter ways_p,            // number of ways
    parameter dma_data_width_p   // bus transfer size in words
)(
    input  logic clk_i,
    input  logic nreset_i,

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
    localparam offset_size_lp   = $clog2(block_width_p) + 2; // offset within block, add 2 because block size in words
    localparam index_size_lp    = $clog2(sets_p);
    localparam tag_size_lp      = 32 - offset_size_lp - index_size_lp;

    // Data transfer ratio
    localparam dma_blk_ratio_lp = $clog2(dma_data_width_p/block_width_p);

    // lru, block_state, tag, data 
    cache_block_t [sets_p-1:0] [ways_p-1:0] cache_mem_r, cache_mem_n;
    logic [ways_p-1:0] [tag_size_lp-1:0] block_tag_r, block_tag_n;
    block_state_t [ways_p-1:0] block_state_r, block_state_n;
    logic [ways_p-1:0] [(block_width_p*32)-1:0] block_data_r, block_data_n;
    logic [ways_p-1:0] block_lru_r, block_lru_n;

    core_cache_pkt_t cc_pkt_r;
    logic [tag_size_lp-1:0] cc_pkt_addr_dly1;
    logic [index_size_lp-1:0] set_index;
    logic write_complete, read_complete, cc_valid_ready, cc_valid_ready_r;

    logic [(block_width_p*32)-1:0] main_mem_rdata, cc_rdata_src;

    typedef enum logic [2:0] {s_idle, s_lookup, s_tx_evict, s_allocate_req, s_allocate_rx} cache_control_t;
    cache_control_t cache_state_r, cache_state_n;

    assign cc_valid_ready = cc_valid_i & cc_ready_o;
    assign set_index = cc_valid_ready? cc_pkt_i.addr[offset_size_lp+:index_size_lp]: cc_pkt_r.addr[offset_size_lp+:index_size_lp];

    // Load block tag, state, data, and lru for all blocks in set upon receiving request
    always_comb begin
        for (int i = 0; i < ways_p; i++) begin
            block_tag_n[i] = cc_valid_ready? cache_mem_r[set_index][i].tag: block_tag_r[i];
            block_state_n[i] = cc_valid_ready? cache_mem_r[set_index][i].block_state: block_state_r[i];
            block_data_n[i] = cc_valid_ready? cache_mem_r[set_index][i].data: block_data_r[i];
            block_lru_n[i] = cc_valid_ready? cache_mem_r[set_index][i].lru: block_lru_r[i];
        end
    end

    // Pipe stage 1
    always_ff @(posedge clk_i) begin
        if (~nreset_i)
            cc_valid_ready_r <= 1'b0;
        else 
            cc_valid_ready_r <= cc_valid_ready;

        cc_pkt_r      <= cc_valid_ready? cc_pkt_i: cc_pkt_r;
        block_tag_r   <= block_tag_n;
        block_state_r <= block_state_n;
        block_data_r  <= block_data_n;
        block_lru_r   <= block_lru_n;
    end

    logic tx_done, rx_done;
    logic read_write_miss, set_full, send_eviction;
    logic [offset_size_lp+2:0] cc_pkt_r_offset; // because we left shift by three to convert byte to bit 
    logic [ways_size_lp-1:0] cc_ways_index, cc_ways_index_n, cc_ways_index_r, evict_block_way_index, open_block_way_index; // evict_block_way_index_r
    logic [ways_p-1:0] block_state_invalid, block_hit;
    logic [31:0] evict_block_address;

    assign cc_pkt_r_offset = cc_pkt_r.addr[offset_size_lp-1:0] <<< 3;

    always_comb begin
        read_write_miss = cc_valid_ready_r;
        set_full = 1'b1;
        open_block_way_index = '0;

        for (int i = 0; i < ways_p; i++) begin
            block_state_invalid[i] = block_state_r[i] == s_invalid;
            block_hit[i] = ~block_state_invalid[i] & block_tag_r[i] == cc_pkt_r.addr[31-:tag_size_lp];

            // not a miss if any valid way holds a matching tag
            read_write_miss = read_write_miss & ~block_hit[i];
            set_full = set_full & ~block_state_invalid[i];
            open_block_way_index = open_block_way_index | ({ways_size_lp{block_state_invalid[i]}} & ways_size_lp'(i));
        end
    end

    // REVISIT LRU
    assign evict_block_way_index = '0;

    // cc_ways_index is used since it is registered, saved beyond s_lookup
    assign evict_block_address = {block_tag_r[cc_ways_index], cc_pkt_r.addr[offset_size_lp+:index_size_lp], offset_size_lp'(0)};
    assign send_eviction = (cache_state_r == s_lookup & read_write_miss & set_full & block_state_r[cc_ways_index] == s_modified) || (cache_state_r == s_tx_evict);

    // if not miss then matching index, else if miss but not full open index, else eviction index
    always_comb begin
        cc_ways_index_n = {ways_size_lp{read_write_miss}} & (open_block_way_index | ({ways_size_lp{set_full}} & evict_block_way_index));
        for (int i = 0; i < ways_p; i++) begin
            cc_ways_index_n = cc_ways_index_n | ({ways_size_lp{block_hit[i]}} & ways_size_lp'(i));
        end
    end


    // Cache State Logic
    always_comb begin
        case (cache_state_r)
            s_idle:     cache_state_n = cc_valid_ready? s_lookup: s_idle;

            s_lookup: begin
                if (read_write_miss) begin
                    if (set_full & block_state_r[evict_block_way_index] == s_modified)
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

    // status signals
    assign write_complete = cc_valid_o & cc_pkt_r.we;
    assign read_complete  = cc_valid_o & ~cc_pkt_r.we;

    assign cc_ready_o = cache_state_r == s_idle;
    assign cc_valid_o = cache_state_r != s_idle & cache_state_n == s_idle;

    generate
        if (block_width_p != dma_data_width_p) begin : block_size_not_dma_data_width
            logic tx_start, rx_start;
            logic [dma_blk_ratio_lp-1:0] rx_count_r, rx_count_n, tx_count_r, tx_count_n;
            
            assign tx_done = tx_count_r == '1;
            assign rx_done = rx_count_r == '1;
            
            // REVISIT DMA TX SIZE
            assign main_mem_rdata = '0; // probably shift reg output, must be valid when rx_done
        end else begin : block_size_eq_dma_data_width
            assign tx_done = cb_yumi_i;
            assign rx_done = cb_valid_i;

            assign cb_pkt_o.wdata = block_data_r[cc_ways_index]; // eviction index stored in cc_ways_index
            assign main_mem_rdata = cb_data_i;
        end
    endgenerate    

    logic [(block_width_p*32)-1:0] main_mem_wdata;
    logic cache_mem_write;
    assign cache_mem_write = cache_state_r == s_lookup & ~read_write_miss & cc_pkt_r.we;

    always_comb begin
        main_mem_wdata = main_mem_rdata;

        if (cc_pkt_r.be[0] & cc_pkt_r.we)
            main_mem_wdata[cc_pkt_r_offset +:8] = cc_pkt_r.wdata[7:0];
        if (cc_pkt_r.be[1] & cc_pkt_r.we)
            main_mem_wdata[cc_pkt_r_offset+8 +:8] = cc_pkt_r.wdata[15:8];
        if (cc_pkt_r.be[2] & cc_pkt_r.we)
            main_mem_wdata[cc_pkt_r_offset+16 +:8] = cc_pkt_r.wdata[23:16];
        if (cc_pkt_r.be[3] & cc_pkt_r.we)
            main_mem_wdata[cc_pkt_r_offset+24 +:8] = cc_pkt_r.wdata[31:24];
    end

    // REVISIT (11/2, consider converting to structural logic)
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
                    cache_mem_n[set_idx][way_idx].tag = '0;
                    `endif
                end
            end
        end

        // Update block state, data, tag, and LRU on allocation
        else if (rx_done) begin
            // REVISIT DMA TX SIZE (can either load entire block at once or write in dma_data_width_p chunks for better PPA)
            cache_mem_n[set_index][cc_ways_index].block_state = cc_pkt_r.we? s_modified: s_shared; // REVISIT SNOOP (s_exclusive)
            cache_mem_n[set_index][cc_ways_index].data = main_mem_wdata;
            cache_mem_n[set_index][cc_ways_index].tag = cc_pkt_r.addr[31-:tag_size_lp]; // REVISIT PIPE
            cache_mem_n[set_index][cc_ways_index].lru = 1'b0; // REVISIT LRU
        end

        // Upon a non-miss write, update the data and LRU fields
        else if (cache_mem_write) begin
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
        cache_mem_r <= cache_mem_n;
        cc_ways_index_r <= cc_valid_ready_r? cc_ways_index_n: cc_ways_index_r;
    end
    
    assign cc_ways_index = cc_valid_ready_r? cc_ways_index_n: cc_ways_index_r;

    assign cc_rdata_src = (cache_state_r == s_allocate_rx)? main_mem_rdata: block_data_r[cc_ways_index];
    assign cc_rdata_o = cc_rdata_src[cc_pkt_r_offset +: 32] & {32{~write_complete}};

    assign cb_pkt_o.we = send_eviction;
    assign cb_pkt_o.addr = send_eviction? evict_block_address: {cc_pkt_r.addr[31:offset_size_lp], offset_size_lp'(0)};
    assign cb_valid_o = send_eviction || cache_state_r == s_allocate_req || (cache_state_r == s_lookup & read_write_miss);

    // Embedded SVAs
    `ifndef DISABLE_TESTING
        
        // Signals for viewing Verdi (structs not supported)
        logic cc_pkt_we_i;
        logic [3:0] cc_pkt_be_i;
        logic [31:0] cc_pkt_addr_i, cc_pkt_wdata_i;

        assign cc_pkt_we_i = cc_pkt_i.we;
        assign cc_pkt_be_i = cc_pkt_i.be;
        assign cc_pkt_addr_i = cc_pkt_i.addr;
        assign cc_pkt_wdata_i = cc_pkt_i.wdata;

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

        assign cb_pkt_we_o = cb_pkt_o.we;
        assign cb_pkt_addr_o = cb_pkt_o.addr;
        assign cb_pkt_wdata_o = cb_pkt_o.wdata;

        logic [(block_width_p*32)-1:0] cache_mem_data_n, cache_mem_data_r;
        assign cache_mem_data_n = cache_mem_n[set_index][cc_ways_index].data;
        assign cache_mem_data_r = cache_mem_r[set_index][cc_ways_index].data;

        // Auxilliary testing code
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
                4'b0000: be_non_contig = 1'b0;
                default: be_non_contig = 1'b1;
            endcase
        end

        // Properties
        property p_main_mem_rx;
            @(posedge clk_i) if (nreset_i)
                cb_valid_i |-> cache_state_r == s_allocate_rx;
        endproperty

        property p_be_contiguous;
            @(posedge clk_i) if (nreset_i)
                cc_valid_i & cc_pkt_i.we |-> ~be_non_contig;
        endproperty

        property p_s_lookup_self_loop;
            @(posedge clk_i) if (nreset_i)
                cache_state_r == s_lookup |=> cache_state_r != s_lookup;
        endproperty

        property p_cc_ways_index_latch;
            @(posedge clk_i) if (nreset_i & $past(nreset_i))
                (cache_state_r != s_lookup) |-> cc_ways_index == $past(cc_ways_index);
        endproperty

        property p_set_full_latch;
            @(posedge clk_i) if (nreset_i & $past(nreset_i))
                (cache_state_r != s_lookup) |-> set_full == $past(set_full);
        endproperty

        property p_s_lookup_latch;
            @(posedge clk_i) p_set_full_latch and p_cc_ways_index_latch;
        endproperty

        logic [sets_p-1:0] [ways_p-1:0] [tag_size_lp-1:0] cache_mem_tag_r;
        always_comb begin
            for (int s = 0; s < sets_p; s++) begin
                for (int w = 0; w < ways_p; w++) begin
                    cache_mem_tag_r[s][w] = cache_mem_r[s][w].tag; 
                end
            end
        end

        property p_block_tag_latch;
            @(posedge clk_i) if (nreset_i) ~rx_done |=> cache_mem_tag_r == $past(cache_mem_tag_r);
        endproperty

        // REVISIT failing property, doesn't account for undefined data situation
        // property p_cache_mem_rd_data_latch;
        //     @(posedge clk_i) if (nreset_i) 
        //         (cache_state_r != s_lookup && ~(cache_state_r == s_allocate_rx && cache_state_n == s_valid)) |=>
        //         cache_mem_rdata_r == $past(cache_mem_rdata_r);
        // endproperty

        // Property assertions
        a_main_mem_rx: assert property (p_main_mem_rx)
            else $error("Assertion failure: Cannot receive memory response unless in s_allocate_rx.");

        a_be_contiguous: assert property (p_be_contiguous)
            else $error("Assertion failure: Byte enable must be contiguous.");

        a_s_lookup_latch: assert property (p_s_lookup_latch)
            else $error("Assertion failure: Status signals must only change on transition to s_lookup.");

        a_s_lookup_self_loop: assert property (p_s_lookup_self_loop)
            else $error("Assertion failure: State cannot stay in s_lookup for more than a cycle.");

        a_tag_latch: assert property (p_block_tag_latch)
            else $error("Assertion failure: Block tag can only change on miss completion.");

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
    // assign cc_pkt_addr_tag_dly1 = {tag_size_lp{cc_valid_ready_r}} & fifo_mem_r[~fifo_wr_ptr_r].addr[31-:tag_size_lp];

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
