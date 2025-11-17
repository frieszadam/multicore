`include "v/cache.vh"

module bus #(
    parameter num_caches_p,       // number of caches in system
    parameter block_width_p,      // words per block
    parameter dma_data_width_p,   // bus transfer size in words
    localparam cache_bus_pkt_width_lp = `cache_bus_pkt_width(dma_data_width_p)
) (
    input  logic clk_i,
    input  logic nreset_i,

    // Cache to Bus
    input  logic [num_caches_p-1:0] cb_valid_i,
    output logic [num_caches_p-1:0] cb_yumi_o,
    input  logic [num_caches_p-1:0] [cache_bus_pkt_width_lp-1:0] cb_pkt_i,

    // Memory to Bus
    input  logic mem_ready_i,
    output logic mem_valid_o,

    input  logic                   mem_valid_i,
    input  logic [(dma_data_width_p*32)-1:0] mem_data_i,

    output logic                   mem_we_o,
    output logic [31:0]            mem_addr_o,
    output logic [(dma_data_width_p*32)-1:0] mem_wdata_o,

    // Bus to Cache
    output logic [num_caches_p-1:0] cb_valid_o,
    output logic [(dma_data_width_p*32)-1:0]  cb_data_o
);
    localparam dma_blk_ratio_lp = $clog2(block_width_p/dma_data_width_p);
    localparam dma_data_size_lp = $clog2(dma_data_width_p);
    localparam num_cache_size_lp = $clog2(num_caches_p);
    
    `declare_cache_bus_pkt_t(dma_data_width_p);
    cache_bus_pkt_t [num_caches_p-1:0] cb_pkt;

    always_comb begin
        for (int c = 0; c < num_caches_p; c++)
            cb_pkt[c] = cache_bus_pkt_t'(cb_pkt_i[c]);
    end
    
    logic tx_inactive; // bus is ready to facilitate a new transaction
    logic [num_cache_size_lp-1:0] tx_cache_id;
    logic tx_done, rx_done;

    // block width = dma_data_width vs unequal case
    generate
        if (block_width_p != dma_data_width_p) begin : gen_block_width_not_dma_data_width
                logic mem_rd_valid, cache_wr_valid, tx_count_incr, rx_count_incr;
                logic [dma_blk_ratio_lp-1:0] tx_count_r, tx_count_n, rx_count_r, rx_count_n;

                always_comb begin
                    tx_inactive = tx_count_r == '0;

                    rx_count_incr = mem_valid_i;
                    tx_count_incr = mem_valid_o;

                    tx_count_n = tx_count_r + {'0, tx_count_incr};
                    rx_count_n = rx_count_r + {'0, rx_count_incr};

                    tx_done = ((tx_count_r == '1) & tx_count_incr);
                    rx_done = (rx_count_r == '1) & rx_count_incr;
                end

                always_ff @(posedge clk_i) begin
                    if (~nreset_i) begin
                        tx_count_r <= '0;
                        rx_count_r <= '0;
                    end else begin
                        tx_count_r <= tx_count_n;
                        rx_count_r <= rx_count_n;
                    end
                end

        end else begin : gen_block_size_eq_dma_data_width
            assign tx_done = cb_yumi_o[tx_cache_id];
            assign rx_done = mem_valid_i;
            assign tx_inactive = 1'b1;
        end
    endgenerate
        
    assign cb_data_o = mem_data_i;

    // multicore vs single core case
    generate
        if (num_caches_p == 1) begin : gen_one_cache
            assign cb_valid_o  = mem_valid_i;
            assign cb_yumi_o   = mem_ready_i & cb_valid_i;

            assign mem_valid_o = mem_ready_i & cb_valid_i;
            assign mem_we_o    = cb_pkt[0].we;
            assign mem_wdata_o = cb_pkt[0].wdata;
            assign mem_addr_o  = cb_pkt[0].addr;
            assign tx_cache_id = 1'b0;

        end else begin : gen_multi_cache
            // tx_begin corresponds to transmission to main memory beginning
            // of_enq corresponds to request accepted from caches into bus fifo
            logic [num_cache_size_lp-1:0] new_cache_id, rx_cache_id;            
            logic [num_caches_p-1:0] [num_cache_size_lp-1:0] lru_priority;
            logic [num_caches_p-1:0] [num_caches_p-1:0] onehot_lru;
            logic [num_caches_p-1:0] [num_caches_p-1:0] onehot_lru_masked;
            logic [num_caches_p-1:0] prior_eq_gnt_prior, prior_reqs, req_yumi, valid_req;
            logic [num_cache_size_lp-1:0] new_gnt_prior;
            logic [num_caches_p-1:0] yumi_inactive, yumi_active, eq_rx_cache_id_r;
            logic of_enq_ready, lru_valid_li, if_enq_ready, if_enq, if_deq, if_full, if_empty, cb_valid_tx_id;
            
            priority_lru #(
                .size_p(num_cache_size_lp)
            ) u_priority_lru (
                .clk_i, 
                .nreset_i,
                .valid_i(lru_valid_li),
                .index_i(new_cache_id),
                .priority_o(lru_priority)
            );
            
            // Use LRU priority to arbitrate current requests
            always_comb begin
                // onehot0 vectors holding the priority of request for each cache
                for (int c = 0; c < num_caches_p; c++) begin
                    for (int r = 0; r < num_caches_p; r++) begin
                        onehot_lru[c][r] = lru_priority[c] == num_cache_size_lp'(r);
                    end
                    onehot_lru_masked[c] = {num_caches_p{valid_req[c]}} & onehot_lru[c];
                end

                // Create vector holding whether requests exist at a certain priority
                prior_reqs = '0;
                for (int c = 0; c < num_caches_p; c++) begin
                    prior_reqs = prior_reqs | onehot_lru_masked[c];
                end
                
                // Priority encoder to select highest priority request
                new_gnt_prior = '0;
                for (int c = 0; c < num_caches_p; c++) begin
                    if (prior_reqs[c]) 
                        new_gnt_prior = num_cache_size_lp'(c);
                end

                // Generate yumi_inactive and convert back from accepted priority to cache id
                new_cache_id = '0;
                for (int c = 0; c < num_caches_p; c++) begin
                    prior_eq_gnt_prior[c] = lru_priority[c] == new_gnt_prior;
                    // new_cache_id = new_cache_id | ({num_cache_size_lp{prior_eq_gnt_prior[c]}} & num_cache_size_lp'(c));
                    new_cache_id = prior_eq_gnt_prior[c]? num_cache_size_lp'(c): new_cache_id;
                    yumi_inactive[c] = prior_eq_gnt_prior[c] & |valid_req & of_enq_ready & (if_enq_ready | cb_pkt[c].we);
                end

                // Generate cb_valid_o
                for (int c = 0; c < num_caches_p; c++) begin
                    eq_rx_cache_id_r[c] = rx_cache_id == num_cache_size_lp'(c);
                    cb_valid_o[c] = eq_rx_cache_id_r[c] & mem_valid_i;
                end
            end
            
            // allow simultaneous enq, deq when FIFO full
            assign if_enq_ready = ~if_full | if_deq;
            assign if_enq = |valid_req & of_enq_ready & if_enq_ready & ~cb_pkt[new_cache_id].we;
            assign if_deq = rx_done;

            if (block_width_p != dma_data_width_p) begin : gen_multi_cache_block_width_not_dma_data_width
                logic tx_begin, of_full, of_empty, of_deq, of_deq_ready, of_enq;
                logic [num_caches_p-1:0] burst_clr, burst_set, burst_pending_r, burst_pending_n, eq_tx_cache_id_r;
                logic [cache_bus_pkt_width_lp+num_cache_size_lp-1:0] of_wdata, of_rdata;
                cache_bus_pkt_t of_pkt_lo;

                always_comb begin
                    // allow simultaneous enq, deq when FIFO full
                    of_deq = tx_done;
                    of_enq_ready = ~of_full | of_deq;
                    of_enq = |valid_req & of_enq_ready & (cb_pkt[new_cache_id].we | if_enq_ready);

                    // Track outstanding burst reqs to not alloc more than one per ID into
                    // out-FIFO at once since they are fulfilled together
                    burst_clr = (1'b1 << tx_cache_id) & {num_caches_p{of_deq}};
                    burst_set = prior_eq_gnt_prior & {num_caches_p{of_enq}};
                    burst_pending_n = (burst_pending_r & ~burst_clr) | burst_set;
                    
                    of_deq_ready = ~of_empty | of_enq;
                    tx_begin = of_deq_ready & mem_ready_i & tx_inactive;
                end

                always_ff @(posedge clk_i) begin
                    if (~nreset_i) begin
                        burst_pending_r <= '0;
                    end else begin
                        burst_pending_r <= burst_pending_n;
                    end
                end

                always_comb begin
                    for (int c = 0; c < num_caches_p; c++) begin
                        eq_tx_cache_id_r[c] = tx_cache_id == num_cache_size_lp'(c);
                        yumi_active[c] = cb_valid_i[c] & eq_tx_cache_id_r[c] & mem_ready_i & ~tx_inactive;
                        cb_yumi_o[c]   = yumi_active[c] | yumi_inactive[c];
                    end
                end
                
                // Only accept requests for CPU that isn't awaiting a burst transfer
                assign valid_req = cb_valid_i & ~burst_pending_r;
                assign of_wdata  = {new_cache_id, cb_pkt_i[new_cache_id]};
                assign of_pkt_lo = cache_bus_pkt_t'(of_rdata[cache_bus_pkt_width_lp-1:0]);
                assign tx_cache_id = of_rdata[cache_bus_pkt_width_lp+num_cache_size_lp-1 -: num_cache_size_lp];
                assign lru_valid_li = of_enq;

                // holds data, addr, we, id for outgoing requests to main mem
                fifo #(
                    .data_width_p(cache_bus_pkt_width_lp+num_cache_size_lp),
                    .els_p(num_caches_p)
                ) u_out_fifo (
                    .clk_i,
                    .nreset_i,
                    .rd_i(of_deq),
                    .wr_i(of_enq),
                    .wdata_i(of_wdata),
                    
                    .full_o(of_full),
                    .empty_o(of_empty),
                    .rdata_o(of_rdata)
                );
                
                // Assign outputs
                assign mem_valid_o = mem_ready_i & of_deq_ready & cb_valid_i[tx_cache_id];
                assign mem_we_o    = of_pkt_lo.we;
                assign mem_wdata_o = of_pkt_lo.wdata;
                assign mem_addr_o  = tx_begin? of_pkt_lo.addr: cb_pkt[tx_cache_id].addr;

                `ifndef DISABLE_TESTING
                    // Out FIFO specific testing
                    property p_yumi_inactive_out_fifo_full;
                        @(posedge clk_i) if (nreset_i) |yumi_inactive |-> of_enq_ready;
                    endproperty

                    a_yumi_inactive_out_fifo_full: assert property (p_yumi_inactive_out_fifo_full)
                        else $error("Assertion failure: Cannot accept a new request when either out-FIFO is full.");

                    property p_of_deq_ready;
                        @(posedge clk_i) if (nreset_i) of_deq |-> of_deq_ready;
                    endproperty

                    a_of_deq_ready: assert property (p_of_deq_ready)
                        else $error("Assertion failure: Cannot dequeqe from out-FIFO when not ready.");
                `endif

            end else begin : gen_multi_cache_block_size_eq_dma_data_width
                assign of_enq_ready = 1'b1;
                assign tx_cache_id  = new_cache_id;
                assign valid_req    = cb_valid_i;
                assign lru_valid_li = |cb_yumi_o;

                assign cb_yumi_o   = yumi_inactive;
                assign mem_valid_o = mem_ready_i & cb_valid_i[new_cache_id];
                assign mem_we_o    = cb_pkt[new_cache_id].we;
                assign mem_wdata_o = cb_pkt[new_cache_id].wdata;
                assign mem_addr_o  = cb_pkt[new_cache_id].addr;
            end

            // holds cache id to route responses coming back from main mem
            fifo #(
                .data_width_p(num_cache_size_lp),
                .els_p(num_caches_p)
            ) u_in_fifo (
                .clk_i,
                .nreset_i,
                .rd_i(if_deq),
                .wr_i(if_enq),
                .wdata_i(new_cache_id),
                
                .full_o(if_full),
                .empty_o(if_empty),
                .rdata_o(rx_cache_id)
            );

            `ifndef DISABLE_TESTING
                logic if_deq_ready;
                assign if_deq_ready = ~if_empty | if_enq;

                property p_unexpected_mem_valid;
                    @(posedge clk_i) if (nreset_i) mem_valid_i |-> ~if_empty;
                endproperty

                a_unexpected_mem_valid: assert property (p_unexpected_mem_valid)
                    else $error("Assertion failure: in-FIFO cannot be empty when mem_valid_i is asserted.");

                property p_yumi_inactive_in_fifo_full;
                    @(posedge clk_i) if (nreset_i) |yumi_inactive |-> if_enq_ready | cb_pkt[new_cache_id].we;
                endproperty

                a_yumi_inactive_in_fifo_full: assert property (p_yumi_inactive_in_fifo_full)
                    else $error("Assertion failure: Cannot accept a new request when either in-FIFO is full.");

                property p_if_deq_ready;
                    @(posedge clk_i) if (nreset_i) if_deq |-> if_deq_ready;
                endproperty

                a_if_deq_ready: assert property (p_if_deq_ready)
                    else $error("Assertion failure: Cannot dequeqe from in-FIFO when not ready.");
            `endif
        end
    endgenerate

endmodule
