`include "cache.vh"

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

    // Snoop Controller to Bus
    input logic [num_caches_p-1:0] sb_wait_i,
    input logic [num_caches_p-1:0] sb_hit_i,
    input logic [num_caches_p-1:0] sb_valid_i,
    input logic [num_caches_p-1:0] [(dma_data_width_p*32)-1:0] sb_data_i,
    
    output logic [num_caches_p-1:0] sb_valid_o,
    output logic sb_last_rx_o,
    output logic sb_tx_begin_o,
    output logic [cache_bus_pkt_width_lp-1:0] sb_pkt_o,

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
    output logic cb_ld_ex_o,
    output logic [(dma_data_width_p*32)-1:0]  cb_data_o
);

    localparam dma_blk_ratio_lp      = block_width_p / dma_data_width_p;
    localparam dma_blk_ratio_size_lp = $clog2(dma_blk_ratio_lp);
    localparam dma_data_size_lp      = $clog2(dma_data_width_p);
    localparam num_cache_size_lp     = $clog2(num_caches_p);
    localparam offset_width_lp       = $clog2(block_width_p) + 2;

    `declare_cache_bus_pkt_t(dma_data_width_p);
    cache_bus_pkt_t [num_caches_p-1:0] cb_pkt;
    cache_bus_pkt_t curr_bus_pkt, sb_pkt;
    bus_req_type_t curr_req_type;

    logic tx_inactive;
    logic [num_cache_size_lp-1:0] tx_cache_id;
    logic [num_caches_p-1:0] sb_wait_valid;
    logic tx_done, rx_done;

    always_comb begin
        for (int c = 0; c < num_caches_p; c++)
            cb_pkt[c] = cache_bus_pkt_t'(cb_pkt_i[c]);
    end
    
    assign curr_req_type = curr_bus_pkt.req_type;
    assign sb_pkt.req_type = curr_bus_pkt.req_type;
    assign sb_pkt.wdata = curr_bus_pkt.wdata;

    assign sb_pkt_o  = cache_bus_pkt_t'(sb_pkt);
    assign sb_wait_valid = sb_wait_i & ~sb_valid_i;

    // block width = dma_data_width vs unequal case
    generate
        if (block_width_p != dma_data_width_p) begin : gen_block_width_not_dma_data_width
                logic mem_rd_valid, cache_wr_valid, tx_count_incr, rx_count_incr;
                logic [dma_blk_ratio_size_lp-1:0] tx_count_r, tx_count_n, rx_count_r, rx_count_n;

                always_comb begin
                    tx_inactive = tx_count_r == '0;

                    rx_count_incr = mem_valid_i;
                    tx_count_incr = mem_valid_o;

                    tx_count_n = tx_count_r + {'0, tx_count_incr};
                    rx_count_n = rx_count_r + {'0, rx_count_incr};

                    tx_done = tx_count_r == '1 & tx_count_incr;
                    rx_done = (rx_count_r == '1) & rx_count_incr;

                    sb_last_rx_o = tx_count_r == '1;
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
            assign tx_done = ~|sb_wait_valid & mem_ready_i;
            assign rx_done = mem_valid_i;
            assign tx_inactive  = 1'b1;
            assign sb_last_rx_o = 1'b1;
        end
    endgenerate

    // multicore vs single core case
    generate
        if (num_caches_p == 1) begin : gen_one_cache
            assign tx_cache_id = 1'b0;

            assign cb_valid_o   = mem_valid_i | (curr_req_type == op_up_exclusive);
            assign cb_yumi_o    = cb_valid_i & (mem_ready_i | (curr_req_type == op_up_exclusive));
            assign curr_bus_pkt = cb_pkt[0];
            assign cb_data_o    = mem_data_i;
            assign cb_ld_ex_o   = 1'b1;

            assign mem_valid_o = mem_ready_i & cb_valid_i;
            assign mem_addr_o  = cb_pkt[0].addr;
            assign mem_wdata_o = curr_bus_pkt.wdata;
            assign mem_we_o    = curr_req_type == op_write_back;

            assign sb_valid_o = 1'b0;
            assign sb_tx_begin_o = 1'b0;
            
        end else begin : gen_multi_cache
            // tx_begin corresponds to transmission to main memory beginning
            // of_enq corresponds to request accepted from caches into bus fifo
            logic [num_cache_size_lp-1:0] new_cache_id, rx_cache_id, sb_rd_index;            
            logic [num_caches_p-1:0] [num_cache_size_lp-1:0] lru_priority;
            logic [num_caches_p-1:0] [num_caches_p-1:0] onehot_lru;
            logic [num_caches_p-1:0] [num_caches_p-1:0] onehot_lru_masked;
            logic [num_caches_p-1:0] prior_eq_gnt_prior, prior_reqs, req_yumi, valid_req;
            logic [num_cache_size_lp-1:0] new_gnt_prior;
            logic [num_caches_p-1:0] yumi_active, eq_rx_cache_id_r, eq_tx_cache_id_r;
            logic of_enq_ready, lru_valid_li, if_enq_ready, if_enq, if_deq, if_full, if_empty, rx_wr_op;

            logic tx_begin, tx_ongoing, ld_shared_n, ld_shared_r, sb_valid_fwd_cache, yumi_state_valid,
                sb_valid_op_up_ex, of_deq_ready, yumi_ahead_r, yumi_done_r, cache_fwd_yumi;
            logic [(dma_data_width_p*32)-1:0] sb_rdata;
            logic [num_cache_size_lp:0] if_wdata, if_rdata;
            logic [num_caches_p-1:0] tx_cache_id_dec, cb_pkt_up;

            typedef enum logic [1:0] {s_ready, s_wait, s_ld_cache, s_xmem} bus_state_t;
            bus_state_t bus_state_r, bus_state_n;

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
                for (int c = 0; c < num_caches_p; c++) begin
                    cb_pkt_up[c] = cb_pkt[c].req_type == op_up_exclusive;
                end

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

                // Convert back from accepted priority to cache id
                new_cache_id = '0;
                for (int c = 0; c < num_caches_p; c++) begin
                    prior_eq_gnt_prior[c] = lru_priority[c] == new_gnt_prior;
                    new_cache_id = prior_eq_gnt_prior[c]? num_cache_size_lp'(c): new_cache_id;
                end
            end

            if (block_width_p != dma_data_width_p) begin
                assign sb_valid_fwd_cache = bus_state_r == s_ld_cache & mem_ready_i;

                logic [31:0] mem_addr_sb_fwd_r, mem_addr_sb_fwd_n;
                logic mem_valid_state_ready;

                assign mem_valid_state_ready = ~|sb_valid_i? bus_state_r != s_ready: bus_state_r == s_ld_cache;
                assign mem_valid_o = mem_ready_i & of_deq_ready & ~|sb_wait_valid & ~(curr_req_type == op_up_exclusive) & mem_valid_state_ready;

                assign mem_addr_o  = (bus_state_r == s_ld_cache)? mem_addr_sb_fwd_r: curr_bus_pkt.addr;
                assign mem_addr_sb_fwd_n = |cb_yumi_o? curr_bus_pkt.addr: mem_addr_sb_fwd_r;

                always_ff @(posedge clk_i)
                    mem_addr_sb_fwd_r <= mem_addr_sb_fwd_n;

            end else begin
                assign sb_valid_fwd_cache = ~|sb_wait_valid & |sb_valid_i & mem_ready_i;

                assign mem_valid_o = mem_ready_i & of_deq_ready & ~|sb_wait_valid & ~(curr_req_type == op_up_exclusive) & bus_state_r != s_ready;
                assign mem_addr_o  = curr_bus_pkt.addr;
            end

            assign sb_valid_op_up_ex  = ~|sb_wait_valid & bus_state_r == s_wait & curr_req_type == op_up_exclusive;
    
            always_comb begin
                for (int c = 0; c < num_caches_p; c++) begin
                    tx_cache_id_dec[c] = tx_cache_id == num_cache_size_lp'(c);
                end

                tx_ongoing = (bus_state_r != s_ready) | of_deq_ready;
                sb_valid_o = ~tx_cache_id_dec & {num_caches_p{tx_ongoing}};

                sb_rd_index = '0;
                for (int c = 0; c < num_caches_p; c++) begin
                    sb_rd_index = sb_rd_index | ({num_cache_size_lp{sb_valid_i[c]}} & num_cache_size_lp'(c));
                end

                // Generate cb_valid_o and cb_yumi_o
                for (int c = 0; c < num_caches_p; c++) begin
                    eq_rx_cache_id_r[c] = rx_cache_id == num_cache_size_lp'(c);
                    eq_tx_cache_id_r[c] = tx_cache_id == num_cache_size_lp'(c);
                    cb_valid_o[c] = (eq_rx_cache_id_r[c] & mem_valid_i) | (eq_tx_cache_id_r[c] & (sb_valid_fwd_cache | sb_valid_op_up_ex));

                    cb_yumi_o[c] = eq_tx_cache_id_r[c] & ~|sb_wait_valid & of_deq_ready & bus_state_r != s_ready & yumi_state_valid;
                end
            end
            
            assign yumi_done_r = sb_last_rx_o & yumi_ahead_r;
            assign cache_fwd_yumi = |{~yumi_ahead_r, cb_valid_o} & ~yumi_done_r;
            assign yumi_state_valid = ~|sb_valid_i? (mem_ready_i & bus_state_r != s_ld_cache): cache_fwd_yumi;

            always_comb begin
                case(bus_state_r)
                    s_ready: bus_state_n = tx_begin? s_wait: s_ready;
                    s_wait: begin
                        if (sb_wait_valid == '0) begin
                            if (curr_req_type == op_up_exclusive | tx_done)
                                bus_state_n = s_ready;
                            else if (|sb_valid_i)
                                bus_state_n = s_ld_cache;
                            else
                                bus_state_n = s_xmem;
                        end else
                            bus_state_n = s_wait;
                    end
                    s_ld_cache: bus_state_n = tx_done? s_ready: s_ld_cache;
                    s_xmem:     bus_state_n = tx_done? s_ready: s_xmem;
                    default:    bus_state_n = s_ready;
                endcase
            end

            always_ff @(posedge clk_i) begin
                if (~nreset_i) begin
                    bus_state_r <= s_ready;
                    ld_shared_r <= 1'b0;
                end else begin
                    bus_state_r <= bus_state_n;
                    ld_shared_r <= ld_shared_n;
                end
            end

            assign ld_shared_n = (ld_shared_r & ~(bus_state_r == s_ready)) | (bus_state_r == s_wait & |sb_hit_i);
            assign cb_ld_ex_o  = ~ld_shared_r;
            
            assign sb_rdata  = sb_data_i[sb_rd_index];
            assign cb_data_o = |sb_valid_i? sb_rdata: mem_data_i;

            assign mem_we_o = |{curr_req_type == op_write_back, sb_valid_i};
            assign sb_tx_begin_o = (bus_state_r == s_ready) & tx_begin;

            logic of_full, of_empty, of_deq, of_enq;
            logic [num_caches_p-1:0] burst_clr, burst_set, burst_pending_r, burst_pending_n;

            always_comb begin
                // allow simultaneous enq, deq when FIFO full
                of_deq = bus_state_r != s_ready & bus_state_n == s_ready;
                of_enq_ready = ~of_full | of_deq;
                of_enq = |valid_req & of_enq_ready & (cb_pkt_up[new_cache_id] | if_enq_ready);

                // Track outstanding burst reqs to not alloc more than one per ID into
                // out-FIFO at once since they are fulfilled together
                burst_clr = (1'b1 << tx_cache_id) & {num_caches_p{of_deq}};
                burst_set = prior_eq_gnt_prior & {num_caches_p{of_enq}};
                burst_pending_n = (burst_pending_r & ~burst_clr) | burst_set;
                
                of_deq_ready = ~of_empty | of_enq;
                tx_begin = of_deq_ready & tx_inactive;
            end

            always_ff @(posedge clk_i) begin
                if (~nreset_i) begin
                    burst_pending_r <= '0;
                end else begin
                    burst_pending_r <= burst_pending_n;
                end
            end

            // Only accept requests for CPU that isn't awaiting a burst transfer
            assign valid_req = cb_valid_i & ~burst_pending_r;
            assign curr_bus_pkt = cb_pkt[tx_cache_id];
            assign lru_valid_li = of_enq;

            // holds data, addr, we, id for outgoing requests to main mem
            fifo #(
                .data_width_p(num_cache_size_lp),
                .els_p(num_caches_p)
            ) u_out_fifo (
                .clk_i,
                .nreset_i,
                .rd_i(of_deq),
                .wr_i(of_enq),
                .wdata_i(new_cache_id),
                
                .full_o(of_full),
                .empty_o(of_empty),
                .rdata_o(tx_cache_id)
            );
            
            logic yumi_ahead_set, yumi_ahead_n;

            assign yumi_ahead_set = |sb_valid_i & |cb_yumi_o & (~|cb_valid_o | yumi_ahead_r);
            assign yumi_ahead_n = yumi_ahead_set | (yumi_ahead_r & ~|cb_valid_o);

            always_ff @(posedge clk_i) begin
                if (~nreset_i) begin
                    yumi_ahead_r <= 1'b0;
                end else begin
                    yumi_ahead_r <= yumi_ahead_n; 
                end
            end

            assign sb_pkt.addr = curr_bus_pkt.addr;
            assign mem_wdata_o  = |sb_valid_i? sb_rdata: curr_bus_pkt.wdata;

            // allow simultaneous enq, deq when FIFO full
            assign if_enq_ready = ~if_full | if_deq;
            assign if_enq = if_enq_ready & bus_state_r == s_wait & bus_state_n != s_wait & ~|sb_valid_i & curr_req_type != op_up_exclusive & curr_req_type != op_write_back;
            assign if_deq = rx_done;
                        
            // holds cache id to route responses coming back from main mem
            fifo #(
                .data_width_p(num_cache_size_lp),
                .els_p(num_caches_p)
            ) u_in_fifo (
                .clk_i,
                .nreset_i,
                .rd_i(if_deq),
                .wr_i(if_enq),
                .wdata_i(tx_cache_id),
                
                .full_o(if_full),
                .empty_o(if_empty),
                .rdata_o(rx_cache_id)
            );

            `ifndef DISABLE_TESTING
                logic if_deq_ready;
                assign if_deq_ready = ~if_empty | if_enq;

                property p_unexpected_mem_valid;
                    @(posedge clk_i) if (nreset_i)
                        mem_valid_i |->~if_empty | bus_state_r == s_ld_cache | $past(bus_state_r) == s_ld_cache;
                endproperty

                a_unexpected_mem_valid: assert property (p_unexpected_mem_valid)
                    else $error("Assertion failure: in-FIFO cannot be empty when mem_valid_i is asserted.");

                property p_if_deq_ready;
                    @(posedge clk_i) if (nreset_i) if_deq |-> if_deq_ready;
                endproperty

                a_if_deq_ready: assert property (p_if_deq_ready)
                    else $error("Assertion failure: Cannot dequeqe from in-FIFO when not ready.");

                property p_sb_valid_timing;
                    @(posedge clk_i) if (nreset_i)
                        |sb_valid_i |-> ~|sb_wait_valid & curr_req_type != op_up_exclusive & (bus_state_r == s_wait | bus_state_r == s_ld_cache);
                endproperty

                a_sb_valid_timing: assert property (p_sb_valid_timing)
                    else $error("Assertion failure: Cannot receive sb_valid when not expected.");

                property p_of_deq_ready;
                    @(posedge clk_i) if (nreset_i) of_deq |-> of_deq_ready;
                endproperty

                a_of_deq_ready: assert property (p_of_deq_ready)
                    else $error("Assertion failure: Cannot dequeqe from out-FIFO when not ready.");

            `endif
        end
    endgenerate
    
    `ifndef DISABLE_TESTING

        wire logic [31:0] bus_pkt_addr0 = cb_pkt[0].addr;
        wire logic [31:0] bus_pkt_addr1 = cb_pkt[1].addr;

        bus_req_type_t curr_bus_pkt_req_type, sb_pkt_req_type;
        logic [31:0] curr_bus_pkt_addr, sb_pkt_addr;
        logic [(32*dma_data_width_p)-1:0] curr_bus_pkt_wdata, sb_pkt_wdata;

        assign curr_bus_pkt_req_type = curr_bus_pkt.req_type;
        assign curr_bus_pkt_addr  = curr_bus_pkt.addr;
        assign curr_bus_pkt_wdata = curr_bus_pkt.wdata;

        assign sb_pkt_req_type = sb_pkt.req_type;
        assign sb_pkt_addr = sb_pkt.addr;
        assign sb_pkt_wdata = sb_pkt.wdata;

        property p_sb_valid_onehot;
            @(posedge clk_i) if (nreset_i) $onehot0(sb_valid_i);
        endproperty

        a_sb_valid_onehot: assert property (p_sb_valid_onehot)
            else $error("Assertion failure: sb_valid_i must only be asserted by one cache at a time.");

        property p_sb_valid_deasserted_tx_done;
            @(posedge clk_i) if (nreset_i)
                |sb_valid_i |=> |sb_valid_i | $past(tx_done) | $past(curr_req_type == op_ld_exclusive);
        endproperty
        
        a_sb_valid_deasserted_tx_done: assert property (p_sb_valid_deasserted_tx_done)
            else $error("Assertion failure: Once sb_valid_i is asserted it can only deassert when TX is done.");

    `endif
    
endmodule
