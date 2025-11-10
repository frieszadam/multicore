`include "v/cache.svh"

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
    
    `declare_cache_bus_pkt_t(dma_data_width_p)
    cache_bus_pkt_t [num_caches_p-1:0] cb_pkt;
    assign cb_pkt = cb_pkt_i;

    logic [num_caches_p-1:0] [31:0] pkt_addr;
    logic [num_caches_p-1:0] [(dma_data_width_p*32)-1:0] pkt_wdata;
    logic [num_caches_p-1:0] pkt_we;
    
    logic tx_inactive, tx_begin; // bus is ready to facilitate a new transaction
    logic mem_ld_r, mem_ld_n, mem_ld_set, mem_ld_clr;    // bus is waiting for the response of a load, serializes accesses
    logic [num_cache_size_lp-1:0] cache_id;

    // block width = dma_data_width vs unequal case
    generate
        if (block_width_p != dma_data_width_p) begin : block_width_not_dma_data_width
                logic mem_rd_valid, cache_wr_valid, tx_count_incr;
                logic [dma_blk_ratio_lp-1:0] tx_count_r, tx_count_n;

                always_comb begin
                    tx_inactive = (tx_count_r == '0) & ~mem_ld_r;
                    
                    mem_rd_valid   = mem_ld_r & mem_valid_i;
                    cache_wr_valid = ~mem_ld_r & mem_we_o & cb_valid_i[cache_id] & mem_ready_i;

                    mem_ld_clr   = (tx_count_r == '1) & mem_valid_i;
                    tx_count_incr = mem_rd_valid | cache_wr_valid;

                    tx_count_n = tx_count_r + {'0, tx_count_incr};
                end

                always_ff @(posedge clk_i) begin
                    if (~nreset_i) begin
                        tx_count_r <= '0;
                    end else begin
                        tx_count_r <= tx_count_n;
                    end
                end

        end else begin : block_size_eq_dma_data_width
            assign tx_inactive = ~mem_ld_r;
            assign mem_ld_clr  = mem_valid_i;
        end
    endgenerate

    assign tx_begin   = |cb_valid_i & mem_ready_i & tx_inactive; // cache initiates tx
    assign mem_ld_set = tx_begin & ~mem_we_o;
    assign mem_ld_n   = (mem_ld_r & ~mem_ld_clr) | mem_ld_set;

    always_ff @(posedge clk_i) begin
        if (~nreset_i) begin
            mem_ld_r   <= '0;
        end else begin
            mem_ld_r   <= mem_ld_n;
        end
    end

    assign mem_addr_o = pkt_addr[cache_id];
    
    always_comb begin
        for (int i = 0; i < num_caches_p; i++) begin
            pkt_addr[i] = cb_pkt[i].addr;
            pkt_wdata[i] = cb_pkt[i].wdata;
            pkt_we[i] = cb_pkt[i].we;
        end
    end

    assign cb_data_o   = mem_data_i;
    assign mem_valid_o = |cb_valid_i & mem_ready_i;
    assign mem_we_o    = pkt_we[cache_id];
    assign mem_wdata_o = pkt_wdata[cache_id];

    // multicore vs single core case
    generate
        if (num_caches_p == 1) begin : gen_one_cache
            assign cb_valid_o = mem_valid_i;
            assign cb_yumi_o   = mem_ready_i & cb_valid_i;
            assign cache_id     = '0;

        end else begin : gen_multi_cache
            // REVISIT MULTICORE INTEGRATION
            logic [num_cache_size_lp-1:0] new_cache_id, cache_id_r, cache_id_n;
            
            logic [num_caches_p-1:0] [num_cache_size_lp-1:0] lru_priority;
            logic [num_caches_p-1:0] [num_caches_p-1:0] onehot_lru;
            logic [num_caches_p-1:0] [num_caches_p-1:0] onehot_lru_masked;
            logic [num_caches_p-1:0] prior_eq_gnt_prior, prior_reqs, req_yumi;
            logic [num_cache_size_lp-1:0] new_gnt_prior;

            // REVISIT (11/4, implement pLRU for fair arb)
            logic [num_caches_p-1:0] yumi_inactive, yumi_active, eq_cache_id_r;
            
            priority_lru #(
                .size_p(num_cache_size_lp)
            ) u_priority_lru (
                .clk_i, 
                .nreset_i,
                .valid_i(tx_begin),
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
                    onehot_lru_masked[c] = {num_caches_p{cb_valid_i[c]}} & onehot_lru[c];
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
                    new_cache_id = new_cache_id | ({num_cache_size_lp{prior_eq_gnt_prior[c]}} & num_cache_size_lp'(c));
                    yumi_inactive[c] = prior_eq_gnt_prior[c] & |cb_valid_i;
                end

                // Generate yumi_active
                for (int c = 0; c < num_caches_p; c++) begin
                    eq_cache_id_r[c] = cache_id_r == num_cache_size_lp'(c);
                    yumi_active[c]   = cb_valid_i[c] & ~mem_ld_r & eq_cache_id_r[c];

                    cb_yumi_o[c]  = mem_ready_i & (tx_inactive? yumi_inactive[c]: yumi_active[c]);
                    cb_valid_o[c] = eq_cache_id_r[c] & mem_valid_i;
                end
            end

            assign cache_id_n = tx_begin? new_cache_id: cache_id_r;
            assign cache_id = tx_inactive? new_cache_id: cache_id_r;

            always_ff @(posedge clk_i) begin
                if (~nreset_i)
                    cache_id_r <= '0;
                else
                    cache_id_r <= cache_id_n;
            end
        end
    endgenerate
    
endmodule
