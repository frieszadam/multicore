`include "../src/cache.svh"

module cache_tb ();

    localparam core_clk_freq_p = 125; // MHz
    localparam core_clk_period_p = 1_000_000 / core_clk_freq_p; // ps

    logic clk, nreset;

    // Core Cache Interface
    logic cc_valid_li, cc_ready_lo;
    core_cache_pkt_t cc_pkt_li;

    logic cc_valid_lo, cc_yumi_li;
    logic [31:0] cc_rdata_lo;

    // Cache Bus Interface
    logic cb_valid_lo, cb_yumi_li;
    cache_bus_pkt_t cb_pkt_lo;

    logic cb_valid_li;
    logic [`DMA_DATA_WIDTH] cb_data_li;

    logic mem_done, mem_req, mem_we;
    logic [31:0] mem_addr;
    logic [`DMA_DATA_WIDTH] mem_rdata, mem_wdata;

    cache #(
        block_size_p,
        sets_p,
        ways_p,
        dma_data_width_p
    ) dut (
        .clk_i(clk),
        .nreset_i(nreset),

        // Core Cache Interface
        .cc_valid_i(cc_valid_li),
        .cc_ready_o(cc_ready_lo),
        .cc_pkt_i(cc_pkt_li),

        .cc_valid_o(cc_valid_lo),
        .cc_yumi_i(cc_yumi_li),
        .cc_rdata_o(cc_rdata_lo),

        // Cache Bus Interface
        .cb_valid_o(cb_valid_lo),
        .cb_yumi_i(cb_yumi_li),
        .cb_pkt_o(cb_pkt_lo),

        .cb_valid_i(cb_valid_li),
        .cb_data_i(cb_data_li)
    );

    bsg_nonsynth_clock_gen #(
        .cycle_time_p(core_clk_period_p)
    ) clock_gen (
        .o(clk)
    );

    bsg_nonsynth_reset_gen #(
        .num_clocks_p(1)
        ,.reset_cycles_lo_p(1)
        ,.reset_cycles_hi_p(10)
    ) reset_gen (
        .clk_i(clk)
        ,.async_reset_o(~nreset)
    );

    main_memory #(
        .els_p(),
        .dma_data_width_p,
        .init_file_p()
    ) main_mem (
        .clk_i(clk),
        .nreset_i(nreset),

        // Memory to Bus
        .mem_valid_i(mem_req),
        .mem_ready_o(mem_ready),
        .mem_valid_o(mem_done),

        .mem_we_i(mem_we),
        .mem_addr_i(mem_addr),
        .mem_wdata_i(mem_wdata),
        .mem_data_o(mem_rdata)
    );

    bus (
        .num_caches_p,
        .block_size_p,
        .dma_data_width_p
    ) cache_mem_bus (
        .clk_i(clk),
        .nreset_i(nreset),

        // Cache to Bus
        .cb_valid_i(cb_valid_lo),
        .cb_yumi_o(cb_yumi_li),
        .cb_pkt_i(cb_pkt_lo),

        // Memory to Bus
        .mem_ready_i(mem_ready),
        .mem_valid_o(mem_req),

        .mem_valid_i(mem_done),
        .mem_data_i(mem_rdata),

        .mem_we_o(mem_we),
        .mem_addr_o(mem_addr),
        .mem_wdata_o(mem_wdata),

        // Bus to Cache
        .cb_valid_o(cb_valid_li),
        .cb_data_o(cb_data_li)
    );


endmodule

