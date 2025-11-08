`include "v/cache.svh"

module cache_tb ();

    // Dump waveform to fsdb file 
    initial begin
        $fsdbDumpfile("waveform.fsdb");
        $fsdbDumpvars();
    end

    localparam core_clk_freq_p = 125; // MHz
    localparam core_clk_period_p = 1_000_000 / core_clk_freq_p; // ps
    localparam ring_width_lp = 69;
    localparam rom_addr_width_lp = 15;
    
    localparam block_width_lp = 16;
    localparam sets_lp = 16;
    localparam ways_lp = 8;
    localparam dma_data_width_lp = 2;

    localparam mem_addr_width_lp = 11;
    localparam num_caches_lp = 1;
    localparam init_file_lp  = "../../tb/dma_init.mem";

    localparam core_cache_pkt_width_lp = `core_cache_pkt_width;
    localparam cache_bus_pkt_width_lp  = `cache_bus_pkt_width(dma_data_width_lp);
    logic clk, reset, nreset;

    // Core Cache Interface
    logic cc_valid_li, cc_ready_lo;
    logic [core_cache_pkt_width_lp-1:0] cc_pkt_li;

    logic cc_valid_lo, cc_yumi_li;
    logic [31:0] cc_rdata_lo;

    // Cache Bus Interface
    logic cb_valid_lo, cb_yumi_li;
    logic [cache_bus_pkt_width_lp-1:0] cb_pkt_lo;

    logic cb_valid_li;
    logic [(dma_data_width_lp*32)-1:0] cb_data_li;

    logic mem_done, mem_ready, mem_req, mem_we;
    logic [31:0] mem_addr;
    logic [(dma_data_width_lp*32)-1:0] mem_rdata, mem_wdata;

    cache #(
        .block_width_p(block_width_lp),
        .sets_p(sets_lp),
        .ways_p(ways_lp),
        .dma_data_width_p(dma_data_width_lp)
    ) dut (
        .clk_i(clk),
        .nreset_i(nreset),

        // Core Cache Interface
        .cc_valid_i(cc_valid_li),
        .cc_ready_o(cc_ready_lo),
        .cc_pkt_i(cc_pkt_li),

        .cc_valid_o(cc_valid_lo),
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
        ,.reset_cycles_lo_p(0)
        ,.reset_cycles_hi_p(10)
    ) reset_gen (
        .clk_i(clk)
        ,.async_reset_o(reset)
    );

    assign nreset = ~reset;

    main_memory #(
        .els_p(2**mem_addr_width_lp),
        .dma_data_width_p(dma_data_width_lp),
        .block_width_p(block_width_lp),
        .init_file_p(init_file_lp)
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

    bus #(
        .num_caches_p(num_caches_lp),
        .block_width_p(block_width_lp),
        .dma_data_width_p(dma_data_width_lp)
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

    logic [ring_width_lp+4-1:0] core_trace_rom_data;
    logic [ring_width_lp-1:0] core_tr_data_lo;
    logic [rom_addr_width_lp-1:0] core_trace_rom_addr;
    logic core_done, core_ready_lo;

    assign cc_pkt_li = core_tr_data_lo[core_cache_pkt_width_lp-1:0];
    assign cc_yumi_li = core_ready_lo & cc_valid_lo;

    logic [ring_width_lp-1:0] trace_replay_data_li;
    assign trace_replay_data_li = {37'b0, cc_rdata_lo};
    bsg_fsb_node_trace_replay #(
        .ring_width_p(ring_width_lp)
        ,.rom_addr_width_p(rom_addr_width_lp)
    ) core_intf_trace_replay (
        .clk_i(clk)
        ,.reset_i(reset)
        ,.en_i(1'b1)

        ,.v_i(cc_valid_lo)
        ,.data_i(trace_replay_data_li)
        ,.ready_o(core_ready_lo)

        ,.v_o(cc_valid_li)
        ,.data_o(core_tr_data_lo)
        ,.yumi_i(cc_ready_lo & cc_valid_li)

        ,.rom_addr_o(core_trace_rom_addr)
        ,.rom_data_i(core_trace_rom_data)

        ,.done_o(core_done)
        ,.error_o()
    ); 

    bsg_core_intf_trace_rom #(
        .width_p(ring_width_lp+4)
        ,.addr_width_p(rom_addr_width_lp)
    ) core_intf_trace_rom (
        .addr_i(core_trace_rom_addr)
        ,.data_o(core_trace_rom_data)
    );

  initial begin
    $display("[START] Starting Simulation");
    repeat(11) begin
      @(posedge clk);
    end

    wait(core_done);
    $display("[FINISH] Test Successful.");
    $finish;
  end


endmodule

