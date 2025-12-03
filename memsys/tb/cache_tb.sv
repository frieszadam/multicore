`include "v/cache.vh"

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
    localparam sets_lp = 64;
    localparam ways_lp = 2;
    localparam dma_data_width_lp = 4;
    localparam num_caches_lp = 2;

    localparam mem_addr_width_lp = 11;
    localparam init_file_lp  = "../../tb/dma_init.mem";

    localparam core_cache_pkt_width_lp = `core_cache_pkt_width;
    localparam cache_bus_pkt_width_lp  = `cache_bus_pkt_width(dma_data_width_lp);
    localparam block_state_width_lp    = $bits(block_state_t);

    logic clk, reset, nreset;
    assign nreset = ~reset;

    // Core Cache Interface
    logic [num_caches_lp-1:0] cc_valid_li, cc_ready_lo;
    logic [num_caches_lp-1:0] [core_cache_pkt_width_lp-1:0] cc_pkt_li;

    logic [num_caches_lp-1:0] cc_valid_lo, cc_yumi_li;
    logic [num_caches_lp-1:0] [31:0] cc_rdata_lo;

    // Cache Snoop Controller Interface
    logic [num_caches_lp-1:0] sc_ready, sc_block_hit, sc_rd_tag_state, sc_rdata_en;
    logic [num_caches_lp-1:0] sc_set_state, sc_state_invalid;
    logic [num_caches_lp-1:0] [block_state_width_lp-1:0] sc_block_state;
    logic [num_caches_lp-1:0] [(dma_data_width_lp*32)-1:0] sc_rdata;
    logic [num_caches_lp-1:0] [31:0] sc_raddr;

    // Snoop Controller Bus Interface
    logic [num_caches_lp-1:0] sb_wait, sb_valid_li, sb_valid_lo, sb_hit;
    logic [num_caches_lp-1:0] [(dma_data_width_lp*32)-1:0] sb_data;
    
    logic sb_last_rx, sb_tx_begin;
    logic [cache_bus_pkt_width_lp-1:0] sb_bus_pkt;

    logic mem_done, mem_ready, mem_req, mem_we;
    logic [31:0] mem_addr;
    logic [(dma_data_width_lp*32)-1:0] mem_rdata, mem_wdata;

    logic [num_caches_lp-1:0] [ring_width_lp+4-1:0] core_trace_rom_data;
    logic [num_caches_lp-1:0] [ring_width_lp-1:0] core_tr_data_lo;
    logic [num_caches_lp-1:0] [rom_addr_width_lp-1:0] core_trace_rom_addr;
    logic [num_caches_lp-1:0] core_done, core_ready_lo, trace_replay_yumi_li;
    logic [num_caches_lp-1:0] [ring_width_lp-1:0] trace_replay_data_li;

    bsg_nonsynth_clock_gen #(
        .cycle_time_p(core_clk_period_p)
    ) u_clock_gen (
        .o(clk)
    );

    bsg_nonsynth_reset_gen #(
        .num_clocks_p(1)
        ,.reset_cycles_lo_p(0)
        ,.reset_cycles_hi_p(10)
    ) u_reset_gen (
        .clk_i(clk)
        ,.async_reset_o(reset)
    );

    generate
        genvar c;
        for (c = 0; c < num_caches_lp; c++) begin : gen_cache_core
            assign cc_pkt_li[c] = core_tr_data_lo[c][core_cache_pkt_width_lp-1:0];
            assign cc_yumi_li[c] = core_ready_lo[c] & cc_valid_lo[c];

            assign trace_replay_data_li[c] = {37'b0, cc_rdata_lo[c]};
            assign trace_replay_yumi_li[c] = cc_ready_lo[c] & cc_valid_li[c];
            bsg_fsb_node_trace_replay #(
                .ring_width_p(ring_width_lp)
                ,.rom_addr_width_p(rom_addr_width_lp)
            ) u_core_intf_trace_replay (
                .clk_i(clk)
                ,.reset_i(reset)
                ,.en_i(1'b1)

                ,.v_i(cc_valid_lo[c])
                ,.data_i(trace_replay_data_li[c])
                ,.ready_o(core_ready_lo[c])

                ,.v_o(cc_valid_li[c])
                ,.data_o(core_tr_data_lo[c])
                ,.yumi_i(trace_replay_yumi_li[c])

                ,.rom_addr_o(core_trace_rom_addr[c])
                ,.rom_data_i(core_trace_rom_data[c])

                ,.done_o(core_done[c])
                ,.error_o()
            ); 

            case(c)
                0: begin : gen_rom0
                    bsg_core_intf_trace_rom0 #(
                        .width_p(ring_width_lp+4)
                        ,.addr_width_p(rom_addr_width_lp)
                    ) u_core_intf_trace_rom (
                        .addr_i(core_trace_rom_addr[c])
                        ,.data_o(core_trace_rom_data[c])
                    );
                end
                1: begin : gen_rom1
                    bsg_core_intf_trace_rom1 #(
                        .width_p(ring_width_lp+4)
                        ,.addr_width_p(rom_addr_width_lp)
                    ) u_core_intf_trace_rom (
                        .addr_i(core_trace_rom_addr[c])
                        ,.data_o(core_trace_rom_data[c])
                    );
                end
                2: begin : gen_rom2
                    bsg_core_intf_trace_rom2 #(
                        .width_p(ring_width_lp+4)
                        ,.addr_width_p(rom_addr_width_lp)
                    ) u_core_intf_trace_rom (
                        .addr_i(core_trace_rom_addr[c])
                        ,.data_o(core_trace_rom_data[c])
                    );
                end
                3: begin : gen_rom3
                    bsg_core_intf_trace_rom3 #(
                        .width_p(ring_width_lp+4)
                        ,.addr_width_p(rom_addr_width_lp)
                    ) u_core_intf_trace_rom (
                        .addr_i(core_trace_rom_addr[c])
                        ,.data_o(core_trace_rom_data[c])
                    );
                end
                4: begin : gen_rom4
                    bsg_core_intf_trace_rom4 #(
                        .width_p(ring_width_lp+4)
                        ,.addr_width_p(rom_addr_width_lp)
                    ) u_core_intf_trace_rom (
                        .addr_i(core_trace_rom_addr[c])
                        ,.data_o(core_trace_rom_data[c])
                    );
                end
                5: begin : gen_rom5
                    bsg_core_intf_trace_rom5 #(
                        .width_p(ring_width_lp+4)
                        ,.addr_width_p(rom_addr_width_lp)
                    ) u_core_intf_trace_rom (
                        .addr_i(core_trace_rom_addr[c])
                        ,.data_o(core_trace_rom_data[c])
                    );
                end
                6: begin : gen_rom6
                    bsg_core_intf_trace_rom6 #(
                        .width_p(ring_width_lp+4)
                        ,.addr_width_p(rom_addr_width_lp)
                    ) u_core_intf_trace_rom (
                        .addr_i(core_trace_rom_addr[c])
                        ,.data_o(core_trace_rom_data[c])
                    );
                end
                7: begin : gen_rom7
                    bsg_core_intf_trace_rom7 #(
                        .width_p(ring_width_lp+4)
                        ,.addr_width_p(rom_addr_width_lp)
                    ) u_core_intf_trace_rom (
                        .addr_i(core_trace_rom_addr[c])
                        ,.data_o(core_trace_rom_data[c])
                    );
                end
                default: ;
            endcase
        end
    endgenerate

    memsys_top #(
        .num_caches_p(num_caches_lp),
        .block_width_p(block_width_lp),
        .sets_p(sets_lp),
        .ways_p(ways_lp),
        .dma_data_width_p(dma_data_width_lp)
    ) u_dut (
        .clk_i(clk),
        .nreset_i(nreset),

        // Core Cache Interface
        .cc_valid_i(cc_valid_li),
        .cc_ready_o(cc_ready_lo),
        .cc_pkt_i(cc_pkt_li),

        .cc_valid_o(cc_valid_lo),
        .cc_rdata_o(cc_rdata_lo),

        // Main Memory Interface
        .mem_ready_i(mem_ready),
        .mem_valid_o(mem_req),

        .mem_valid_i(mem_done),
        .mem_data_i(mem_rdata),

        .mem_we_o(mem_we),
        .mem_addr_o(mem_addr),
        .mem_wdata_o(mem_wdata)
    );

    main_memory #(
        .els_p(2**mem_addr_width_lp),
        .dma_data_width_p(dma_data_width_lp),
        .block_width_p(block_width_lp),
        .init_file_p(init_file_lp)
    ) u_main_mem (
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

    // Assertions
    // s_ready and s_idle == '0

    `ifndef DISABLE_TESTING
        generate
            logic [num_caches_lp-1:0] sc_idle_r, cache_idle_r, cache_idle_n;
            for (genvar i = 0; i < num_caches_lp; i++) begin
                assign sc_idle_r[i] = u_dut.gen_cache_snoop_controller[i].u_snoop_controller.control_state_r == '0;

                assign cache_idle_r[i] = u_dut.gen_cache_snoop_controller[i].u_cache.cache_state_r == '0;
                assign cache_idle_n[i] = u_dut.gen_cache_snoop_controller[i].u_cache.cache_state_n == '0;
            end

            if (num_caches_lp != 1) begin
                logic control_state_active;
                always_comb begin
                    control_state_active = 1'b0;
                    for (int c = 0; c < num_caches_lp; c++) begin
                        control_state_active = control_state_active | ~sc_idle_r[c];
                    end
                end

                property p_bus_ready_control_state_idle;
                    @(posedge clk) if (nreset)
                        u_dut.u_bus.gen_multi_cache.bus_state_r == '0 |-> ~control_state_active;
                endproperty

                a_bus_ready_control_state_idle: assert property (p_bus_ready_control_state_idle)
                    else $error("Assertion failure: All snoop controller must be idle when bus is idle.");
            end
        endgenerate
    `endif 

  initial begin
    $display("[START] Starting Simulation");
    repeat(11) begin
      @(posedge clk);
    end

    wait(&core_done);
    $display("[FINISH] Test Successful.");
    $finish;
  end


endmodule

