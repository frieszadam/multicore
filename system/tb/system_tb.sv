`include "cache.vh"
`define tohost 32'h80001000
`define tohost_exit 32'h800026f4

module system_tb ();

    // Dump waveform to fsdb file 
    initial begin
        $fsdbDumpfile("waveform.fsdb");
        $fsdbDumpvars();
    end

    localparam core_clk_freq_p = 125; // MHz
    localparam core_clk_period_p = 1_000_000 / core_clk_freq_p; // ps
    localparam ring_width_lp = 70;
    localparam rom_addr_width_lp = 15;
    
    localparam num_cores_lp = 1;
    localparam block_width_lp = 16;
    localparam sets_lp = 64;
    localparam ways_lp = 2;
    localparam dma_data_width_lp = 4;

    localparam main_memory_delay_lp = 5;
    localparam mem_addr_width_lp = 20;
    localparam instr_file_lp  = "../../tb/instruction_memory.hex";
    localparam data_file_lp  = "../../tb/data_memory.hex";

    localparam core_cache_pkt_width_lp = `core_cache_pkt_width;
    localparam cache_bus_pkt_width_lp  = `cache_bus_pkt_width(dma_data_width_lp);
    localparam block_state_width_lp    = $bits(block_state_t);

    logic clk, reset, nreset;
    assign nreset = ~reset;
    
    logic data_ready, data_valid_lo, data_valid_li, data_we;
    logic [31:0] data_addr;
    logic [(dma_data_width_lp*32)-1:0] data_rdata, data_wdata;

    logic [num_cores_lp-1:0] instr_ready, instr_valid_lo, instr_valid_li;
    logic [num_cores_lp-1:0] [31:0] instr_addr;
    logic [num_cores_lp-1:0] [31:0] instr_rdata;

    bsg_nonsynth_clock_gen #(
        .cycle_time_p(core_clk_period_p)
    ) u_clock_gen (
        .o(clk)
    );

    bsg_nonsynth_reset_gen #(
        .num_clocks_p(1)
        ,.reset_cycles_lo_p(5)
        ,.reset_cycles_hi_p(10)
    ) u_reset_gen (
        .clk_i(clk)
        ,.async_reset_o(reset)
    );

    system_top #(
        .num_cores_p(num_cores_lp),
        .block_width_p(block_width_lp),
        .sets_p(sets_lp),
        .ways_p(ways_lp),
        .dma_data_width_p(dma_data_width_lp)
    ) u_dut (
        .clk_i(clk),
        .nreset_i(nreset),

        // Data Memory Interface
        .data_ready_i(data_ready),
        .data_valid_o(data_valid_lo),
        .data_valid_i(data_valid_li),

        .data_we_o(data_we),
        .data_addr_o(data_addr),
        .data_wdata_o(data_wdata),
        .data_rdata_i(data_rdata),

        // Instr Memory Interface
        .instr_ready_i(instr_ready),
        .instr_valid_o(instr_valid_lo),
        .instr_addr_o(instr_addr),

        .instr_valid_i(instr_valid_li),
        .instr_rdata_i(instr_rdata)
    );

    memory_model #(
        .words_p(2**mem_addr_width_lp),
        .width_words_p(dma_data_width_lp),
        .delay_p(main_memory_delay_lp),
        .init_file_p(data_file_lp)
    ) u_data_mem (
        .clk_i(clk),
        .nreset_i(nreset),

        // Memory to Bus
        .valid_i(data_valid_lo),
        .ready_o(data_ready),
        .valid_o(data_valid_li),

        .we_i(data_we),
        .addr_i(data_addr - `INSTR_OFFSET),
        .wdata_i(data_wdata),
        .data_o(data_rdata)
    );

    generate
        genvar c;
        for (c = 0; c < num_cores_lp; c++) begin : gen_instr_mem
            memory_model #(
                .words_p(2**mem_addr_width_lp),
                .width_words_p(1),
                .delay_p(1),
                .init_file_p(instr_file_lp)
            ) u_instr_mem (
                .clk_i(clk),
                .nreset_i(nreset),

                // Memory to Bus
                .valid_i(instr_valid_lo[c]),
                .ready_o(instr_ready[c]),
                .valid_o(instr_valid_li[c]),

                .addr_i(instr_addr[c] - `INSTR_OFFSET),
                .data_o(instr_rdata[c]),

                // Unused for Instr Memory
                .we_i('0),
                .wdata_i('0)
            );
        end
    endgenerate
 
    logic program_exit, tohost_addr_write;
    logic [31:0] return_value_r, return_value_n;

    assign program_exit = instr_addr == `tohost_exit & instr_valid_lo;
    assign tohost_addr_write = u_dut.u_memsys.gen_cache_snoop_controller[0].u_cache.cc_valid_i &
                               u_dut.u_memsys.gen_cache_snoop_controller[0].u_cache.cc_pkt.we &
                               (u_dut.u_memsys.gen_cache_snoop_controller[0].u_cache.cc_pkt.addr == `tohost | 
                               u_dut.u_memsys.gen_cache_snoop_controller[0].u_cache.cc_pkt.addr == `tohost_exit);
    assign return_value_n = tohost_addr_write? u_dut.u_memsys.gen_cache_snoop_controller[0].u_cache.cc_pkt.wdata: return_value_r;
    
    always_ff @(posedge clk) begin
        if (~nreset) begin
            return_value_r <= '0;
        end else begin
            return_value_r <= return_value_n;
        end
    end

    logic rf_we;
    logic [4:0]  rf_waddr, rf_raddr0, rf_raddr1;
    logic [31:0] rf_wdata, rf_rdata0, rf_rdata1;

    assign rf_we     = u_dut.gen_core[0].u_core.u_core.register_file_wrapper_i.register_file_i.we_i[0];
    assign rf_wdata  = u_dut.gen_core[0].u_core.u_core.register_file_wrapper_i.register_file_i.wdata_i[0];

    assign rf_waddr  = u_dut.gen_core[0].u_core.u_core.register_file_wrapper_i.register_file_i.waddr_i[0];
    assign rf_raddr0 = u_dut.gen_core[0].u_core.u_core.register_file_wrapper_i.register_file_i.raddr_i[0];
    assign rf_raddr1 = u_dut.gen_core[0].u_core.u_core.register_file_wrapper_i.register_file_i.raddr_i[1];

    assign rf_rdata0 = u_dut.gen_core[0].u_core.u_core.register_file_wrapper_i.register_file_i.rdata_o[0];
    assign rf_rdata1 = u_dut.gen_core[0].u_core.u_core.register_file_wrapper_i.register_file_i.rdata_o[1];

    initial begin
        $display("[START] Starting Simulation");
        repeat(10) begin
            @(posedge clk);
        end

        // REVISIT (testing, set a memory address as test complete signal)
        wait(program_exit);
        if (return_value_r == '0)
            $display("[FINISH] Test Successful.");
        else
            $display("[FINISH] Test Failed.");
        $finish;
    end


endmodule
