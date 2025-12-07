`include "core.vh"
import cv32e40x_pkg::*;

module core_top #(
    parameter MHART_ID
)(
    input logic clk_i,
    input logic nreset_i,
    input logic fetch_enable_i,

    // Instruction memory interface
    output logic                          instr_req_o,
    input  logic                          instr_gnt_i,
    input  logic                          instr_rvalid_i,
    output logic [31:0]                   instr_addr_o,
    input  logic [31:0]                   instr_rdata_i,

    // Data memory interface
    output logic                          data_req_o,
    input  logic                          data_gnt_i,
    input  logic                          data_rvalid_i,
    output logic [31:0]                   data_addr_o,
    output logic [3:0]                    data_be_o,
    output logic                          data_we_o,
    output logic [31:0]                   data_wdata_o,
    output logic                          data_lr_sc_o,
    input  logic [31:0]                   data_rdata_i,
    input  logic                          data_err_i,
    input  logic                          data_exokay_i,

    output logic                          fencei_flush_req_o,
    input  logic                          fencei_flush_ack_i
);

    logic core_sleep, debug_havereset, debug_running, debug_halted, debug_pc_valid, data_dbg, instr_dbg;
    logic [1:0] data_memtype, instr_memtype; // holds [cacheable, bufferable] as defined by physical memory attributes
    logic [2:0] data_prot, instr_prot;
    logic [5:0] data_atop;
    logic [31:0] debug_pc;
    logic [63:0] mcycle;
    
    assign data_lr_sc_o = data_atop[5] & (data_atop[4:0] == `ATOP_LR | data_atop[4:0] == `ATOP_SC);

    cv32e40x_if_xif xif_compressed_if ();
    cv32e40x_if_xif xif_issue_if ();
    cv32e40x_if_xif xif_commit_if ();
    cv32e40x_if_xif xif_mem_if ();
    cv32e40x_if_xif xif_mem_result_if ();
    cv32e40x_if_xif xif_result_if ();

    //  xif_issue_if, xif_commit_if, xif_mem_if, xif_mem_result_if, xif_result_if;

    cv32e40x_core #(
        .LIB                        (            0 ),
        .RV32                       (        RV32I ),
        .A_EXT                      (       ZALRSC ),
        .B_EXT                      (       B_NONE ),
        .M_EXT                      (            M ),
        .X_EXT                      (            0 ),
        .X_NUM_RS                   (            2 ),
        .X_ID_WIDTH                 (            4 ),
        .X_MEM_WIDTH                (           32 ),
        .X_RFR_WIDTH                (           32 ),
        .X_RFW_WIDTH                (           32 ),
        .X_MISA                     (        32'h0 ),
        .X_ECS_XS                   (         2'b0 ),
        .DEBUG                      (            0 ),
        .DM_REGION_START            ( 32'hF0000000 ),
        .DM_REGION_END              ( 32'hF0003FFF ),
        .DBG_NUM_TRIGGERS           (            1 ),
        .NUM_MHPMCOUNTERS           (            1 ),
        .PMA_NUM_REGIONS            (            0 ), // REVISIT (confirm default behavior with PMA disabled)
        .PMA_CFG                    (              ),
        .CLIC                       (            0 ),
        .CLIC_ID_WIDTH              (            5 )
    ) u_core (
        // Clock and reset
        .clk_i                    (clk_i),
        .rst_ni                   (nreset_i),
        .scan_cg_en_i             (1'b0),

        // Configuration
        .boot_addr_i              ('0),
        .mtvec_addr_i             ('0),
        .dm_halt_addr_i           ('0),
        .dm_exception_addr_i      ('0),
        .mhartid_i                (MHART_ID),
        .mimpid_patch_i           ('0),

        // Instruction memory interface
        .instr_req_o              (instr_req_o),
        .instr_gnt_i              (instr_gnt_i),
        .instr_addr_o             (instr_addr_o),
        .instr_memtype_o          (instr_memtype),
        .instr_prot_o             (instr_prot),
        .instr_dbg_o              (instr_dbg),
        .instr_rvalid_i           (instr_rvalid_i),
        .instr_rdata_i            (instr_rdata_i),
        .instr_err_i              ('0),

        // Data memory interface
        .data_req_o               (data_req_o),
        .data_gnt_i               (data_gnt_i),
        .data_addr_o              (data_addr_o),
        .data_atop_o              (data_atop),
        .data_be_o                (data_be_o),
        .data_memtype_o           (data_memtype),
        .data_prot_o              (data_prot),
        .data_dbg_o               (data_dbg),
        .data_wdata_o             (data_wdata_o),
        .data_we_o                (data_we_o),
        .data_rvalid_i            (data_rvalid_i),
        .data_rdata_i             (data_rdata_i),
        .data_err_i               (data_err_i),
        .data_exokay_i            (data_exokay_i),

        // Cycle, Time
        .mcycle_o                 (mcycle),
        .time_i                   (0),

        // eXtension interface
        .xif_compressed_if        (xif_compressed_if),
        .xif_issue_if             (xif_issue_if),
        .xif_commit_if            (xif_commit_if),
        .xif_mem_if               (xif_mem_if),
        .xif_mem_result_if        (xif_mem_result_if),
        .xif_result_if            (xif_result_if),

        // Interrupt interface
        .irq_i                    ('0),

        .clic_irq_i               ('0),
        .clic_irq_id_i            ('0),
        .clic_irq_level_i         ('0),
        .clic_irq_priv_i          ('0),
        .clic_irq_shv_i           ('0),

        // Fencei flush handshake
        .fencei_flush_req_o       (fencei_flush_req_o),
        .fencei_flush_ack_i       (fencei_flush_ack_i),

        // Debug interface
        .debug_req_i              ('0),
        .debug_havereset_o        (debug_havereset),
        .debug_running_o          (debug_running),
        .debug_halted_o           (debug_halted),
        .debug_pc_valid_o         (debug_pc_valid),
        .debug_pc_o               (debug_pc),

        // Special control signals
        .fetch_enable_i           (fetch_enable_i),
        .core_sleep_o             (core_sleep),
        .wu_wfe_i                 ('0)
    );

endmodule
