`include "cache.vh"

module system_top #(
    parameter num_cores_p,
    parameter block_width_p = 16,
    parameter sets_p = 64,
    parameter ways_p = 2,
    parameter dma_data_width_p = 4
) (
    input logic clk_i,
    input logic nreset_i,

    // Data Memory Interface
    input  logic                             data_ready_i,
    output logic                             data_valid_o,

    input  logic                             data_valid_i,
    input  logic [(dma_data_width_p*32)-1:0] data_rdata_i,

    output logic                             data_we_o,
    output logic [31:0]                      data_addr_o,
    output logic [(dma_data_width_p*32)-1:0] data_wdata_o,

    // Instr Memory Interface
    input  logic [num_cores_p-1:0]          instr_ready_i,
    output logic [num_cores_p-1:0]          instr_valid_o,
    output logic [num_cores_p-1:0] [31:0]   instr_addr_o,

    input  logic [num_cores_p-1:0]          instr_valid_i,
    input  logic [num_cores_p-1:0] [31:0]   instr_rdata_i
);

    // Core Cache Interface    
    logic [num_cores_p-1:0] cc_req, cc_ready, cc_we, cc_lr_sc;
    logic [num_cores_p-1:0] [3:0] cc_be;
    logic [num_cores_p-1:0] [31:0] cc_addr;
    logic [num_cores_p-1:0] [(32*dma_data_width_p)-1:0] cc_wdata;
    logic [num_cores_p-1:0] [`core_cache_pkt_width-1:0] cc_pkt;

    logic [num_cores_p-1:0] cc_valid;
    logic [num_cores_p-1:0] [31:0] cc_rdata;
    core_cache_pkt_t [num_cores_p-1:0] cc_pkt_struct;

    // REVISIT (implement atomic related signals)
    logic [num_cores_p-1:0] cc_err, cc_exokay, cc_flush_req, cc_flush_ack;
    assign cc_err = '0;
    assign cc_exokay = '0;
    assign cc_flush_ack = cc_flush_req;

    memsys_top #(
        .num_caches_p(num_cores_p),
        .block_width_p(block_width_p),
        .sets_p(sets_p),
        .ways_p(ways_p),
        .dma_data_width_p(dma_data_width_p)
    ) u_dut (
        .clk_i(clk_i),
        .nreset_i(nreset_i),

        // Core Cache Interface
        .cc_valid_i(cc_req),
        .cc_ready_o(cc_ready),
        .cc_pkt_i  (cc_pkt),

        .cc_valid_o(cc_valid),
        .cc_rdata_o(cc_rdata),

        // Main Memory Interface
        .mem_ready_i(data_ready_i),
        .mem_valid_o(data_valid_o),

        .mem_valid_i(data_valid_i),
        .mem_data_i (data_rdata_i),

        .mem_we_o   (data_we_o),
        .mem_addr_o (data_addr_o),
        .mem_wdata_o(data_wdata_o)
    );

    generate
        genvar c;
        for (c = 0; c < num_cores_p; c++) begin : gen_core

            core_top #(
                .MHART_ID(c)
            ) u_core (
                .clk_i,
                .nreset_i,
                .fetch_enable_i(1'b1),

                // Instruction memory interface
                .instr_req_o(instr_valid_o[c]),
                .instr_gnt_i(instr_ready_i[c] & instr_valid_o[c]),
                .instr_rvalid_i(instr_valid_i[c]),
                .instr_addr_o(instr_addr_o[c]),
                .instr_rdata_i(instr_rdata_i[c]),

                // Data memory interface
                .data_req_o   (cc_req[c]),
                .data_gnt_i   (cc_req[c] & cc_ready[c]),
                .data_rvalid_i(cc_valid[c]),
                .data_addr_o  (cc_addr[c]),
                .data_be_o    (cc_be[c]),
                .data_we_o    (cc_we[c]),
                .data_wdata_o (cc_wdata[c]),
                .data_lr_sc_o (cc_lr_sc[c]),
                .data_rdata_i (cc_rdata[c]),
                .data_err_i   (cc_err[c]),
                .data_exokay_i(cc_exokay[c]),

                .fencei_flush_req_o(cc_flush_req[c]),
                .fencei_flush_ack_i(cc_flush_ack[c])
            );

            assign cc_pkt_struct[c].be    = cc_be[c];
            assign cc_pkt_struct[c].we    = cc_we[c];
            assign cc_pkt_struct[c].lr_sc = cc_lr_sc[c];
            assign cc_pkt_struct[c].addr  = cc_addr[c];
            assign cc_pkt_struct[c].wdata = cc_wdata[c];

            assign cc_pkt[c] = core_cache_pkt_t'(cc_pkt_struct[c]);
        end
    endgenerate

endmodule

