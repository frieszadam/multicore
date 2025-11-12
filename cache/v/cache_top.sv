`include "v/cache.vh"

// Instantiate the cache with the desired parameters for synthesis
`define block_width_p 16
`define sets_p 64
`define ways_p 4
`define dma_data_width_p 2

module cache_top (
    input  logic clk_i,
    input  logic nreset_i,

    // Core Cache Interface
    input  logic                               cc_valid_i,
    output logic                               cc_ready_o,
    input  logic [`core_cache_pkt_width-1:0] cc_pkt_i,

    output logic            cc_valid_o,
    output logic [31:0]     cc_rdata_o,

    // Cache Bus Interface
    output logic                              cb_valid_o,
    input  logic                              cb_yumi_i,
    output logic [`cache_bus_pkt_width(`dma_data_width_p)-1:0] cb_pkt_o,

    input  logic                           cb_valid_i,
    input  logic [(`dma_data_width_p*32)-1:0] cb_data_i
);

    cache #(
        .block_width_p(`block_width_p),       // words per block
        .sets_p(`sets_p),                     // number of sets
        .ways_p(`ways_p),                     // number of ways
        .dma_data_width_p(`dma_data_width_p)  // bus transfer size in words
    ) u_cache (
        .clk_i,
        .nreset_i,

        // Core Cache Interface
        .cc_valid_i,
        .cc_ready_o,
        .cc_pkt_i,

        .cc_valid_o,
        .cc_rdata_o,

        // Cache Bus Interface
        .cb_valid_o,
        .cb_yumi_i,
        .cb_pkt_o,

        .cb_valid_i,
        .cb_data_i
    );

endmodule

