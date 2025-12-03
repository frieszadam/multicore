`include "v/cache.vh"

module memsys_top #(
    parameter num_caches_p = 2,
    parameter block_width_p = 16,    // words per block
    parameter sets_p = 64,           // number of sets
    parameter ways_p = 2,            // number of ways
    parameter dma_data_width_p = 1,  // bus transfer size in words

    localparam core_cache_pkt_width_lp = `core_cache_pkt_width,
    localparam cache_bus_pkt_width_lp  = `cache_bus_pkt_width(dma_data_width_p),
    localparam block_state_width_lp    = $bits(block_state_t)
)(
    input  logic clk_i,
    input  logic nreset_i,

    // Core Cache Interface
    input  logic [num_caches_p-1:0]                               cc_valid_i,
    output logic [num_caches_p-1:0]                               cc_ready_o,
    input  logic [num_caches_p-1:0] [core_cache_pkt_width_lp-1:0] cc_pkt_i,

    output logic [num_caches_p-1:0]        cc_valid_o,
    output logic [num_caches_p-1:0] [31:0] cc_rdata_o,

    // Main Memory Interface
    input  logic mem_ready_i,
    output logic mem_valid_o,

    input  logic                             mem_valid_i,
    input  logic [(dma_data_width_p*32)-1:0] mem_data_i,

    output logic                   mem_we_o,
    output logic [31:0]            mem_addr_o,
    output logic [(dma_data_width_p*32)-1:0] mem_wdata_o
);
    
    // Cache Bus Interface
    logic cb_ld_ex;
    logic [num_caches_p-1:0] cb_valid_lo, cb_yumi_li;
    logic [num_caches_p-1:0] [cache_bus_pkt_width_lp-1:0] cb_pkt_lo;

    logic [num_caches_p-1:0] cb_valid_li;
    logic [(dma_data_width_p*32)-1:0] cb_data_li;

    // Cache Snoop Controller Interface
    logic [num_caches_p-1:0] sc_ready, sc_block_hit, sc_rd_tag_state, sc_rdata_en;
    logic [num_caches_p-1:0] sc_set_state, sc_state_invalid;
    logic [num_caches_p-1:0] [block_state_width_lp-1:0] sc_block_state;
    logic [num_caches_p-1:0] [(dma_data_width_p*32)-1:0] sc_rdata;
    logic [num_caches_p-1:0] [31:0] sc_raddr;

    // Snoop Controller Bus Interface
    logic [num_caches_p-1:0] sb_wait, sb_valid_li, sb_valid_lo, sb_hit;
    logic [num_caches_p-1:0] [(dma_data_width_p*32)-1:0] sb_data;
    
    logic sb_last_rx, sb_tx_begin;
    logic [cache_bus_pkt_width_lp-1:0] sb_bus_pkt;

    generate
        genvar c;
        for (c = 0; c < num_caches_p; c++) begin : gen_cache_snoop_controller

            cache #(
                .block_width_p(block_width_p),
                .sets_p(sets_p),
                .ways_p(ways_p),
                .dma_data_width_p(dma_data_width_p)
            ) u_cache (
                .clk_i(clk_i),
                .nreset_i(nreset_i),

                // Core Cache Interface
                .cc_valid_i(cc_valid_i[c]),
                .cc_ready_o(cc_ready_o[c]),
                .cc_pkt_i(cc_pkt_i[c]),

                .cc_valid_o(cc_valid_o[c]),
                .cc_rdata_o(cc_rdata_o[c]),

                // Cache Bus Interface
                .cb_valid_o(cb_valid_lo[c]),
                .cb_yumi_i(cb_yumi_li[c]),
                .cb_pkt_o(cb_pkt_lo[c]),

                .cb_valid_i(cb_valid_li[c]),
                .cb_ld_ex_i(cb_ld_ex),
                .cb_data_i(cb_data_li),

                .sc_rd_tag_state_i(sc_rd_tag_state[c]),
                .sc_rdata_en_i(sc_rdata_en[c]),
                .sc_raddr_i(sc_raddr[c]),
                .sc_set_state_i(sc_set_state[c]),
                .sc_state_invalid_i(sc_state_invalid[c]),

                .sc_ready_o(sc_ready[c]),
                .sc_block_hit_o(sc_block_hit[c]),
                .sc_block_state_o(sc_block_state[c]),
                .sc_rdata_o(sc_rdata[c])
            );

            snoop_controller #(
                .dma_data_width_p(dma_data_width_p)
            ) u_snoop_controller (
                .clk_i(clk_i),
                .nreset_i(nreset_i),

                .sc_ready_i(sc_ready[c]),
                .sc_block_hit_i(sc_block_hit[c]),
                .sc_block_state_i(sc_block_state[c]),
                .sc_rdata_i(sc_rdata[c]),

                .sc_rd_tag_state_o(sc_rd_tag_state[c]),
                .sc_rdata_en_o(sc_rdata_en[c]),
                .sc_raddr_o(sc_raddr[c]),
                .sc_set_state_o(sc_set_state[c]),
                .sc_state_invalid_o(sc_state_invalid[c]),

                .sb_valid_i(sb_valid_li[c]),
                .sb_last_rx_i(sb_last_rx),
                .sb_tx_begin_i(sb_tx_begin),
                .sb_bus_pkt_i(sb_bus_pkt),

                .sb_wait_o(sb_wait[c]),
                .sb_hit_o(sb_hit[c]),
                .sb_valid_o(sb_valid_lo[c]),
                .sb_data_o(sb_data[c])
            );

        end
    endgenerate

    bus #(
        .num_caches_p(num_caches_p),
        .block_width_p(block_width_p),
        .dma_data_width_p(dma_data_width_p)
    ) u_bus (
        .clk_i(clk_i),
        .nreset_i(nreset_i),

        // Cache to Bus
        .cb_valid_i(cb_valid_lo),
        .cb_yumi_o(cb_yumi_li),
        .cb_pkt_i(cb_pkt_lo),

        // Memory to Bus
        .mem_ready_i(mem_ready_i),
        .mem_valid_o(mem_valid_o),

        .mem_valid_i(mem_valid_i),
        .mem_data_i(mem_data_i),

        .mem_we_o(mem_we_o),
        .mem_addr_o(mem_addr_o),
        .mem_wdata_o(mem_wdata_o),

        // Bus to Cache
        .cb_valid_o(cb_valid_li),
        .cb_data_o(cb_data_li),
        .cb_ld_ex_o(cb_ld_ex),

        .sb_wait_i(sb_wait),
        .sb_hit_i(sb_hit),
        .sb_valid_i(sb_valid_lo),
        .sb_data_i(sb_data),

        .sb_valid_o(sb_valid_li),
        .sb_last_rx_o(sb_last_rx),
        .sb_tx_begin_o(sb_tx_begin),
        .sb_bus_pkt_o(sb_bus_pkt)
    );

endmodule
