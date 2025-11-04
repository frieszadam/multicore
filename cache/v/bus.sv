// REVISIT ADD SPEC
// Hold counter for the block_width_p / dma_data_width_p to monitor when reqs complete 

`include "v/cache.svh"

module bus #(
    parameter num_caches_p,       // number of caches in system
    parameter block_width_p,      // words per block
    parameter dma_data_width_p,   // bus transfer size in words
    localparam cache_bus_pkt_width_lp = `cache_bus_pkt_width(dma_data_width_p)
) (
    input  logic clk_i, // REVISIT MULTICORE INTEGRATION (retain scheduled cache ID and tx/rx counters)
    input  logic nreset_i,

    // Cache to Bus
    input  logic [num_caches_p-1:0] cb_valid_i,
    output logic [num_caches_p-1:0] cb_yumi_o,
    input  logic [cache_bus_pkt_width_lp-1:0] [num_caches_p-1:0] cb_pkt_i,

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
    `declare_cache_bus_pkt_t(dma_data_width_p)
    cache_bus_pkt_t [num_caches_p-1:0] cb_pkt;
    assign cb_pkt = cb_pkt_i;

    logic [num_caches_p-1:0] [31:0] pkt_addr;
    logic [num_caches_p-1:0] [(dma_data_width_p*32)-1:0] pkt_wdata;
    logic [num_caches_p-1:0] pkt_we;

    always_comb begin
        for (int i = 0; i < num_caches_p; i++) begin
            pkt_addr[i] = cb_pkt[i].addr;
            pkt_wdata[i] = cb_pkt[i].wdata;
            pkt_we[i] = cb_pkt[i].we;
        end
    end

    assign cb_data_o   = mem_data_i;
    assign mem_valid_o = |cb_valid_i;
    assign cb_yumi_o   = mem_ready_i & cb_valid_i;

    generate
        if (num_caches_p == 1) begin : gen_one_cache
            assign cb_valid_o = mem_valid_i;

            assign mem_wdata_o = pkt_wdata;
            assign mem_addr_o  = pkt_addr;
            assign mem_we_o    = pkt_we;

        end else begin : gen_multi_cache
            // REVISIT MULTICORE INTEGRATION
        end
    endgenerate

    
endmodule
