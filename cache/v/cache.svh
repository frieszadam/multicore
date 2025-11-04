`ifndef CACHE_SVH
`define CACHE_SVH

// `define DISABLE_TESTING

typedef struct packed {
    logic we;           // write enable bit
    logic [3:0] be;     // byte enable
    logic [31:0] addr;
    logic [31:0] wdata; // write data
} core_cache_pkt_t;

typedef struct packed {
    logic tag_i;           // write enable bit
    logic [31:0] addr;
    logic [31:0] wdata; // write data
} bus_cache_pkt_t;

// Macro functions are used to pass parameters to struct declarations
`define core_cache_pkt_width 69
`define cache_bus_pkt_width(dma_data_width_p) \
    (33 + 32 * dma_data_width_p)

typedef enum logic [1:0] {s_invalid, s_exclusive, s_shared, s_modified} block_state_t;

`define declare_cache_bus_pkt_t(dma_data_width_p) \
    typedef struct packed {                        \
        logic we;                                  \
        logic [31:0] addr;                         \
        logic [(32*dma_data_width_p)-1:0] wdata;   \
    } cache_bus_pkt_t;                             \

`define declare_cache_block_t(tag_width_p, block_width_p) \
    typedef struct packed {                                  \
        block_state_t block_state;                           \
        logic [tag_width_p-1:0] tag;                         \
        logic [(32*block_width_p)-1:0] data;                 \
    } cache_block_t;

`endif
