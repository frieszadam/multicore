`ifndef CACHE_VH
`define CACHE_VH

// `define DISABLE_TESTING

// Macro functions are used to pass parameters to struct declarations
`define core_cache_pkt_width 69
`define cache_bus_pkt_width(dma_data_width_p) \
    (33 + 32 * dma_data_width_p)

`define dma_offset_incr(dma_data_size_p) \
    (1 << (5 + dma_data_size_lp))

`define declare_cache_bus_pkt_t(dma_data_width_p) \
    typedef struct packed {                       \
        logic we;                                 \
        logic [31:0] addr;                        \
        logic [(32*dma_data_width_p)-1:0] wdata;  \
    } cache_bus_pkt_t

`define declare_cache_block_t(tag_width_p, block_width_p) \
    typedef struct packed {                               \
        block_state_t block_state;                        \
        logic [tag_width_p-1:0] tag;                      \
        logic [(32*block_width_p)-1:0] data;              \
    } cache_block_t

`endif
