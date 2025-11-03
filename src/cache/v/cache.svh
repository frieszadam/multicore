`ifndef CACHE_SVH
`define CACHE_SVH

// REVISIT consider how to pass parameter values into the struct file

// `define DISABLE_TESTING

typedef struct packed {
    logic we;           // write enable bit
    logic [3:0] be;     // byte enable
    logic [31:0] addr;
    logic [31:0] wdata; // write data
} core_cache_pkt_t;

// REVISIT hardcode (16 = dma_data_width_p)
`define DMA_DATA_WIDTH (16*32)-1:0

typedef struct packed {
    logic we;           // write enable bit
    logic [31:0] addr;
    logic [`DMA_DATA_WIDTH] wdata; // write data
} cache_bus_pkt_t;

typedef struct packed {
    logic tag_i;           // write enable bit
    logic [31:0] addr;
    logic [31:0] wdata; // write data
} bus_cache_pkt_t;

typedef enum logic [1:0] {s_invalid, s_exclusive, s_shared, s_modified} block_state_t;

// REVISIT hardcode (tag_size_p = 22), (block_size_p = 16)

typedef struct packed {
    logic lru;
    block_state_t block_state;
    logic [22-1:0] tag;
    logic [(32*16)-1:0] data;
} cache_block_t;

`endif
