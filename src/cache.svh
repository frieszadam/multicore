`ifndef CACHE_SVH
`define CACHE_SVH

typedef struct packed {
    logic we;           // write enable bit
    logic [3:0] be;     // byte enable
    logic [31:0] addr;
    logic [31:0] wdata; // write data
} core_cache_pkt_t;

typedef struct packed {
    logic we;           // write enable bit
    logic [31:0] addr;
    logic [(dma_data_width_p*32)-1:0] wdata; // write data
} cache_bus_pkt_t;

typedef struct packed {
    logic tag_i;           // write enable bit
    logic [31:0] addr;
    logic [31:0] wdata; // write data
} bus_cache_pkt_t;

typedef enum {s_invalid, s_exclusive, s_shared, s_modified} block_state_t;

typedef struct packed {
    logic lru;
    block_state_t block_state;
    logic [tag_size_lp-1:0] tag;
    logic [block_size_p-1:0] data;
} cache_block_t;

`endif
