package cache_pkg;

    typedef struct packed {
        logic we;           // write enable bit
        logic [3:0] be;     // byte enable
        logic [31:0] addr;
        logic [31:0] wdata; // write data
    } core_cache_pkt_t;

    // typedef struct packed {
    //     logic tag_i;           // write enable bit
    //     logic [31:0] addr;
    //     logic [31:0] wdata; // write data
    // } bus_cache_pkt_t;

    typedef enum logic [1:0] {s_invalid, s_exclusive, s_shared, s_modified} block_state_t;

endpackage