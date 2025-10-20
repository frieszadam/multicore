/*
    Description: 2-way DFF cache with parameterized size
    TODO: incorporate writing from both processor and main memory (over multiple cycles)
    implement write-back characteristics, determine whether should be 1R1W or 1RW
*/

module two_way_cache #(
    parameter BLOCK_SIZE    = 256,          // bits per block
    parameter NUM_BLOCKS    = 16,           // total number of blocks
    localparam NUM_SETS     = NUM_BLOCKS / 2,
    localparam OFFSET_BITS  = $clog2(BLOCK_SIZE / 8),
    localparam INDEX_BITS   = $clog2(NUM_SETS),
    localparam TAG_BITS     = 32 - OFFSET_BITS - INDEX_BITS
)(
    input  logic clk_i,
    input  logic reset_i,
    input  logic rd_en_i,
    input  logic wr_en_i,
    input  logic [31:0] rd_addr_i, wr_addr_i,
    input  logic [BLOCK_SIZE-1:0] wr_data_i,
    output logic [31:0] rd_data_o,
    output logic rd_valid_o,
    output logic cache_miss_o
);

    // Synthesizable construct, grouping cache register wires together for easy reference
    typedef struct packed {
        logic valid, dirty, lru;
        logic [TAG_BITS-1:0] tag;
        logic [BLOCK_SIZE-1:0] data;
    } cache_block_s;

    // Cache storage: NUM_SETS sets, 2 ways
    cache_block_s [NUM_SETS-1:0][1:0] cache_memory_r, cache_memory_n;

    // Extract address fields
    logic [INDEX_BITS-1:0]    rd_set_index, wr_set_index;
    logic [OFFSET_BITS-1:0]   rd_byte_offset, wr_byte_offset;
    logic [TAG_BITS-1:0]      rd_tag, wr_tag;

    assign rd_byte_offset = rd_addr_i[OFFSET_BITS-1:0];  // LSB
    assign rd_set_index   = rd_addr_i[OFFSET_BITS +: INDEX_BITS];
    assign rd_tag         = rd_addr_i[31 -: TAG_BITS];  // MSB

    assign wr_byte_offset = wr_addr_i[OFFSET_BITS-1:0];  // LSB
    assign wr_set_index   = wr_addr_i[OFFSET_BITS +: INDEX_BITS];
    assign wr_tag         = wr_addr_i[31 -: TAG_BITS];  // MSB


    // Read logic
    logic rd_was_hit, rd_hit_sel;
    logic [1:0] rd_way_hit;

    // Write logic
    logic wr_was_hit, wr_hit_sel, wr_set_full;
    logic [1:0] wr_way_hit, wr_to_way;  // wr_to_way should have at most one line hot

    always_comb begin
        // by default retain previous values
        cache_memory_n = cache_memory_r;
        
        // read logic - updates LRU field
        // muxes and comparators
        for (int w = 0; w < 2; w++) begin
            rd_way_hit[w] = cache_memory_r[rd_set_index][w].valid &
                (cache_memory_r[rd_set_index][w].tag == rd_tag);

            wr_way_hit[w] = cache_memory_r[wr_set_index][w].valid &
                (cache_memory_r[wr_set_index][w].tag == wr_tag);
        end

        rd_was_hit = rd_way_hit[0] | rd_way_hit[1];
        rd_hit_sel = rd_way_hit[1]; // 1 if found at way 2, else 0

        wr_was_hit = wr_way_hit[0] | wr_way_hit[1];
        wr_hit_sel = wr_way_hit[1]; // 1 if found at way 2, else 0

        // maintain LRU field for replacement scheme
        // "For a two-way set-associative cache, tracking when the two elements were used can
        // be implemented by keeping a single bit in each set and setting the bit to indicate
        // an element whenever that element is referenced."
        // when a read or write occurs within a set, the read or written element lru field is set to 0
        // and the other element lru field is set to 1
        cache_memory_n[rd_set_index][0].lru = (rd_en_i & rd_was_hit)? rd_hit_sel: cache_memory_r[rd_set_index][0].lru;
        cache_memory_n[rd_set_index][1].lru = (rd_en_i & rd_was_hit)? ~rd_hit_sel: cache_memory_r[rd_set_index][1].lru;

        // select read data that is a 32-bit subset of the block size
        // this describes the logical function but is quite abstract hardware
        rd_data_o = cache_memory_r[rd_set_index][rd_hit_sel].data[(rd_byte_offset << 3) +: 32];

        // Write logic - with lru replacement scheme
        // two special cases: 1) if address is already in cache     2) if cache set is full
        
        wr_set_full = cache_memory_r[wr_set_index][0].valid &
            cache_memory_r[wr_set_index][1].valid;

        // write to way 0 if wr is enabled AND we already store that address here OR
        // way not used OR (set is full AND this is not the lru)
        wr_to_way[0] = wr_en_i & (
            (wr_was_hit & ~wr_hit_sel) |
            (~cache_memory_r[wr_set_index][0].valid) |
            (wr_set_full & ~cache_memory_n[wr_set_index][0].lru) );
        
        // write to way 1 if wr is enabled AND we already store that address here OR
        // way not used OR (set is full AND this is not the lru)
        wr_to_way[1] = wr_en_i & (
            (wr_was_hit & wr_hit_sel) |
            (~cache_memory_r[wr_set_index][1].valid & cache_memory_r[wr_set_index][0].valid) | 
            (wr_set_full & ~cache_memory_n[wr_set_index][1].lru) );

        for (int i = 0; i < 2; i++) begin
            cache_memory_n[wr_set_index][i].data  = wr_to_way[i]? wr_data_i: cache_memory_r[wr_set_index][i].data;
            cache_memory_n[wr_set_index][i].tag   = wr_to_way[i]? wr_tag: cache_memory_r[wr_set_index][i].tag;

            cache_memory_n[wr_set_index][i].valid = wr_to_way[i] | cache_memory_r[wr_set_index][i].valid;
            cache_memory_n[wr_set_index][i].dirty = wr_to_way[i] | cache_memory_r[wr_set_index][i].dirty; // TODO:
            cache_memory_n[wr_set_index][i].lru   = wr_en_i? ~wr_to_way[i]: cache_memory_r[wr_set_index][i].lru;
        end
    end

    assign rd_valid_o = rd_was_hit;
    assign cache_miss_o = rd_en_i & ~ rd_valid_o;

    // Update registers
    always_ff @(posedge clk_i) begin
        // Synchronous reset logic
        if (reset_i) begin
            for (int s = 0; s < NUM_SETS; s++) begin
                cache_memory_r[s][0].valid <= 1'b0;     // first way
                cache_memory_r[s][1].valid <= 1'b0;     // second way
            end
        end else begin
            cache_memory_r <= cache_memory_n;
        end
    end
    
endmodule
