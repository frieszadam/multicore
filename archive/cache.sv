// DFF cache with configurable size and associativity

module cache #(
    parameter BLOCK_SIZE    = 256,          // bits per block
    parameter NUM_BLOCKS    = 16,           // total number of blocks
    parameter ASSOC         = 2,            // number of ways
    localparam NUM_SETS     = NUM_BLOCKS / ASSOC,
    localparam OFFSET_BITS  = $clog2(BLOCK_SIZE / 8),
    localparam INDEX_BITS   = $clog2(NUM_SETS),
    localparam TAG_BITS     = 32 - OFFSET_BITS - INDEX_BITS
)(
    input  logic clk_i,
    input  logic reset_i,
    input  logic rd_en_i,
    input  logic wr_en_i,
    input  logic [31:0] rd_addr_i,
    input  logic [BLOCK_SIZE-1:0] wr_data_i,
    output logic [31:0] rd_data_o,
    output logic        rd_valid_o
);

    // Synthesizable construct, grouping cache register wires together for easy reference
    typedef struct packed {
        logic valid, lru;
        logic [TAG_BITS-1:0] tag;
        logic [BLOCK_SIZE-1:0] data;
    } cache_block_s;

    // Cache storage: NUM_SETS sets, each with ASSOC ways
    cache_block_s [NUM_SETS-1:0][ASSOC-1:0] cache_memory_r, cache_memory_n;

    // Extract address fields
    logic [INDEX_BITS-1:0]    rd_set_index;
    logic [OFFSET_BITS-1:0]   rd_byte_offset;
    logic [TAG_BITS-1:0]      rd_tag;

    assign rd_byte_offset = rd_addr_i[OFFSET_BITS-1:0];  // LSB
    assign rd_set_index   = rd_addr_i[OFFSET_BITS +: INDEX_BITS];
    assign rd_tag         = rd_addr_i[31 -: TAG_BITS];  // MSB

    assign wr_byte_offset = rd_addr_i[OFFSET_BITS-1:0];  // LSB
    assign wr_set_index   = rd_addr_i[OFFSET_BITS +: INDEX_BITS];
    assign wr_tag         = rd_addr_i[31 -: TAG_BITS];  // MSB


    // Read logic
    logic hit;
    logic [31:0] word_selected;

    always_comb begin
        hit = 1'b0;
        word_selected = 32'b0;
        
        // ASSOC # muxes and comparators
        for (int w = 0; w < ASSOC; w++) begin
            if (cache_memory_r[rd_set_index][w].valid &&
                cache_memory_r[rd_set_index][w].rd_tag == rd_tag) begin
                hit = 1'b1;
                cache_memory_r[rd_set_index][w].lru = 1'b1;
                word_selected = cache_memory_r[rd_set_index][w].data[(rd_byte_offset << 3) +: 32];
            end
        end
    end

    assign rd_valid_o = hit;
    assign rd_data_o  = word_selected;

    // Update registers
    always_ff @(posedge clk_i) begin
        // Synchronous reset logic
        if (reset_i) begin
            for (int s = 0; s < NUM_SETS; s++) begin
                for (int w = 0; w < ASSOC; w++) begin
                    cache_memory_r[s][w].valid <= 1'b0;
                end
            end
        end else begin
            cache_memory_r <= cache_memory_n;
        end
    end

    always_comb begin
        for (int i = 0; i < ASSOC; i++) begin
            
        end
    end

    // Write logic - modify to include replacement scheme
    always_comb begin
        cache_memory_n = cache_memory_r;

        if (wr_en_i) begin
            
            cache_memory_n[wr_set_index][0].valid = 1'b1;
            cache_memory_n[wr_set_index][0].tag   = tag;

            // Write 32-bit word into the 256-bit block -- INCORRECT
            cache_memory_n[wr_set_index][0].data = cache_memory_r[wr_set_index][0].data;
            cache_memory_n[wr_set_index][0].data[(wr_byte_offset << 3) +: 32] = wr_data_i;
        end
    end

    assign valid 

endmodule
