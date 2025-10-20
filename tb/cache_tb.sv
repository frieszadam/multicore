// testing method
// load and read data
// evict data and check that it is evicted (by attempting a read)
// check that LRU scheme functions properly

module cache_tb ();

    localparam BLOCK_SIZE    = 32;         // bits per block
    localparam NUM_BLOCKS    = 16;          // total number of blocks

    logic clk_i, reset_i, rd_en_i, wr_en_i, rd_valid_o, cache_miss_o;
    logic [31:0] rd_addr_i, wr_addr_i;
    logic [BLOCK_SIZE-1:0] wr_data_i, rd_data_o;

    // Instantiate device under test
    two_way_cache #(.BLOCK_SIZE(BLOCK_SIZE), .NUM_BLOCKS(NUM_BLOCKS)) dut (.*);

    always #(5) clk_i = ~clk_i;

    initial begin
        {clk_i, reset_i, rd_en_i, wr_en_i, rd_addr_i, wr_data_i} = '0;
        
        reset_i = 1'b1; @(posedge clk_i);
        reset_i = 1'b0; @(posedge clk_i);

        wr_en_i = 1'b1;

        // fill all cache blocks
        for (int i = 0; i < NUM_BLOCKS/2; i++) begin
            wr_addr_i = i*4;
            wr_data_i = i;   @(posedge clk_i);

            wr_addr_i = 64 + i*4;  // different tag bit
            wr_data_i = i;   @(posedge clk_i);

        end

        wr_en_i = 1'b0;
        rd_en_i = 1;

        // read from all cache blocks
        for (int i = 0; i < NUM_BLOCKS/2; i++) begin
            rd_addr_i = i*4; @(posedge clk_i);

            rd_addr_i = 64 + i*4; @(posedge clk_i);
        end 

        $finish;

    end

endmodule
