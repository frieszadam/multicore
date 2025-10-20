// REVISIT MODEL means consider a more realistic main memory model
// idea: add delay considering DRAM burst access model

module main_memory #(
    parameter els_p,
    parameter dma_data_width_p,   // bus transfer size in words
    parameter init_file_p = ""
)(
    input  logic clk_i,
    input  logic nreset_i,

    // Memory to Bus
    input  logic mem_valid_i,
    output logic mem_ready_o,
    output logic mem_valid_o,

    input  logic mem_we_i,
    input  logic [`DMA_DATA_WIDTH] mem_addr_i,
    input  logic [(dma_data_width_p*32)-1:0] mem_wdata_i,
    output logic [(dma_data_width_p*32)-1:0] mem_data_o
);
    localparam addr_size_lp = $clog2(els_p);

    logic [addr_size_lp-1:0] mem_addr;
    logic [`DMA_DATA_WIDTH] mem_rdata_r, mem_rdata_n;
    logic [els_p-1:0] [7:0] mem_data_r, mem_data_n;

    assign mem_addr = mem_addr_i[addr_size_lp-1:0];
    assign mem_ready_o = 1'b1; // REVISIT MODEL

    always_comb begin
        mem_data_n = mem_data_r;
        if (mem_valid_i & mem_we_i)
            mem_data_n[mem_addr+:dma_data_width_p/4] = mem_wdata_i;
        
        mem_rdata_n = mem_data_r[mem_addr+:dma_data_width_p/4]; // REVISIT little endian / big endian
    end

    always_ff @(posedge clk_i) begin
        mem_rdata_r <= mem_rdata_n;

        if (~nreset_i)
            if (init_file_p != "") begin
                $readmemh(init_file_p, mem); // non-synth used for preloading for tests
            end else begin
                for (integer i = 0; i < els_p; i++)
                    mem[i] <= '0;
            end
            mem_valid_o <= 1'b0;
        else begin
            mem_data_r <= mem_data_n;
            mem_valid_o <= mem_valid_i & ~mem_we_i; // REVISIT MODEL
        end
    end



endmodule