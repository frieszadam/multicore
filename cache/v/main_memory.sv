// REVISIT (11/2, model DRAM burst access delay)

module main_memory #(
    parameter els_p,
    parameter dma_data_width_p,   // bus transfer size in words
    parameter init_file_p = "",
    localparam addr_size_lp = $clog2(els_p)
)(
    input  logic clk_i,
    input  logic nreset_i,

    // Memory to Bus
    input  logic mem_valid_i,
    output logic mem_ready_o,
    output logic mem_valid_o,

    input  logic mem_we_i,
    input  logic [31:0] mem_addr_i,
    input  logic [(dma_data_width_p*32)-1:0] mem_wdata_i,
    output logic [(dma_data_width_p*32)-1:0] mem_data_o
);

    logic [(dma_data_width_p*32)-1:0] mem_rdata_r, mem_rdata_n;
    logic [31:0] mem_data_r [els_p-1:0];
    logic [31:0] mem_data_n [els_p-1:0];
    logic [addr_size_lp-1:0] mem_addr;

    assign mem_addr = mem_addr_i[addr_size_lp+1:2]; // lower two bits are byte address
    assign mem_ready_o = 1'b1; // REVISIT MODEL
    assign mem_data_o = mem_rdata_r;

    always_comb begin
        mem_data_n = mem_data_r;
        if (mem_valid_i & mem_we_i) begin
            for (int i = 0; i < dma_data_width_p; i++)
                mem_data_n[mem_addr+i] = mem_wdata_i[32*i +: 32];
        end

        for (int i = 0; i < dma_data_width_p; i++)
            mem_rdata_n[32*i +: 32] = mem_data_r[mem_addr+i]; // REVISIT little endian / big endian
    end

    always_ff @(posedge clk_i) begin
        mem_rdata_r <= mem_rdata_n;

        if (~nreset_i) begin
            for (integer i = 0; i < els_p; i++)
                mem_data_r[i] <= '0;

            // if (init_file_p != "") begin
            //     $readmemh(init_file_p, mem_data_r); // non-synth used for preloading for tests
            // end else begin
            //     for (integer i = 0; i < els_p; i++)
            //         mem_data_r[i] <= '0;
            // end
            mem_valid_o <= 1'b0;
        end else begin
            mem_data_r <= mem_data_n;
            mem_valid_o <= mem_valid_i & ~mem_we_i; // REVISIT MODEL
        end
    end



endmodule