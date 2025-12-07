// Non-synth memory model simulating bursty access with parameterizable delay

module memory_model #(
    parameter words_p,
    parameter width_words_p,
    parameter delay_p,
    parameter init_file_p = "",
    
    localparam addr_width_lp = $clog2(words_p)
)(
    input  logic clk_i,
    input  logic nreset_i,

    // Memory to Bus
    input  logic valid_i,
    output logic ready_o,           // Model actually requires data before acceptance
    output logic valid_o,

    input  logic we_i,
    input  logic [31:0] addr_i,     // Byte address
    input  logic [(width_words_p*32)-1:0] wdata_i,
    output logic [(width_words_p*32)-1:0] data_o
);

    logic valid_n;
    logic [(width_words_p*32)-1:0] rdata_r, rdata_n;
    logic [31:0] data_r [words_p-1:0];
    logic [31:0] data_n [words_p-1:0];

    logic mem_read, mem_write;
    logic [addr_width_lp-1:0] mem_addr;
    logic [(width_words_p*32)-1:0] mem_wdata;
    logic [addr_width_lp-1:0] new_addr;
    assign new_addr = addr_i[2 +: addr_width_lp];

    generate
        if (delay_p == 1) begin : gen_single_cycle_delay
            assign ready_o = 1'b1;

            assign mem_read = valid_i & ~we_i;
            assign mem_write = valid_i & we_i;
            assign mem_addr = new_addr;
            assign mem_wdata = wdata_i;

        end else begin : gen_multi_cycle_delay
            logic [delay_p-1:0] valid_shifter_r, valid_shifter_n, we_shifter_r, we_shifter_n;
            logic [delay_p-1:0] [addr_width_lp-1:0] addr_shifter_r, addr_shifter_n;
            logic [delay_p-1:0] [(width_words_p*32)-1:0] wdata_shifter_r, wdata_shifter_n;
            // logic [addr_width_lp-1:0] addr_shifter_r [delay_p-1:0];
            // logic [addr_width_lp-1:0] addr_shifter_n [delay_p-1:0];
            // logic [(width_words_p*32)-1:0] wdata_shifter_r [delay_p-1:0];
            // logic [(width_words_p*32)-1:0] wdata_shifter_n [delay_p-1:0];
            logic addr_contig;

            always_comb begin
                addr_contig = new_addr == addr_shifter_r[0] | (new_addr + width_words_p) == addr_shifter_r[0];
                ready_o = ~|valid_shifter_r[delay_p-2:0] | (valid_shifter_r[0] & addr_contig);

                valid_shifter_n = {valid_shifter_r[delay_p-2:0], ready_o & valid_i};
                we_shifter_n    = {we_shifter_r[delay_p-2:0], we_i};

                addr_shifter_n  = {addr_shifter_r[delay_p-2:0], new_addr};
                wdata_shifter_n = {wdata_shifter_r[delay_p-2:0], wdata_i};
            end

            always_ff @(posedge clk_i) begin
                if (~nreset_i) begin
                    valid_shifter_r <= '0;
                end else begin
                    valid_shifter_r <= valid_shifter_n;
                end

                we_shifter_r    <= we_shifter_n;
                addr_shifter_r  <= addr_shifter_n;
                wdata_shifter_r <= wdata_shifter_n;
            end

            assign mem_write = valid_shifter_r[delay_p-2] & we_shifter_r[delay_p-2];
            assign mem_read  = valid_shifter_r[delay_p-2] & ~we_shifter_r[delay_p-2];
            assign mem_addr  = addr_shifter_r[delay_p-2];
            assign mem_wdata = wdata_shifter_r[delay_p-2];
        end
    endgenerate

    assign data_o = valid_o? rdata_r: 'x;

    always_ff @(posedge clk_i) begin
        if (~nreset_i)
            valid_o <= 1'b0;
        else
            valid_o <= (mem_read | mem_write);
    end

    always_comb begin
        for (int i = 0; i < width_words_p; i++)
            rdata_n[32*i +: 32] = data_r[mem_addr+i]; // REVISIT little endian / big endian
    end

    always_ff @(posedge clk_i) begin
        rdata_r <= rdata_n;
        
        if (~nreset_i) begin
            // Non-synth initialization
            if (init_file_p != "") begin
                $readmemh(init_file_p, data_r);
            end else begin
                for (integer i = 0; i < words_p; i++)
                    data_r[i] <= '0;
            end
        end else if (mem_write) begin
            for (int i = 0; i < width_words_p; i++)
                data_r[mem_addr+i] <= mem_wdata[32*i +: 32];
        end

    end

    `ifndef DISABLE_TESTING
        property p_mem_valid_delay;
            @(posedge clk_i) if (nreset_i)
                valid_i & ready_o |-> ##(delay_p) valid_o;
        endproperty

        a_mem_valid_delay: assert property (p_mem_valid_delay)
            else $error("Assertion failure: valid_o must be asserted delay_p cycles after accepted req.");

    `endif

endmodule