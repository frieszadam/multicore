// Edge case behavior:
//  if empty and deq + enq outputs wdata_i
//  if (full & deq) enq valid
//  else if (full & ~deq) enq invalid
module fifo #(data_width_p, els_p) (
    input logic clk_i,
    input logic nreset_i,
    input logic rd_i,
    input logic wr_i,
    input logic [data_width_p-1:0] wdata_i,
    
    output logic full_o,
    output logic empty_o,
    output logic [data_width_p-1:0] rdata_o
);

    localparam els_size_lp = $clog2(els_p);

    logic enq, deq;
    logic [data_width_p-1:0] mem_array_r [els_p-1:0];
    logic [data_width_p-1:0] mem_array_n [els_p-1:0];

    logic [els_size_lp-1:0] wr_addr_r, wr_addr_n, rd_addr_r, rd_addr_n;
    logic [$clog2(els_p+1)-1:0] count_r, count_n;

    always_comb begin
        count_n = count_r; // Default
        case ({enq, deq})
            2'b10: count_n = count_r + 1;
            2'b01: count_n = count_r - 1;
            2'b11: count_n = count_r;
            default: count_n = count_r;
        endcase
    end

    assign full_o = count_r == els_p;
    assign empty_o = count_r == '0;

    assign enq = wr_i & (~full_o  | rd_i);
    assign deq = rd_i & (~empty_o | wr_i);

    always_ff @(posedge clk_i) begin
        if (~nreset_i) begin
            count_r   <= '0;
            wr_addr_r <= '0;
            rd_addr_r <= '0;
        end else begin
            count_r   <= count_n;
            wr_addr_r <= wr_addr_n;
            rd_addr_r <= rd_addr_n;
        end

        mem_array_r <= mem_array_n;
    end
    
    always_comb begin
        rd_addr_n = rd_addr_r;
        if (deq) begin
            rd_addr_n = (rd_addr_r == (els_p-1))? '0: rd_addr_r + els_size_lp'(1);
        end

        wr_addr_n = wr_addr_r;
        if (enq) begin
            wr_addr_n = (wr_addr_r == (els_p-1))? '0: wr_addr_r + els_size_lp'(1);
        end
        rdata_o = empty_o? {data_width_p{wr_i}} & wdata_i: mem_array_r[rd_addr_r];

        mem_array_n = mem_array_r;
        if (enq)
            mem_array_n[wr_addr_r] = wdata_i;            
    end

endmodule
