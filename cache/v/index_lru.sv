module index_lru #(
    parameter size_p
) (
    input logic               clk_i, 
    input logic               nreset_i,
    input logic               valid_i, // valid access
    input logic  [size_p-1:0] index_i, // access index
    output logic [size_p-1:0] index_o // LRU index
);

    localparam width_lp = 2**size_p;
    logic [width_lp-2:0] flag_r, flag_n;

    always_ff @(posedge clk_i) begin
        if (~nreset_i)
            flag_r <= '0;
        else
            flag_r <= flag_n;
    end

    if (size_p == 1) begin                
        always_comb begin
            index_o = flag_r;
            flag_n = valid_i? ~index_i: flag_r;
        end
    end

    else if (size_p == 2) begin
        always_comb begin
            index_o = (flag_r[0] << 1) | (flag_r[0]? flag_r[2]: flag_r[1]);
            
            flag_n[0] =  (valid_i)? ~index_i[1]: flag_r[0];
            flag_n[1] =  (valid_i & ~index_i[1])? ~index_i[0]: flag_r[1];
            flag_n[2] =  (valid_i &  index_i[1])? ~index_i[0]: flag_r[2];
        end
    end

    else if (size_p == 3) begin
        always_comb begin
            index_o = size_p'(flag_r[0] << (size_p-1));

            if (flag_r[0]) begin
                index_o = index_o | (flag_r[2] << (size_p-2));
                if (flag_r[2])
                    index_o = index_o | (flag_r[6] << (size_p-3));
                else
                    index_o = index_o | (flag_r[5] << (size_p-3));
            end else begin
                index_o = index_o | (flag_r[1] << (size_p-2));
                if (flag_r[1])
                    index_o = index_o | (flag_r[4] << (size_p-3));
                else
                    index_o = index_o | (flag_r[3] << (size_p-3));
            end

            // Update of each lru flag bit in the accessed set
            flag_n[0] =  (valid_i)? ~index_i[size_p-1]: flag_r[0];

            flag_n[1] =  (valid_i & ~index_i[size_p-1])? ~index_i[size_p-2]: flag_r[1];
            flag_n[2] =  (valid_i &  index_i[size_p-1])? ~index_i[size_p-2]: flag_r[2];

            flag_n[3] =  (valid_i & ~index_i[size_p-1] & ~index_i[size_p-2])? ~index_i[size_p-3]: flag_r[3];
            flag_n[4] =  (valid_i & ~index_i[size_p-1] &  index_i[size_p-2])? ~index_i[size_p-3]: flag_r[4];
            flag_n[5] =  (valid_i &  index_i[size_p-1] & ~index_i[size_p-2])? ~index_i[size_p-3]: flag_r[5];
            flag_n[6] =  (valid_i &  index_i[size_p-1] &  index_i[size_p-2])? ~index_i[size_p-3]: flag_r[6];
        end
    end

endmodule
