// Statically outputs the current priority of each index given the LRU history table,
// here referred to as flags. The table is updated given the valid and index fields.
//
// The alternate LRU module may be implemented using a priority_lru, by outputting the
// highest priority index.

module priority_lru #(
    parameter size_p,
    localparam width_lp = 2**size_p
) (
    input logic               clk_i, 
    input logic               nreset_i,
    input logic               valid_i, // valid access
    input logic  [size_p-1:0] index_i, // access index
    
    // Relative piority of each LRU slot
    output logic [width_lp-1:0] [size_p-1:0] priority_o
);

    logic [width_lp-2:0] flag_r, flag_n;
    logic [width_lp-1:0] [size_p-1:0] distance_from_lru;

    always_ff @(posedge clk_i) begin
        if (~nreset_i)
            flag_r <= '0;
        else
            flag_r <= flag_n;
    end

    if (size_p == 1) begin                
        always_comb begin
            priority_o[0] = flag_r;
            priority_o[1] = ~flag_r;
            flag_n = valid_i? ~index_i: flag_r;
        end
    end

    else if (size_p == 2) begin
        always_comb begin
            // Distance from selecting this index in number of moves 
            distance_from_lru[0] = flag_r[0]  + (flag_r[1] << 1);
            distance_from_lru[1] = flag_r[0]  + (~flag_r[1] << 1);
            distance_from_lru[2] = ~flag_r[0] + (flag_r[2] << 1);
            distance_from_lru[3] = ~flag_r[0] + (~flag_r[2] << 1);
            
            // Since highest value = highest priority we do (max distance - distance) = priority
            // which is equivalent to bitwise inversion in 1s complement.
            // This makes sense as the least recently used value will be at distance 0 and should
            // have highest priority.
            for (int i = 0; i < width_lp; i++) begin
                priority_o[i] = ~distance_from_lru[i];
            end

            flag_n[0] =  (valid_i)? ~index_i[1]: flag_r[0];
            flag_n[1] =  (valid_i & ~index_i[1])? ~index_i[0]: flag_r[1];
            flag_n[2] =  (valid_i &  index_i[1])? ~index_i[0]: flag_r[2];
        end
    end

    else if (size_p == 3) begin
        always_comb begin
            // Distance from selecting this index in number of moves 
            distance_from_lru[0] = flag_r[0]  + (flag_r[1] << 1)  + (flag_r[3] << 2);
            distance_from_lru[1] = flag_r[0]  + (flag_r[1] << 1)  + (~flag_r[3] << 2);
            distance_from_lru[2] = flag_r[0]  + (~flag_r[1] << 1) + (flag_r[4] << 2);
            distance_from_lru[3] = flag_r[0]  + (~flag_r[1] << 1) + (~flag_r[4] << 2);
            
            distance_from_lru[4] = ~flag_r[0] + (flag_r[2] << 1)  + (flag_r[5] << 2);
            distance_from_lru[5] = ~flag_r[0] + (flag_r[2] << 1)  + (~flag_r[5] << 2);
            distance_from_lru[6] = ~flag_r[0] + (~flag_r[2] << 1) + (flag_r[6] << 2);
            distance_from_lru[7] = ~flag_r[0] + (~flag_r[2] << 1) + (~flag_r[6] << 2);

            // Since highest value = highest priority we do (max distance - distance) = priority
            // which is equivalent to bitwise inversion in 1s complement.
            // This makes sense as the least recently used value will be at distance 0 and should
            // have highest priority.
            for (int i = 0; i < width_lp; i++) begin
                priority_o[i] = ~distance_from_lru[i];
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
