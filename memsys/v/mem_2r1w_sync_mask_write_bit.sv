module mem_2r1w_sync_mask_write_bit #(
    parameter width_p,
    parameter els_p,
    localparam addr_width_lp = $clog2(els_p)
) (
    input logic clk_i,
    input logic reset_i,
    
    // core access ports
    input  logic a_v_i,
    input  logic [addr_width_lp-1:0] a_addr_i,
    input  logic a_w_i,
    input  logic [width_p-1:0] a_w_mask_i,
    input  logic [width_p-1:0] a_data_i,
    output logic [width_p-1:0] a_data_o,

    input  logic b_v_i,
    input  logic [addr_width_lp-1:0] b_addr_i,
    output logic [width_p-1:0] b_data_o
);
    logic [addr_width_lp-1:0] b_addr;
    assign b_addr = (a_v_i & a_w_i)? a_addr_i: b_addr_i;

    bsg_mem_1rw_sync_mask_write_bit #(
        .width_p(width_p),
        .els_p(els_p)
    ) u_mem0 (
        .clk_i,
        .reset_i,

        .data_i(a_data_i),
        .addr_i(a_addr_i),
        .v_i(a_v_i),
        .w_i(a_w_i),
        .w_mask_i(a_w_mask_i),
        .data_o(a_data_o)
    );

    bsg_mem_1rw_sync_mask_write_bit #(
        .width_p(width_p),
        .els_p(els_p)
    ) u_mem1 (
        .clk_i,
        .reset_i,

        .data_i(a_data_i),
        .addr_i(b_addr),
        .v_i(a_v_i | b_v_i),
        .w_i(a_w_i),
        .w_mask_i(a_w_mask_i),
        .data_o(b_data_o)
    );

    `ifndef DISABLE_TESTING
        property p_no_read_write_intersection;
            @(posedge clk_i) if (nreset_i) a_v_i & a_we_i |-> ~b_v_i;
        endproperty

        a_no_read_write_intersection: assert property (p_no_read_write_intersection)
            else $error("Assertion failure: only 2 reads or 1 writes may happen in a given cycle.");
    `endif

endmodule
