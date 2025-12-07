// Non-synth clock gate model
// replace with PDK specific ICG
module cv32e40x_clock_gate #(
  parameter LIB
) (
    input logic clk_i,
    input logic en_i,
    input logic scan_cg_en_i,
    output logic clk_o
);

  assign clk_o = clk_i & (en_i | scan_cg_en_i);
endmodule

