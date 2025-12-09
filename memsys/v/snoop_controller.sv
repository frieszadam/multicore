`include "cache.vh"

module snoop_controller #(
    parameter dma_data_width_p,
    parameter block_width_p,

    localparam cache_bus_pkt_width_lp = `cache_bus_pkt_width(dma_data_width_p),
    localparam block_state_width_lp   = $bits(block_state_t),
    localparam offset_width_lp        = $clog2(block_width_p) + 2
)(
    input logic clk_i,
    input logic nreset_i,

    // Input from Bus
    input  logic sb_valid_i,  // Not asserted when this cache's request is under active arb
    input  logic sb_last_rx_i, // Asserted when the bus is awaiting this request's last packet
    input  logic sb_tx_begin_i,
    input  logic [cache_bus_pkt_width_lp-1:0] sb_pkt_i, // Bus address increments in response to send/receive, but other fields stay the same

    // Cache <-> Cache Controller
    input  logic sc_ready_i, // When the cache is ready to handle set tag and rd data requests
    input  logic sc_res_valid_i,
    input  logic sc_block_hit_i,
    input  logic [31-offset_width_lp:0] sc_res_addr_i,
    input  logic [block_state_width_lp-1:0] sc_block_state_i, // data valid one cycle after sc_rd_tag_state_o
    input  logic [(dma_data_width_p*32)-1:0] sc_rdata_i, // data valid one cycle after sc_rdata_en_o and sc_ready_i

    output logic sc_rd_tag_state_o, // Cache is always ready to read these requests
    output logic sc_rdata_en_o,
    output logic [31:0] sc_raddr_o,

    output logic sc_set_state_o,
    output logic sc_state_invalid_o,
    output logic sc_clr_res_o,

    // Output to Bus
    output logic sb_wait_o, // Asserted if block_hit between s_check_hit and sc_ready
    output logic sb_hit_o,
    output logic sb_valid_o, // Asserted when modified data is ready to write back in response to coherency request
    output logic [(dma_data_width_p*32)-1:0] sb_data_o
);

    `declare_cache_bus_pkt_t(dma_data_width_p);
    cache_bus_pkt_t bus_pkt;
    bus_req_type_t bus_pkt_req_type;
    block_state_t sc_block_state;

    assign bus_pkt = sb_pkt_i;
    assign bus_pkt_req_type = bus_req_type_t'(bus_pkt.req_type);
    assign sc_block_state = block_state_t'(sc_block_state_i); // only valid 1 cycle after sc_rd_tag_state_o

    logic sc_rd_data_valid_r, sc_rd_data_valid_n, state_eq_mod, state_eq_ex, req_type_ex, valid_block_hit;
    logic set_state_r, set_state_n;
    typedef enum logic [1:0] {s_idle, s_check_hit, s_set_state, s_rd_data} control_state_t;
    control_state_t control_state_r, control_state_n;

    assign state_eq_mod = sc_block_state == s_modified;
    assign state_eq_ex = sc_block_state == s_exclusive;
    assign req_type_ex = (bus_pkt_req_type == op_ld_exclusive) | (bus_pkt_req_type == op_up_exclusive);
    assign valid_block_hit = sc_block_hit_i & ~(sc_block_state == s_invalid); // only valid in s_check_hit

    always_comb begin
        case (control_state_r)
            s_idle: control_state_n = sb_valid_i & sb_tx_begin_i? s_check_hit: s_idle;
            s_check_hit: begin
                if (valid_block_hit & state_eq_mod)
                    control_state_n = s_rd_data;
                else if (valid_block_hit & ~sc_ready_i & (req_type_ex | state_eq_ex))
                    control_state_n = s_set_state;
                else
                    control_state_n = s_idle;
            end
            s_set_state: control_state_n = sc_ready_i? s_idle: s_set_state;
            s_rd_data:   control_state_n = (sb_last_rx_i & sc_rd_data_valid_r)? s_idle: s_rd_data;
            default:     control_state_n = s_idle;
        endcase

        sc_rd_data_valid_n = sc_rdata_en_o & sc_ready_i;
        set_state_n = (set_state_r | sc_set_state_o) & ~(control_state_r == s_idle);
    end

    always_ff @(posedge clk_i) begin
        if (~nreset_i) begin
            control_state_r    <= s_idle;
            sc_rd_data_valid_r <= 1'b0;
            set_state_r        <= 1'b0;
        end else begin
            control_state_r    <= control_state_n;
            sc_rd_data_valid_r <= sc_rd_data_valid_n;
            set_state_r        <= set_state_n;
        end
    end
    
    // snoop cache interface
    assign sc_rd_tag_state_o = control_state_n == s_check_hit;
    assign sc_rdata_en_o = control_state_n == s_rd_data;
    assign sc_raddr_o = bus_pkt.addr;
    
    // Set state at the start of read transaction
    assign sc_set_state_o = sc_ready_i & ( (control_state_r == s_rd_data & ~set_state_r) |
        (control_state_r == s_set_state ) | (valid_block_hit & (req_type_ex | state_eq_mod | state_eq_ex)) );
    assign sc_state_invalid_o = req_type_ex;
    assign sc_clr_res_o = sb_valid_i & bus_pkt.lr_sc & (bus_pkt.addr[31:offset_width_lp] == sc_res_addr_i) & sc_res_valid_i;

    // snoop bus interface
    assign sb_wait_o  = control_state_r != s_idle & control_state_n != s_idle;
    assign sb_valid_o = sc_rd_data_valid_r;
    assign sb_data_o  = sc_rdata_i;
    assign sb_hit_o   = valid_block_hit;

    `ifndef DISABLE_TESTING
        property p_no_upgrade_from_exclusive;
            @(posedge clk_i) if (nreset_i)
                sb_valid_i & (bus_pkt_req_type == op_up_exclusive) |-> ~(sc_block_hit_i & (state_eq_mod | state_eq_ex));
        endproperty

        a_no_upgrade_from_exclusive: assert property (p_no_upgrade_from_exclusive)
            else $error("Assertion failure: An upgrade request cannot come when this cache has the block exclusively.");

        property p_data_tag_read_onehot0;
            @(posedge clk_i) if (nreset_i) $onehot0(sc_rdata_en_o, sc_rd_tag_state_o); 
        endproperty

        a_data_tag_read_onehot0: assert property (p_data_tag_read_onehot0)
            else $error("Assertion failure: Cannot read tag and data in same clock cycle, conflicts with snp_way_index design.");
    `endif

endmodule

/*
  Pseudocode

  if block_hit 
    assert sb_wait_o
    obtain home cache access

    if block_state == modified 
      assert sb_valid_o and send forwarded data to requesting cache
      BUS forwards this write data back to main memory at same time
      if bus_pkt.bus_req_type == RDX
        set block_state to invalid
      else
         set block_state to shared
      deassert sb_wait_o

    else // block_state != modified 
      if bus_pkt.bus_req_type == RDX
        set block_state to invalid
      else
         set block_state to shared
      deassert sb_wait_o
*/
