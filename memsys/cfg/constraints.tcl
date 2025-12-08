# constraints.tcl
#
# This file is where design timing constraints are defined for Genus and Innovus.
# Many constraints can be written directly into the Hammer config files. However, 
# you may manually define constraints here as well.
#

set clk_period 15.0
set mem_input_delay [expr {$clk_period / 4}]
set mem_output_delay [expr {$clk_period / 2}]

set core_input_delay [expr {$clk_period / 4}]
set core_output_delay [expr {$clk_period / 2}]

create_clock -name clk -period $clk_period [get_ports clk_i]
set_clock_uncertainty 0.100 [get_clocks clk]

set core_input_ports [get_ports {nreset_i cc_valid_i cc_pkt_i*}]
set core_output_ports [get_ports {cc_ready_o cc_rdata_o* cc_valid_o}]

set mem_input_ports [get_ports {mem_ready_i mem_valid_i mem_data_i}]
set mem_output_ports [get_ports {mem_valid_o mem_we_o mem_addr_o mem_wdata_o}]

set_input_delay  $core_input_delay -max -clock [get_clocks clk] $core_input_ports
set_output_delay $core_output_delay -max -clock [get_clocks clk] $core_output_ports

set_input_delay  $mem_input_delay -max -clock [get_clocks clk] $mem_input_ports
set_output_delay $mem_output_delay -max -clock [get_clocks clk] $mem_output_ports

# Always set the input/output delay as 0 for clock hold checks
set_input_delay  0.0 -min -clock [get_clocks clk] $core_input_ports
set_input_delay  0.0 -min -clock [get_clocks clk] $mem_input_ports

set_output_delay 0.0 -min -clock [get_clocks clk] $core_output_ports
set_output_delay 0.0 -min -clock [get_clocks clk] $mem_output_ports
