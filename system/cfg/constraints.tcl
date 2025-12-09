# constraints.tcl
#
# This file is where design timing constraints are defined for Genus and Innovus.
# Many constraints can be written directly into the Hammer config files. However, 
# you may manually define constraints here as well.
#

set clk_period 15.0
set mem_input_delay [expr {$clk_period / 4}]
set mem_output_delay [expr {$clk_period / 2}]

create_clock -name clk -period $clk_period [get_ports clk_i]
set_clock_uncertainty 0.100 [get_clocks clk]

set_input_delay  $mem_input_delay -max -clock [get_clocks clk] [all_inputs]
set_output_delay $mem_output_delay -max -clock [get_clocks clk] [all_outputs]

# Always set the input/output delay as 0 for clock hold checks
set_input_delay  0.0 -min -clock [get_clocks clk] [all_inputs]
set_output_delay 0.0 -min -clock [get_clocks clk] [all_outputs]
