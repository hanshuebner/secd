SetActiveLib -work
comp -include "h:\fpga\secd\fep\clock_synthesis.vhd" 
comp -include "H:\fpga\secd\fep\clock_synthesis_TB.vhd" 
asim TESTBENCH_FOR_clock_synthesis 
wave 
wave -noreg clk_30mhz
wave -noreg vdu_clk
wave -noreg cpu_clk
wave -noreg locked
# The following lines can be used for timing simulation
# acom <backannotated_vhdl_file_name>
# comp -include "H:\fpga\secd\fep\clock_synthesis_TB_tim_cfg.vhd" 
# asim TIMING_FOR_clock_synthesis 
