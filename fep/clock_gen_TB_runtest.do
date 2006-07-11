SetActiveLib -work
comp -include "h:\fpga\secd\vhdl\clock_gen.vhd" 
comp -include "H:\fpga\secd\fep\clock_gen_TB.vhd" 
asim TESTBENCH_FOR_clock_gen 
wave 
wave -noreg reset
wave -noreg clk
wave -noreg alu_ins
wave -noreg ram_busy
wave -noreg phi_read
wave -noreg phi_alu
wave -noreg phi_write
wave -noreg phi_next
wave -noreg stop
wave -noreg stopped
# The following lines can be used for timing simulation
# acom <backannotated_vhdl_file_name>
# comp -include "H:\fpga\secd\fep\clock_gen_TB_tim_cfg.vhd" 
# asim TIMING_FOR_clock_gen 
