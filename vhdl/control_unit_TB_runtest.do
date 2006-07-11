SetActiveLib -work
comp -include "h:\fpga\secd\vhdl\secd_defs.vhd" 
comp -include "h:\fpga\secd\secd-microcode.vhd" 
comp -include "h:\fpga\secd\vhdl\control_unit.vhd" 
comp -include "H:\fpga\secd\vhdl\control_unit_TB.vhd" 
asim TESTBENCH_FOR_control_unit 
wave 
wave -noreg clk
wave -noreg reset
wave -noreg phi_next
wave -noreg button
wave -noreg opcode
wave -noreg flags
wave -noreg read_sel
wave -noreg write_sel
wave -noreg alu_sel
wave -noreg alu_ins
wave -noreg stop_instruction
# The following lines can be used for timing simulation
# acom <backannotated_vhdl_file_name>
# comp -include "H:\fpga\secd\vhdl\control_unit_TB_tim_cfg.vhd" 
# asim TIMING_FOR_control_unit 
