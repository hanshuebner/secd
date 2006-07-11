SetActiveLib -work
comp -include "h:\fpga\secd\fep\secd_ram_controller.vhd" 
comp -include "H:\fpga\secd\fep\secd_ram_controller_TB.vhd" 
asim TESTBENCH_FOR_secd_ram_controller 
wave 
wave -noreg reset
wave -noreg clk
wave -noreg port8_cs
wave -noreg port8_hold
wave -noreg port8_rw
wave -noreg port8_a
wave -noreg port8_din
wave -noreg port8_dout
wave -noreg port32_cs
wave -noreg port32_hold
wave -noreg port32_re
wave -noreg port32_we
wave -noreg port32_a
wave -noreg port32_din
wave -noreg port32_dout
wave -noreg ram_cen
wave -noreg ram_wen
wave -noreg ram_oen
wave -noreg ram_bhen
wave -noreg ram_blen
wave -noreg ram_a
wave -noreg ram_io
# The following lines can be used for timing simulation
# acom <backannotated_vhdl_file_name>
# comp -include "H:\fpga\secd\fep\secd_ram_controller_TB_tim_cfg.vhd" 
# asim TIMING_FOR_secd_ram_controller 
