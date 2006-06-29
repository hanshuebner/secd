SetActiveLib -work
comp -include "h:\fpga\secd\fmf\idt71v416.vhd" 
comp -include "h:\fpga\secd\fep\secd_ram_controller.vhd" 
comp -include "H:\fpga\secd\fep\secd_ram_controller_TB.vhd" 
asim TESTBENCH_FOR_secd_ram_controller 
wave 
wave -noreg clk
wave -noreg reset
wave -noreg busy8
wave -noreg busy32
wave -noreg din32
wave -noreg dout32
wave -noreg addr32
wave -noreg read32_enable
wave -noreg write32_enable
wave -noreg din8
wave -noreg dout8
wave -noreg addr8
wave -noreg read8_enable
wave -noreg write8_enable
wave -noreg ram_oen
wave -noreg ram_cen
wave -noreg ram_wen
wave -noreg ram_io
wave -noreg ram_a
wave -noreg ram_bhen
wave -noreg ram_blen
# The following lines can be used for timing simulation
# acom <backannotated_vhdl_file_name>
# comp -include "H:\fpga\secd\fep\secd_ram_controller_TB_tim_cfg.vhd" 
# asim TIMING_FOR_secd_ram_controller 
