SetActiveLib -work
comp -include "h:\fpga\secd\fep\vdu8.vhd" 
comp -include "H:\fpga\secd\fep\vdu_TB.vhd" 
asim TESTBENCH_FOR_vdu 
wave 
wave -noreg vdu_clk_in
wave -noreg cpu_clk_out
wave -noreg ram_clk_out
wave -noreg vdu_rst
wave -noreg vdu_cs
wave -noreg vdu_rw
wave -noreg vdu_addr
wave -noreg vdu_data_in
wave -noreg vdu_data_out
wave -noreg vga_red_o
wave -noreg vga_green_o
wave -noreg vga_blue_o
wave -noreg vga_hsync_o
wave -noreg vga_vsync_o
# The following lines can be used for timing simulation
# acom <backannotated_vhdl_file_name>
# comp -include "H:\fpga\secd\fep\vdu_TB_tim_cfg.vhd" 
# asim TIMING_FOR_vdu 
