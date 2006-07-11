SetActiveLib -work
comp -include "h:\fpga\secd\fep\fep_toplevel.vhd" 
comp -include "H:\fpga\secd\fep\secd_fep_trenz_TB.vhd" 
asim TESTBENCH_FOR_secd_fep_trenz 
wave 
wave -noreg utmi_clkout
wave -noreg utmi_databus16_8
wave -noreg reset_sw
wave -noreg ps2_clk1
wave -noreg ps2_data1
wave -noreg fpga_rxd
wave -noreg fpga_txd
wave -noreg fpga_cts
wave -noreg fpga_rts
wave -noreg vsync_b
wave -noreg hsync_b
wave -noreg fpga_b
wave -noreg fpga_g
wave -noreg fpga_r
wave -noreg mm_led
wave -noreg led
wave -noreg joy_down
wave -noreg joy_fire
wave -noreg joy_left
wave -noreg joy_right
wave -noreg joy_up
wave -noreg lcd_e
wave -noreg lcd_rw
wave -noreg lcd_rs
wave -noreg lcd_d
wave -noreg aud_out
wave -noreg ram_a
wave -noreg ram_io
wave -noreg ram_bhen
wave -noreg ram_blen
wave -noreg ram_cen
wave -noreg ram_oen
wave -noreg ram_wen
wave -noreg cf_reset
wave -noreg cf_irq
wave -noreg cf_iord
wave -noreg cf_iowr
wave -noreg cf_wait
wave -noreg cf_dasp
wave -noreg cf_pdiag
wave -noreg cf_cd1
wave -noreg cf_cd2
wave -noreg iois16
wave -noreg cf_oe
wave -noreg cf_pwr_en
wave -noreg cf_cs0
wave -noreg cf_cs1
wave -noreg cf_we
wave -noreg cf_rew
# The following lines can be used for timing simulation
# acom <backannotated_vhdl_file_name>
# comp -include "H:\fpga\secd\fep\secd_fep_trenz_TB_tim_cfg.vhd" 
# asim TIMING_FOR_secd_fep_trenz 
