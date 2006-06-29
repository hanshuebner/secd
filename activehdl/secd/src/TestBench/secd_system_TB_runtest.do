SetActiveLib -work
comp -include "h:\fpga\secd\vhdl\secd_defs.vhd" 
comp -include "h:\fpga\secd\vhdl\secd_ram_defs.vhd" 
comp -include "h:\fpga\secd\secd-microcode.vhd" 
comp -include "h:\fpga\secd\vhdl\microcode_rom.vhd" 
comp -include "h:\fpga\secd\vhdl\clock_gen.vhd" 
comp -include "h:\fpga\secd\vhdl\secd_ram.vhd" 
comp -include "h:\fpga\secd\vhdl\control_unit.vhd" 
comp -include "h:\fpga\secd\vhdl\datapath.vhd" 
comp -include "h:\fpga\secd\vhdl\toplevel.vhd" 
comp -include "h:\fpga\secd\vhdl\testbench.vhd" 
asim TESTBENCH_FOR_secd_system