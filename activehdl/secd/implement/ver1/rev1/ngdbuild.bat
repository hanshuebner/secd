@set XILINX=C:\Xilinx92i
@set PATH=C:\Xilinx92i\bin\nt
@C:\Xilinx92i\bin\nt\ngdbuild.exe -p 3S1000FT256-5   -sd "h:\fpga\secd\activehdl\secd\synthesis" -sd "h:\fpga\secd\activehdl\secd\compile" -sd "h:\fpga\secd\activehdl\secd\src" -sd "C:\Program Files\Aldec\Active-HDL 7.2\vlib\SPARTAN3\compile" -uc "secd_fep_trenz.ucf" "secd_fep_trenz.ngc" "secd_fep_trenz.ngd"
