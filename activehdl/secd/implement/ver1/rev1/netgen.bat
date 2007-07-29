@set XILINX=C:\Xilinx92i
@set PATH=C:\Xilinx92i\bin\nt
@C:\Xilinx92i\bin\nt\netgen.exe -w -sim -ofmt vhdl -pcf "secd_fep_trenz.pcf"  -tpw 0  -rpw 100  -s  5  -ar  Structure  -insert_pp_buffers false "secd_fep_trenz.ncd" "time_sim.vhd"
