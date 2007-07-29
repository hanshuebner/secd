set XILINX=C:\Xilinx92i
call "C:\Xilinx92i\bin\nt\xst.exe" -ifn secd_fep_trenz.xst >> synthesize.plg
call "C:\Xilinx92i\bin\nt\netgen.exe" -ofmt vhdl -intstyle silent -w secd_fep_trenz.ngc  secd_fep_trenz.vhd >> synthesize.plg
