@set XILINX=C:\Xilinx92i
@set PATH=C:\Xilinx92i\bin\nt
@C:\Xilinx92i\bin\nt\map.exe  -p 3S1000FT256-5 -o "map.ncd"  -pr b  -k  4  -cm area  -c 100 "secd_fep_trenz.ngd" "secd_fep_trenz.pcf"
