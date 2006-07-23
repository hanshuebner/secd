setPreference -pref AutoSignature:FALSE
setPreference -pref KeepSVF:FALSE
setPreference -pref ConcurrentMode:FALSE
setPreference -pref UseHighz:FALSE
setPreference -pref UserLevel:NOVICE
setPreference -pref svfUseTime:FALSE
loadProjectFile -file "H:\fpga\secd\secd.ipf"
setMode -ss
setMode -sm
setMode -hw140
setMode -acecf
setMode -acempm
setMode -pff
setMode -bs
setMode -bs
setMode -bs
setMode -pff
setMode -pff
setMode -pff
setMode -pff
setCurrentDesign -version 0
setMode -pff
setCurrentDeviceChain -index 0
setCurrentDesign -version 0
setCurrentDeviceChain -index 0
setMode -pff
setSubmode -pffserial
setAttribute -configdevice -attr fillValue -value "FF"
setAttribute -configdevice -attr fileFormat -value "mcs"
setAttribute -configdevice -attr dir -value "UP"
setAttribute -configdevice -attr path -value "H:\fpga\secd\/"
setAttribute -configdevice -attr name -value "secd"
generate
setCurrentDesign -version 0
setCurrentDesign -version 0
setMode -bs
setMode -bs
setCable -port auto
Program -p 1 -e -v -loadfpga -defaultVersion 0 
setMode -pff
setMode -pff
setMode -pff
setSubmode -pffserial
setAttribute -configdevice -attr fillValue -value "FF"
setAttribute -configdevice -attr fileFormat -value "mcs"
setAttribute -configdevice -attr dir -value "UP"
setAttribute -configdevice -attr path -value "H:\fpga\secd\/"
setAttribute -configdevice -attr name -value "secd"
generate
setCurrentDesign -version 0
setCurrentDesign -version 0
setMode -bs
setMode -bs
Program -p 1 -e -v -loadfpga -defaultVersion 0 
setMode -pff
setMode -pff
setMode -pff
setSubmode -pffserial
setAttribute -configdevice -attr fillValue -value "FF"
setAttribute -configdevice -attr fileFormat -value "mcs"
setAttribute -configdevice -attr dir -value "UP"
setAttribute -configdevice -attr path -value "H:\fpga\secd\/"
setAttribute -configdevice -attr name -value "secd"
generate
setCurrentDesign -version 0
setCurrentDesign -version 0
setMode -bs
setMode -bs
Program -p 1 -e -v -loadfpga -defaultVersion 0 
assignFile -p 2 -file "H:/fpga/Trenz/RetroBB/Application/an-te0141-1st_steps/pong/toplevel.bit"
Program -p 2 -defaultVersion 0 
assignFile -p 2 -file "H:/fpga/Trenz/RetroBB/Application/an-te0141-1st_steps/pong/toplevel.bit"
Program -p 2 -v -defaultVersion 0 
assignFile -p 2 -file "H:/fpga/Trenz/RetroBB/Application/an-te0141-1st_steps/pong/toplevel.bit"
Program -p 2 -defaultVersion 0 
setMode -pff
setMode -pff
setMode -pff
setSubmode -pffserial
setAttribute -configdevice -attr fillValue -value "FF"
setAttribute -configdevice -attr fileFormat -value "mcs"
setAttribute -configdevice -attr dir -value "UP"
setAttribute -configdevice -attr path -value "H:\fpga\secd\/"
setAttribute -configdevice -attr name -value "secd"
generate
setCurrentDesign -version 0
setCurrentDesign -version 0
setMode -bs
setMode -bs
Program -p 1 -e -v -defaultVersion 0 
assignFile -p 2 -file "H:/fpga/secd/activehdl/secd/implement/ver1/rev1/secd_fep_trenz.bit"
setMode -pff
setMode -pff
setCurrentDesign -version 0
setCurrentDeviceChain -index 0
setMode -pff
setSubmode -pffserial
setAttribute -configdevice -attr fillValue -value "FF"
setAttribute -configdevice -attr fileFormat -value "mcs"
setAttribute -configdevice -attr dir -value "UP"
setAttribute -configdevice -attr path -value "H:\fpga\secd\/"
setAttribute -configdevice -attr name -value "secd"
generate
setCurrentDesign -version 0
setCurrentDesign -version 0
setMode -bs
setMode -bs
Program -p 1 -e -v -loadfpga -defaultVersion 0 
setMode -pff
setMode -pff
