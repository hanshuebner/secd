loadProjectFile -file "H:\fpga\secd\default.ipf"
setMode -ss
setMode -sm
setMode -hw140
setMode -spi
setMode -acecf
setMode -acempm
setMode -pff
setMode -bs
setMode -bs
setMode -bs
setMode -pff
setMode -pff
setMode -bs
setMode -pff
setMode -pff
setMode -bs
setMode -bs
setMode -pff
setMode -pff
setMode -bs
setMode -bs
setMode -pff
setMode -pff
setMode -pff
setMode -pff
setCurrentDesign -version 0
setMode -pff
setCurrentDeviceChain -index 0
setCurrentDeviceChain -index 0
setMode -pff
setSubmode -pffserial
setAttribute -configdevice -attr fillValue -value "FF"
setAttribute -configdevice -attr fileFormat -value "mcs"
setAttribute -configdevice -attr dir -value "UP"
setAttribute -configdevice -attr path -value "H:\fpga\secd\/"
setAttribute -configdevice -attr name -value "secd-maisforth.mcs"
generate
setCurrentDesign -version 0
setMode -bs
setMode -bs
Program -p 1 -e -v -loadfpga -defaultVersion 0 
Program -p 1 -e -v -loadfpga -defaultVersion 0 
