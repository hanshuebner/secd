SetActiveLib -work
#Compiling UUT entity design files
comp "h:\fpga\secd\fep\rxunit3.vhd"

#Compiling WAVES Testbench neccessary files
acom -work secd "$DSN\src\WAVES\rxunit_TB_pins.vhd"
acom -work secd "$ALDEC\DAT\WAVES\waves_objects.vhd"
acom -work secd "$DSN\src\WAVES\rxunit_TB_declaration.vhd"
acom -work secd "$ALDEC\DAT\WAVES\monitor_utilities.vhd"
acom -work secd "$ALDEC\DAT\WAVES\waves_generator.vhd"
acom -work secd "$DSN\src\WAVES\rxunit_TB.vhd"

#Compiling timing configuration
#acom -work secd "$DSN\src\WAVES\"

#Run simulation
asim  TESTBENCH_FOR_rxunit

wave
wave -noreg STIM_RxDat
wave -noreg STIM_Clk
wave -noreg STIM_Reset
wave -noreg STIM_ReadD
wave -noreg STIM_WdFmt
wave -noreg STIM_BdFmt
wave -noreg STIM_RxClk
wave -noreg ACTUAL_FRErr
wave -noreg ACTUAL_ORErr
wave -noreg ACTUAL_PAErr
wave -noreg ACTUAL_DARdy
wave -noreg ACTUAL_DAOut
wave WPL
wave ERR_STATUS

run

#End simulation macro
