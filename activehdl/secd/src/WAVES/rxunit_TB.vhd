-------------------------------------------------------------------------------
--
-- Title       : 
-- Design      : secd
-- Author      : Hans Hübner
-- Company     : .
--
-------------------------------------------------------------------------------
--
-- File        : rxunit_TB.vhd
-- Generated   : Fri Jul  7 11:23:49 2006
-- From        : h:\fpga\secd\activehdl\secd\src\WAVES\rxunit_TB_settings.txt
-- By          : tb_generator.pl ver. ver 1.2s
--
-------------------------------------------------------------------------------
--
-- Description : main Test Bench entity
--
-------------------------------------------------------------------------------

library ieee;
use ieee.std_logic_unsigned.all;
use ieee.std_logic_1164.all;

use IEEE.waves_interface.all;
use WORK.UUT_test_pins.all;
use WORK.waves_objects.all;
use WORK.DESIGN_DECLARATIONS.all;
use WORK.MONITOR_UTILITIES.all;
use WORK.WAVES_GENERATOR.all;

-- User can put library and packages declaration here

entity rxunit_wb is
end rxunit_wb;

architecture TB_ARCHITECTURE of rxunit_wb is

	-- Component declaration of the tested unit
	component rxunit

	port (
		RxDat : in std_logic;
		Clk : in std_logic;
		Reset : in std_logic;
		ReadD : in std_logic;
		WdFmt : in std_logic_vector(2 downto 0);
		BdFmt : in std_logic_vector(1 downto 0);
		RxClk : in std_logic;
		FRErr : out std_logic;
		ORErr : out std_logic;
		PAErr : out std_logic;
		DARdy : out std_logic;
		DAOut : out std_logic_vector(7 downto 0));
	end component;

	-- Internal signals declarations:
	--   stimulus signals (STIM_)for the waveforms mapped into UUT inputs,
	--   observed signals (ACTUAL_) used in monitoring ACTUAL Values of UUT Outputs,
	--   bi-directional signals (BI_DIRECT_) mapped into UUT Inout ports,
	--    the BI_DIRECT_ signals are used as stimulus and also used for monitoring the UUT Inout ports
	signal STIM_RxDat : std_logic;
	signal STIM_Clk : std_logic;
	signal STIM_Reset : std_logic;
	signal STIM_ReadD : std_logic;
	signal STIM_WdFmt : std_logic_vector(2 downto 0);
	signal STIM_BdFmt : std_logic_vector(1 downto 0);
	signal STIM_RxClk : std_logic;
	signal ACTUAL_FRErr : std_logic;
	signal ACTUAL_ORErr : std_logic;
	signal ACTUAL_PAErr : std_logic;
	signal ACTUAL_DARdy : std_logic;
	signal ACTUAL_DAOut : std_logic_vector(7 downto 0);


	-- WAVES signals OUTPUTing each slice of the waves port list
	signal WPL  : WAVES_PORT_LIST;
	signal TAG  : WAVES_TAG;
	signal ERR_STATUS: STD_LOGIC:='L';
	-- Signal END_SIM denotes end of test vectors file
	signal END_SIM : BOOLEAN:=FALSE;

begin

	-- Process that generates the WAVES waveform
	WAVES: WAVEFORM (WPL, TAG);


	-- Processes that convert the WPL values to 1164 Logic Values
	ASSIGN_STIM_RxDat: STIM_RxDat <= WPL.SIGNALS(TEST_PINS'pos(RxDat)+1);


	-- Unit Under Test port map
	UUT: rxunit
	port map(
		 RxDat => STIM_RxDat,
		 Clk => STIM_Clk,
		 Reset => STIM_Reset,
		 ReadD => STIM_ReadD,
		 WdFmt => STIM_WdFmt,
		 BdFmt => STIM_BdFmt,
		 RxClk => STIM_RxClk,
		 FRErr => ACTUAL_FRErr,
		 ORErr => ACTUAL_ORErr,
		 PAErr => ACTUAL_PAErr,
		 DARdy => ACTUAL_DARdy,
		 DAOut => ACTUAL_DAOut);


	-- Process denoting end of test vectors file
	NOTIFY_END_VECTORS: process (TAG)
	begin
		if TAG.len /= 0 then
			if ERR_STATUS='L' then
				report "All vectors passed.";
			elsif ERR_STATUS='1' then
				report "Errors were encountered on the output ports, differences are listed in rxunit_report.log";
			end if;
			END_SIM <= TRUE;
			CLOSE_VECTOR;
			CLOSE_REPORT;
		end if;
	end process;

end TB_ARCHITECTURE;


configuration TESTBENCH_FOR_rxunit of rxunit_wb is
	for TB_ARCHITECTURE
		for UUT : rxunit
			use entity work.rxunit (behaviour);
		end for;
	end for;
end TESTBENCH_FOR_rxunit;
