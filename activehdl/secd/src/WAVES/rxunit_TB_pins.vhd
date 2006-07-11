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
-- Description : declaration of TEST_PINS package
--
-------------------------------------------------------------------------------
--The TEST_PINS package contains declaration of enumerated type named TEST_PINS.
--This declaration contains one enumerated value for each port
-- find in test vector file: wf.vec
--An order of declared values match the order of ports in test vector file.

package UUT_TEST_PINS is
type TEST_PINS is (
	RxDat);
end UUT_TEST_PINS;
