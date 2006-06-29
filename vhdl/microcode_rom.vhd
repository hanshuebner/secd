	--
-- ROMs Using Block RAM Resources.
-- VHDL code for a ROM with registered output (template 1)
--

library ieee;
use ieee.std_logic_1164.all;
use ieee.std_logic_unsigned.all;
use work.microcode_rom_defs.all;

entity microcode_rom is
  port (clk  : in std_logic;
        en   : in std_logic;
        addr : in std_logic_vector(8 downto 0);
        data : out std_logic_vector(27 downto 0));
end microcode_rom;

architecture syn of microcode_rom is

begin

  process (clk)
  begin
    if (clk'event and clk = '1') then
      if (en = '1') then
        data <= microcode_rom_defs.MICROCODE_ROM(conv_integer(addr));
      end if;
    end if;
  end process;

end syn;
