-- kbug_ram.vhd - Synthesizable model for the KBUG RAM

library ieee;

use ieee.std_logic_1164.all;
use ieee.numeric_std.all;
use ieee.std_logic_unsigned.all;

entity kbug_ram is
  port(
    dout             : out std_logic_vector(7 downto 0);
    din              : in std_logic_vector(7 downto 0);
    addr             : in std_logic_vector(10 downto 0);
    en               : in std_logic;
    we               : in std_logic;
    clk              : in std_logic
  );
end;

architecture internal_ram of kbug_ram is

  type ram_type is array (0 to 2047) of std_logic_vector(7 downto 0);
  signal RAM : ram_type := (others => (others => '0'));

begin
  process (clk)
  begin
    if rising_edge(clk) then
      if en = '1' then
        if we = '1' then
          RAM(conv_integer(addr)) <= din;
        end if;
        dout <= RAM(conv_integer(addr));
      end if;
    end if;
  end process;
end internal_ram;

