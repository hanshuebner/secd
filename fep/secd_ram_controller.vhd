-- secd_ram_controller.vhd
--
-- Multiplex the external 16 bit SRAM to the 32 bit interface required
-- by the CPU and provide for an 8 bit backside port for the 6809 to
-- read and write SECD memory

library ieee;

use ieee.std_logic_1164.all;
use ieee.numeric_std.all;
use ieee.std_logic_unsigned.all;

entity secd_ram_controller is
  port(
    clk                 : in std_logic;
    reset               : in std_logic;

    -- Internal interface to SECD (16k x 32)
    din32               : in std_logic_vector(31 downto 0);
    dout32              : out std_logic_vector(31 downto 0);
    addr32              : in std_logic_vector(13 downto 0);
    read32_enable       : in std_logic;
    write32_enable      : in std_logic;
    busy8               : out std_logic;

    -- Internal interface to 6809 (64k x 8)
    din8                : in std_logic_vector(7 downto 0);
    dout8               : out std_logic_vector(7 downto 0);
    addr8               : in std_logic_vector(15 downto 0);
    rw8                 : in std_logic;
    cs8                 : in std_logic;
    busy32              : out std_logic;

    -- External interface
    ram_oen          : out std_logic;
    ram_cen          : out std_logic;
    ram_wen          : out std_logic;
    ram_io           : inout std_logic_vector(15 downto 0);
    ram_a            : out std_logic_vector(20 downto 0);
    ram_bhen         : out std_logic;
    ram_blen         : out std_logic
  );
end;

architecture external_ram of secd_ram_controller is

  type state_type is (idle,
                      read32_high, read32_low, write32_high, write32_low,
                      read8, write8,
                      wait_deselect);

  signal state: state_type;

  signal read32_buf : std_logic_vector(31 downto 0);

  signal selected: std_logic;

begin

  secd_ram_controller : process(reset, clk,
                                read32_enable, write32_enable, din32,
                                cs8, rw8, din8,
                                ram_io,
                                selected)

  begin
    if reset = '1' then
      ram_cen <= '1';
      ram_oen <= '1';
      ram_a <= (others => '0');
      ram_io <= (others => 'Z');
      busy8 <= '0';
      busy32 <= '0';
      state <= idle;

    elsif rising_edge(clk) then

      case state is

      when idle =>

        busy8 <= '0';
        busy32 <= '0';
        ram_cen <= '1';
        ram_oen <= '1';
        ram_blen <= '1';
        ram_bhen <= '1';
        ram_io <= (others => 'Z');
        ram_a(1 downto 0) <= "00";

        if cs8 = '1' then

          ram_a(14 downto 0) <= addr8(15 downto 1);
          ram_cen <= '0';
          busy8 <= '1';

          if rw8 = '1' then

            ram_oen <= '0';
            if addr8(0) = '0' then
              ram_blen <= '0';
            else
              ram_bhen <= '0';
            end if;

            state <= read8;

          else

            if addr8(0) = '0' then
              ram_io(7 downto 0) <= din8;
              ram_blen <= '0';
            else
              ram_io(15 downto 8) <= din8;
              ram_bhen <= '0';
            end if;

            state <= write8;

          end if;

        elsif read32_enable = '1' then
          ram_a(14 downto 1) <= addr32;
          ram_blen <= '0';
          ram_bhen <= '0';
          ram_cen <= '0';
          ram_oen <= '0';
          busy32 <= '1';
          state <= read32_low;

        elsif write32_enable = '1' then
          ram_a(14 downto 1) <= addr32;
          ram_blen <= '0';
          ram_bhen <= '0';
          ram_cen <= '0';
          ram_io(15 downto 0) <= din32(15 downto 0);
          busy32 <= '1';
          state <= write32_low;
        end if;

      when read8 =>
        if selected = '1' then
          state <= wait_deselect;
        else
          state <= idle;
        end if;

      when write8 =>
        if selected = '1' then
          state <= wait_deselect;
        else
          state <= idle;
        end if;

      when read32_low =>
        read32_buf(15 downto 0) <= ram_io;
        ram_a(0) <= '1';
        state <= read32_high;

      when read32_high =>
        read32_buf(31 downto 16) <= ram_io;
        if selected = '1' then
          state <= wait_deselect;
        else
          state <= idle;
        end if;

      when write32_low =>
        ram_a(0) <= '1';
        state <= write32_high;

      when write32_high =>
        ram_io(15 downto 0) <= din32(31 downto 16);
        if selected = '1' then
          state <= wait_deselect;
        else
          state <= idle;
        end if;

      when wait_deselect =>

        ram_cen <= '1';
        ram_oen <= '1';
        ram_blen <= '1';
        ram_bhen <= '1';
        ram_io <= (others => 'Z');
        busy8 <= '0';
        busy32 <= '0';

        if selected = '0' then
          state <= idle;
        end if;
      end case;
    end if;
  end process;

  generate_selected : process(cs8, read32_enable, write32_enable)
  begin
    if cs8 = '1' or read32_enable = '1' or write32_enable = '1' then
      selected <= '1';
    else
      selected <= '0';
    end if;
  end process;

  process_port : process(clk, ram_io, state)
  begin
    if falling_edge(clk) then

      case state is
        when write8 | write32_low | write32_high =>
          ram_wen <= '0';

        when read8 =>
          ram_wen <= '1';

          if addr8(0) = '0' then
            dout8 <= ram_io(7 downto 0);
          else
            dout8 <= ram_io(15 downto 8);
          end if;

        when others =>
          ram_wen <= '1';

      end case;

    end if;
  end process;

  dout32 <= read32_buf;
  
end;

