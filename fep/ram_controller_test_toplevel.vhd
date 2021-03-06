-- SECD Front End Processor derived from System09 written by John E. Kent
-- This core adheres to the GNU public license  

library ieee;
use ieee.std_logic_1164.all;
use IEEE.STD_LOGIC_ARITH.ALL;
use IEEE.STD_LOGIC_UNSIGNED.ALL;
use ieee.numeric_std.all;
use work.all;

entity secd_fep_trenz is
  port(
    utmi_clkout      : in  Std_Logic;  -- UTMI Clock input
    utmi_databus16_8 : out Std_Logic;  -- UTMI configuration input

    reset_sw    : in  Std_logic;  -- Master Reset input (active low)

    -- PS/2 Keyboard
    ps2_clk1    : inout Std_logic;
    ps2_data1   : inout Std_Logic;

    -- Uart Interface
    fpga_rxd    : in  Std_Logic;
    fpga_txd    : out Std_Logic;
    fpga_cts    : in  Std_Logic;
    fpga_rts    : out Std_Logic;

    -- CRTC output signals
    vsync_b     : out Std_Logic;
    hsync_b     : out Std_Logic;
    fpga_b      : out Std_Logic_Vector(2 downto 0);
    fpga_g      : out Std_Logic_Vector(2 downto 0);
    fpga_r      : out Std_Logic_Vector(2 downto 0);

    -- LEDS & Switches
    mm_led      : out Std_Logic;
    led         : out Std_Logic_Vector(3 downto 0);

    joy_down    : in Std_Logic;
    joy_fire    : in Std_Logic;
    joy_left    : in Std_Logic;
    joy_right   : in Std_Logic;
    joy_up      : in Std_Logic;

    -- LCD Display
    lcd_e       : out Std_Logic;
    lcd_rw      : out Std_Logic;
    lcd_rs      : out Std_Logic;
    lcd_d       : out Std_Logic_Vector(3 downto 0);

    -- Audio
    aud_out     : out std_logic_vector(4 downto 1);

    -- Memory interface
    ram_a       : out std_logic_vector(20 downto 0);
    ram_io      : inout std_logic_vector(15 downto 0);
    ram_bhen    : out std_logic;
    ram_blen    : out std_logic;
    ram_cen     : out std_logic;
    ram_oen     : out std_logic;
    ram_wen     : out std_logic;

    -- Compact flash
    cf_reset    : out std_logic;
    cf_irq      : in std_logic;
    cf_iord     : out std_logic;
    cf_iowr     : out std_logic;
    cf_wait     : in std_logic;
    cf_dasp     : in std_logic;
    cf_pdiag    : in std_logic;
    cf_cd1      : in std_logic;
    cf_cd2      : in std_logic;
    iois16      : in std_logic;
    cf_oe       : out std_logic;
    cf_pwr_en   : out std_logic;
    cf_cs0      : out std_logic;
    cf_cs1      : out std_logic;
    cf_we       : out std_logic;
    cf_rew      : out std_logic
    );
end secd_fep_trenz;

-------------------------------------------------------------------------------
-- Architecture for System09
-------------------------------------------------------------------------------
architecture rtl of secd_fep_trenz is

  -----------------------------------------------------------------------------
  -- Configurable components
  -----------------------------------------------------------------------------

  component user_ram
    port (
      clk: IN std_logic;
      din: IN std_logic_VECTOR(7 downto 0);
      addr: IN std_logic_VECTOR(13 downto 0);
      en: IN std_logic;
      we: IN std_logic;
      dout: OUT std_logic_VECTOR(7 downto 0)
      );
  end component;

  -----------------------------------------------------------------------------
  -- Signals
  -----------------------------------------------------------------------------

  -- BOOT ROM
  signal rom_cs        : Std_logic;
  signal rom_data_out  : Std_Logic_Vector(7 downto 0);

  -- RAM
  signal int_ram_we    : std_logic;

  -- We have two internal RAM areas.  One for the KBUG9 monitor mapped
  -- from $F000 to $F7FF (2K) and a user area mapped from $0000 (16K)
  signal user_ram_en   : std_logic;
  signal kbug_ram_en   : std_logic;
  signal user_ram_dout : std_logic_vector(7 downto 0);
  signal kbug_ram_dout : std_logic_vector(7 downto 0);

  -- UART Interface signals
  signal uart_data_out : Std_Logic_Vector(7 downto 0);  
  signal uart_cs       : Std_Logic;
  signal uart_irq      : Std_Logic;
  signal baudclk       : Std_Logic;
  signal DCD_n         : Std_Logic;
  signal RTS_n         : Std_Logic;
  signal CTS_n         : Std_Logic;

  -- keyboard port
  signal keyboard_data_out : std_logic_vector(7 downto 0);
  signal keyboard_cs       : std_logic;
  signal keyboard_irq      : std_logic;

  -- CPU Interface signals
  signal cpu_clk      : Std_Logic;
  signal cpu_rw       : std_logic;
  signal cpu_vma      : std_logic;
  signal cpu_halt     : std_logic;
  signal cpu_hold     : std_logic;
  signal cpu_firq     : std_logic;
  signal cpu_irq      : std_logic;
  signal cpu_nmi      : std_logic;
  signal cpu_addr     : std_logic_vector(15 downto 0);
  signal cpu_data_in  : std_logic_vector(7 downto 0);
  signal cpu_data_out : std_logic_vector(7 downto 0);

  -- Video Display Unit
  signal vdu_cs       : std_logic;
  signal vdu_data_out : std_logic_vector(7 downto 0);

  -- VGA output signals (distributed to VGA DAC)
  signal red          : std_logic;
  signal green        : std_logic;
  signal blue         : std_logic;

  -- System Clock as generated by the clock synthesis module
  signal sysclk       : std_logic;

  attribute period : string;
  attribute period of sysclk : signal is "20 ns";

  -- System Reset (generated by key press)
  signal reset        : std_logic;

  -- LCD register select
  signal lcd_cs       : std_logic;

  -- LED register select
  signal led_cs       : std_logic;
  signal led_reg      : std_logic_vector(7 downto 0) := (others => '0');

  -- Joystick buffer
  signal joystick     : std_logic_vector(7 downto 0);

  -- Baud rate generator register
  signal baud_count   : std_logic_vector(5 downto 0) := (others => '0');

  -- LED Flasher
  signal blink_count  : std_logic_vector(25 downto 0) := (others => '0');
  
  -- SECD interface
  signal secd_button           : std_logic := '0';
  signal secd_stop             : std_logic := '1';
  signal secd_stopped          : std_logic;
  signal secd_state            : std_logic_vector(1 downto 0);
  signal secd_ram_addr8        : std_logic_vector(15 downto 0) := (others => '0');
  signal secd_ram_din8         : std_logic_vector(7 downto 0);
  signal secd_ram_addr_high_cs : std_logic := '0';
  signal secd_ram_addr_low_cs  : std_logic := '0';
  signal secd_ram_cs           : std_logic := '0';
  signal secd_control_cs       : std_logic := '0';

  -- SECD RAM Controller interface
  signal secd_ram_clk           : std_logic;
  signal secd_ram_busy8         : std_logic;
  signal secd_ram_busy32        : std_logic;

  -- Interface signals for SECD
  signal secd_ram_din32         : std_logic_vector(31 downto 0);
  signal secd_ram_dout32        : std_logic_vector(31 downto 0);
  signal secd_ram_addr32        : std_logic_vector(13 downto 0);
  signal secd_ram_read32        : std_logic;
  signal secd_ram_write32       : std_logic;

  -- Interface signals for 6809
  signal secd_ram_dout8         : std_logic_vector(7 downto 0);

begin

  -----------------------------------------------------------------
  --
  -- CPU09 CPU core
  --
  -----------------------------------------------------------------

  my_cpu : entity cpu09 port map (    
    clk	      => cpu_clk,
    rst       => reset,
    rw	      => cpu_rw,
    vma       => cpu_vma,
    address   => cpu_addr(15 downto 0),
    data_in   => cpu_data_in,
    data_out  => cpu_data_out,
    halt      => cpu_halt,
    hold      => cpu_hold,
    irq       => cpu_irq,
    nmi       => cpu_nmi,
    firq      => cpu_firq
    );

  ----------------------------------------
  --
  -- Block RAM Monitor ROM
  --
  ----------------------------------------

  my_mon_rom : entity mon_rom port map (
    clk   => cpu_clk,
    cs    => rom_cs,
    addr  => cpu_addr(10 downto 0),
    rdata => rom_data_out
    );

  -----------------------------------------------------------------------------
  --
  -- Internal RAM (Xilinx Block RAM, 16k)
  --
  -----------------------------------------------------------------------------

  my_user_ram : user_ram port map (
    clk   => cpu_clk,
    en    => user_ram_en,
    we    => int_ram_we,
    addr  => cpu_addr(13 downto 0),
    din   => cpu_data_out,
    dout  => user_ram_dout
    );

  -----------------------------------------------------------------------------
  --
  -- KBUG RAM (Xilinx Block RAM, 2k)
  --
  -----------------------------------------------------------------------------

  my_kbug_ram : entity kbug_ram port map (
    clk  => cpu_clk,
    en   => kbug_ram_en,
    we   => int_ram_we,
    addr => cpu_addr(10 downto 0),
    din  => cpu_data_out,
    dout => kbug_ram_dout
    );

  -----------------------------------------------------------------
  --
  -- Open Cores Mini UART
  --
  -----------------------------------------------------------------

  my_uart  : entity miniUART port map (
    clk	      => cpu_clk,
    rst       => reset,
    cs        => uart_cs,
    rw        => cpu_rw,
    irq       => uart_irq,
    Addr      => cpu_addr(0),
    Datain    => cpu_data_out,
    DataOut   => uart_data_out,
    RxC       => baudclk,
    TxC       => baudclk,
    RxD       => fpga_rxd,
    TxD       => fpga_txd,
    DCD_n     => dcd_n,
    CTS_n     => fpga_cts,
    RTS_n     => fpga_rts
    );

  ----------------------------------------
  --
  -- PS/2 Keyboard
  --
  ----------------------------------------

  my_keyboard : entity keyboard port map(
    clk          => cpu_clk,
    rst          => reset,
    cs           => keyboard_cs,
    rw           => cpu_rw,
    addr         => cpu_addr(0),
    data_in      => cpu_data_out,
    data_out     => keyboard_data_out(7 downto 0),
    irq          => keyboard_irq,
    kbd_clk      => ps2_clk1,
    kbd_data     => ps2_data1
    );

  ----------------------------------------
  --
  -- Video Display Unit instantiation
  --
  ----------------------------------------

  my_vdu : entity vdu port map(

    -- Control Registers
    vdu_clk_in    => sysclk,            -- 50 Mhz pixel clock input
    cpu_clk_out   => cpu_clk,           -- 12.5 Mhz CPU clock output
    ram_clk_out   => secd_ram_clk,      -- 25 Mhz RAM clock output
    vdu_rst       => reset,
    vdu_cs        => vdu_cs,
    vdu_rw        => cpu_rw,
    vdu_addr      => cpu_addr(2 downto 0),
    vdu_data_in   => cpu_data_out,
    vdu_data_out  => vdu_data_out,

    -- vga port connections
    vga_red_o     => red,
    vga_green_o   => green,
    vga_blue_o    => blue,
    vga_hsync_o   => hsync_b,
    vga_vsync_o   => vsync_b
    );

  ----------------------------------------
  --
  -- Clock Synthesis instantiation
  --
  ----------------------------------------

  my_clock_synthesis : entity clock_synthesis port map (
    clkin_in        => utmi_clkout,
    clkfx_out       => sysclk,
    locked_out      => open);
  
  ----------------------------------------
  --
  -- SECD CPU instantiation
  --
  ----------------------------------------

  my_secd_system : entity secd_system port map (
    clk         => cpu_clk,
    reset       => reset,
    button      => secd_button,
    ram_read    => secd_ram_read32,
    ram_in      => secd_ram_dout32,
    ram_write   => secd_ram_write32,
    ram_out     => secd_ram_din32,
    ram_a       => secd_ram_addr32,
    ram_busy    => secd_ram_busy8,
    stop_input  => secd_stop,
    stopped     => secd_stopped,
    state       => secd_state
    );

  ----------------------------------------
  --
  -- SECD RAM Controller instantiation
  --
  ----------------------------------------

  my_secd_ram : entity secd_ram_controller port map (
    clk                 => cpu_clk,
    reset 		=> reset,
    busy8 		=> secd_ram_busy8,
    busy32 		=> secd_ram_busy32,

    -- SECD interface
    din32               => secd_ram_din32,
    dout32              => secd_ram_dout32,
    addr32              => secd_ram_addr32,
    read32_enable       => secd_ram_read32,
    write32_enable      => secd_ram_write32,

    -- 6809 interface
    din8                => secd_ram_din8,
    dout8               => secd_ram_dout8,
    addr8               => secd_ram_addr8,
    cs8			=> secd_ram_cs,
    rw8			=> cpu_rw,

    -- external interface
    ram_oen 		=> ram_oen,
    ram_cen 		=> ram_cen,
    ram_wen 		=> ram_wen,
    ram_io 		=> ram_io,
    ram_a 		=> ram_a,
    ram_bhen 		=> ram_bhen,
    ram_blen		=> ram_blen
    );

  ----------------------------------------------------------------------
  --
  -- Process to decode memory map
  --
  ----------------------------------------------------------------------

  mem_decode : process( cpu_clk, reset,
                        cpu_addr, cpu_rw, cpu_vma,
                        rom_data_out,
                        user_ram_dout, kbug_ram_dout,
                        uart_data_out,
                        keyboard_data_out,
                        joystick,
                        vdu_data_out,
                        cpu_data_out,
                        secd_state, secd_stopped, secd_ram_dout8, secd_ram_addr8 )

  begin
    user_ram_en      <= '0';
    kbug_ram_en      <= '0';
    rom_cs           <= '0';
    uart_cs          <= '0';
    keyboard_cs      <= '0';
    vdu_cs           <= '0';
    lcd_cs           <= '0';
    led_cs           <= '0';
    cpu_data_in      <= X"00";

    secd_control_cs       <= '0';
    secd_ram_cs           <= '0';
    secd_ram_addr_high_cs <= '0';
    secd_ram_addr_low_cs  <= '0';

    case cpu_addr(15 downto 11) is

      -- Monitor ROM - $F800 - $FFFF
      when "11111" => -- $F800 - $FFFF
        cpu_data_in     <= rom_data_out;
        rom_cs          <= cpu_vma;              -- read  ROM

      -- IO Devices - $E000 - $E7FF
      when "11100" =>

        case cpu_addr(10 downto 8) is

          -- Real I/O $E000 - $E0FF
          when "000" =>
            case cpu_addr(7 downto 4) is

              -- UART / ACIA $E000
              when X"0" =>
                cpu_data_in <= uart_data_out;
                uart_cs     <= cpu_vma;

              -- Keyboard port $E010 - $E01F
              when X"1" =>
                cpu_data_in <= keyboard_data_out;
                keyboard_cs <= cpu_vma;

              -- VDU port $E020 - $E02F
              when X"2" =>
                cpu_data_in <= vdu_data_out;
                vdu_cs      <= cpu_vma;

              -- Joystick $E0D0 (read only)
              when X"D" =>
                if cpu_addr(3 downto 0) = "0000" then
                  cpu_data_in <= joystick;
                end if;

              -- LED $E0E0 (write only)
              when X"E" =>
                if cpu_addr(3 downto 0) = "0000" then
                  led_cs <= cpu_vma;
                end if;

              -- LCD Display $E0F0 (write only)
              when X"F" =>
                if cpu_addr(3 downto 0) = "0000" then
                  lcd_cs <= cpu_vma;
                end if;

              when others =>
                null;
            end case;

          -- SECD Control registers - $E100
          when "001" =>

            case cpu_addr(3 downto 0) is

              -- $E140 -> SECD Status
              when X"0" =>
                secd_control_cs         <= cpu_vma;
                cpu_data_in(0)          <= secd_stopped;
                cpu_data_in(2 downto 1) <= secd_state;

              -- $E141 -> SECD Address Low
              when X"1" =>
                secd_ram_addr_low_cs    <= cpu_vma;
                cpu_data_in             <= secd_ram_addr8(7 downto 0);

              -- $E142 -> SECD Address High
              when X"2" =>
                secd_ram_addr_high_cs   <= cpu_vma;
                cpu_data_in             <= secd_ram_addr8(15 downto 8);

              -- $E143 -> SECD DATA
              when X"3" =>
                secd_ram_cs             <= cpu_vma;
                cpu_data_in             <= secd_ram_dout8;

              when others =>
                null;

            end case;

          when others =>
            null;

        end case;

      -- Everything else is RAM
      when others =>

        if cpu_addr(15 downto 11) = "11110" then
          cpu_data_in <= kbug_ram_dout;
          kbug_ram_en <= cpu_vma;

        elsif cpu_addr(15 downto 14) = "00" then
          cpu_data_in <= user_ram_dout;
          user_ram_en <= cpu_vma;
        else
          cpu_data_in <= "00000000";
        end if;
    end case;
  end process;

--
-- Interrupts and other bus control signals
--
  interrupts : process( reset_sw, uart_irq, keyboard_irq, reset, joy_up )
  begin
    reset     <= not reset_sw; -- CPU reset is active high
    cpu_irq   <= keyboard_irq;
    cpu_nmi   <= not joy_up;
    cpu_firq  <= uart_irq;
    cpu_halt  <= '0';
  end process;

--
-- Baud rate clock
-- 50 MHz / 54 = ~921.6 KHz (57600 * 16)
--
  my_baud: process( sysclk )
  begin
    if(sysclk'event and sysclk = '0') then
      if( baud_count = 53 )	then
        baud_count <= "000000";
        baudclk <= '0';
      else
        baud_count <= baud_count + 1;
        if baud_count = 26 then
          baudclk <= '1';
        else
          baudclk <= baudclk;
        end if;
      end if;			 
    end if;
  end process;

  --
  -- LCD write register
  --
  lcd_control : process(lcd_cs, cpu_clk, cpu_data_out)
  begin
    if falling_edge(cpu_clk) then
      if lcd_cs = '1' and cpu_rw = '0' then
        lcd_d     <= cpu_data_out(3 downto 0);
        lcd_e     <= cpu_data_out(4);
        lcd_rw    <= cpu_data_out(5);
        lcd_rs    <= cpu_data_out(6);
      end if;
    end if;
  end process;

  --
  -- LED write register
  --
  led_control : process(led_reg, led_cs, cpu_clk, cpu_data_out)
  begin
    if falling_edge(cpu_clk) then
      if led_cs = '1' and cpu_rw = '0' then
        led_reg(3 downto 0) <= cpu_data_out(3 downto 0);
      else
        led_reg <= led_reg;
      end if;
    end if;

    led <= led_reg(3 downto 0);
  end process;

  -- SECD control register
  --
  secd_control : process(secd_control_cs, cpu_clk, cpu_data_out)
  begin
    if falling_edge(cpu_clk) then
      if secd_control_cs = '1' and cpu_rw = '0' then
        secd_stop   <= cpu_data_out(0);
        secd_button <= cpu_data_out(1);
      end if;
    end if;
  end process;

  --
  -- SECD RAM Adressing
  --

  secd_ram_addressing_low : process(cpu_clk, cpu_rw, cpu_data_out, secd_ram_addr_low_cs)
  begin
    if falling_edge(cpu_clk) then
      if cpu_rw = '0' and secd_ram_addr_low_cs = '1' then
        secd_ram_addr8(7 downto 0) <= cpu_data_out;
      end if;
    end if;
  end process;

  secd_ram_addressing_high : process(cpu_clk, cpu_rw, cpu_data_out, secd_ram_addr_high_cs)
  begin
    if falling_edge(cpu_clk) then
      if cpu_rw = '0' and secd_ram_addr_high_cs = '1' then
        secd_ram_addr8(15 downto 8) <= cpu_data_out;
      end if;
    end if;
  end process;

  secd_ram_write_latch : process(cpu_clk, cpu_rw, secd_ram_cs, cpu_data_out)
  begin
    if falling_edge(cpu_clk) then
      if cpu_rw = '0' and secd_ram_cs = '1' then
        secd_ram_din8 <= cpu_data_out;
      end if;
    end if;
  end process;

  --
  -- Joystick register
  --
  read_joystick : process(cpu_clk, joy_up, joy_right, joy_down, joy_left, joy_fire)
  begin
    if rising_edge(cpu_clk) then
      joystick(0) <= joy_up;
      joystick(1) <= joy_right;
      joystick(2) <= joy_down;
      joystick(3) <= joy_left;
      joystick(4) <= joy_fire;
      joystick(7 downto 5) <= (others => '0');
    end if;
  end process;
  
--
-- LED Flasher
--
  my_led_flasher: process( sysclk, reset, blink_count )
  begin
    if reset = '1' then
      blink_count <= (others => '0');
    elsif rising_edge(sysclk) then
      blink_count <= blink_count + 1;
    end if;

    mm_led <= blink_count(25);

  end process;

-- Set UART DCD to always true
  DCD_n <= '0';

--
-- Feed RGB DAC
--
  fpga_r(0) <= red;
  fpga_r(1) <= red;
  fpga_r(2) <= red;
  fpga_g(0) <= green;
  fpga_g(1) <= green;
  fpga_g(2) <= green;
  fpga_b(0) <= blue;
  fpga_b(1) <= blue;
  fpga_b(2) <= blue;

  -- set USB PHY to 16 bit mode so that it generates a 30 Mhz Clock
  utmi_databus16_8 <= '1';

  aud_out <= (others => '0');
  int_ram_we <= not cpu_rw;

  cf_cs0 <= cpu_rw;
  cf_cs1 <= secd_ram_cs;
  cf_we <= secd_ram_busy8;

end;

