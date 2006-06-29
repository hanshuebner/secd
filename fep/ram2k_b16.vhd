library IEEE;
use IEEE.STD_LOGIC_1164.ALL;
use IEEE.STD_LOGIC_ARITH.ALL;
library unisim;
use unisim.all;

entity ram_2k is
  Port (
    clk   : in  std_logic;
    rst   : in  std_logic;
    cs    : in  std_logic;
    rw    : in  std_logic;
    addr  : in  std_logic_vector (10 downto 0);
    rdata : out std_logic_vector (7 downto 0);
    wdata : in  std_logic_vector (7 downto 0)
    );
end ram_2k;

architecture rtl of ram_2k is

  component RAMB16_S9
    generic (
      INIT_00, INIT_01, INIT_02, INIT_03,
      INIT_04, INIT_05, INIT_06, INIT_07,
      INIT_08, INIT_09, INIT_0A, INIT_0B,
      INIT_0C, INIT_0D, INIT_0E, INIT_0F,
      INIT_10, INIT_11, INIT_12, INIT_13,
      INIT_14, INIT_15, INIT_16, INIT_17,
      INIT_18, INIT_19, INIT_1A, INIT_1B,
      INIT_1C, INIT_1D, INIT_1E, INIT_1F,
      INIT_20, INIT_21, INIT_22, INIT_23,
      INIT_24, INIT_25, INIT_26, INIT_27,
      INIT_28, INIT_29, INIT_2A, INIT_2B,
      INIT_2C, INIT_2D, INIT_2E, INIT_2F,
      INIT_30, INIT_31, INIT_32, INIT_33,
      INIT_34, INIT_35, INIT_36, INIT_37,
      INIT_38, INIT_39, INIT_3A, INIT_3B,
      INIT_3C, INIT_3D, INIT_3E, INIT_3F : bit_vector (255 downto 0)
      );

    port (
      do   : out std_logic_vector(7 downto 0);
      dop  : out std_logic_vector(0 downto 0);
      addr : in std_logic_vector(10 downto 0);
      clk  : in std_logic;
      di   : in std_logic_vector(7 downto 0);
      dip : in std_logic_vector(0 downto 0);
      en   : in std_logic;
      ssr  : in std_logic;
      we   : in std_logic
      );
  end component RAMB16_S9;

  signal we : std_logic;
  signal dp : std_logic;

begin

  ROM : RAMB16_S9
    generic map ( 
      INIT_00 => x"A780A610C6C0DF8E104FFE8E81FBADFDB1FDBDFDEEFDDFFDC9FDCFFD61F814F8",
      INIT_01 => x"17431FE4A7D0866AAFDD8C30FB265AE26F0CC67A0217E0DFBF04E08EF9265AA0",
      INIT_02 => x"051774FE8E260517F62A5A19048B0327856D0DC64FD0DF8E7505175FFE8EBE05",
      INIT_03 => x"17408B981F7305175E86092C2081891FF1270D817F846505174605177BFE8E5C",
      INIT_04 => x"201E05177DFE8EF5264FFE8C02300F2780E113FE8E20C0022F60C16705176C05",
      INIT_05 => x"83FE8E310417290417210417190417110417FF041783FE8E3B341FBC2094ADC0",
      INIT_06 => x"ED0317394AAF02295704171705172704174804164104173A0417330417EA0417",
      INIT_07 => x"17ED0417E703173946AF02293B0417FB04170004173948AF0229490417090517",
      INIT_08 => x"0229220417D10417F503173943A70229300417DF0417CE03173944AF02292D04",
      INIT_09 => x"C4A7808A0429060417B50417E303173941A70229140417C30417DD03173942A7",
      INIT_0A => x"03178E0417260417A4A6960417260417211F5F041783FE8E121F2D29EB031739",
      INIT_0B => x"173F866F04170827A4A1A4A7390F260D8117275E81DD271881E12708811128DF",
      INIT_0C => x"24E1AC203406298B031705201F30C0DF8E321F350317BE203F31C22021316C04",
      INIT_0D => x"8E103439623203272704170527E4AC011FF0C4201F0634F0C41000C3101F3901",
      INIT_0E => x"80A610C6E1AE100417F5265A180417B0031780A610C6AF0317E4AEE8031783FE",
      INIT_0F => x"2562AC7B2930342B0317E26FE26FBF20EE265A0104172E8602237E8104252081",
      INIT_10 => x"A0E8E0EB023464E3201F62AE10F125E4AC10A0A7E0AB043464E3201FE8031777",
      INIT_11 => x"3903175003174701171035880317A1FE8E10344C03173F3085031783FE8E3C27",
      INIT_12 => x"AC101A268303173E0317A6FE8E981F6C03178FFE8E2E031764AE77031787FE8E",
      INIT_13 => x"1E29B102173966328C26646C9026656C62AE100B267403178603172B86B325E4",
      INIT_14 => x"173984A73F86A4AFA0A709273F8184A60F271035558DFFFF8E10341A24C0DF8C",
      INIT_15 => x"8D4AAF0427268D1F304AAE431F39FB265A188D08C6E3DF8E104703163F864A03",
      INIT_16 => x"A0A7A0A7A0A7FF8684A7A4A604263F8184A60A24C0DF8C21AE9AFD16E4FD1706",
      INIT_17 => x"F0B714F0B7FF8624F0B7DE86393D3139F7265A0427A1ACA0A608C6E3DF8E1039",
      INIT_18 => x"B68A001720F0B70986FB2B20F0B697001720F0B7D88610F07D16F0B715F0B710",
      INIT_19 => x"F0BFFFFE8E00F0FD5343101F40F0B7108A528D00C08ECA261085F926018520F0",
      INIT_1A => x"0A2A10F07D5F04345F528D20F0B78C8622F0B7018614F0B7FE8610F0B7FF8602",
      INIT_1B => x"341F4AAF00C08E24F0F7DEC63901271C8520F0B604358A20F0265A0435F8265A",
      INIT_1C => x"0F8462A65858585853A6E6E4E754545454A6E6D0DF8E104444444462A636343B",
      INIT_1D => x"013000008E03C614E07F18E07D390435FD265A20C6043439363562E762EA62A7",
      INIT_1E => x"B78C86298D1AE0B70186F92601C518E0F6378D18E0B70F86F6265AF92600008C",
      INIT_1F => x"C08E3901272CC5F02601C518E0F680A71BE0B6052702C5092000C08E228D18E0",
      INIT_20 => x"3981A60117F9265381AD0117E2DF7FDD0117118639FD265A20C63B341F4AAF00",
      INIT_21 => x"0434E46AE46AE4EBE0EBE0E610342129FF001726290234170117F12631813D27",
      INIT_22 => x"738F01173F86B227FFC102355FEB2080A70527E46AE0EB02340C290435FD0017",
      INIT_23 => x"A3E4EC7101171286E4AF0130462562AC4A293034B80017E26F8701161386E2DF",
      INIT_24 => x"EBDA001762AEE70017981F03CB1A0117EBFE8E64E720C6022320008310062762",
      INIT_25 => x"322F01171486C326E4AC62AFCD0017981F53F526646AD7001780A684EB63EB62",
      INIT_26 => x"43A6DF0017CCFE8EA1001648AEEA0017BAFE8EAC0016311FF50017AEFE8E3965",
      INIT_27 => x"AEBE0017B4FE8E80001646AEC90017C0FE8E8B001644AED40017C6FE8E9E0016",
      INIT_28 => x"8EC4A6A00017DCFE8E6A2042A6AA0017D7FE8E742041A6B40017D2FE8E76204A",
      INIT_29 => x"39103561A710343D29098D011F43290F8DBF00172D86121F4E29098D7320E3FE",
      INIT_2A => x"393080032239811D2530816F8D39E0AB04342829078D891F484848483229118D",
      INIT_2B => x"35028D0235103439021A39578003226681072561813937800322468112254181",
      INIT_2C => x"25E46880A608C602345720078B022F3981308B0F840235048D44444444023402",
      INIT_2D => x"8180A6318D391035058D75FE8E10340C20028D390235F1265A458D498D2D8602",
      INIT_2E => x"3439103501A6FA27018584A6E0DFBE10341F207F84048D0627E2DF7D39F82604",
      INIT_2F => x"39103501A70235FA27028584A6E0DFBE12342086008D3902350185E0DF9FA602",
      INIT_30 => x"1007F90431F90315F90223F90139E2DFB7FF86016D84A7118684A70386E0DFBE",
      INIT_31 => x"67FC5041F94D0CFC4CA5F84796F945F4FA447BFA42EBF819F9F818DDF815CFF8",
      INIT_32 => x"00FFFFFFFFB3FAA7F8A7F8A7F8A7F8B3FAA7FA58B3FB558AF953A8F852F2F951",
      INIT_33 => x"414857043E040000000A0D4B04202D20382E31204755422D530000000A0D0000",
      INIT_34 => x"203A524F525245204E492053544942202C042053534150202C04202D20043F54",
      INIT_35 => x"043D53552020043D43502020043D50532020303132333435363704203E3D2004",
      INIT_36 => x"43432020043D422020043D412020043D50442020043D58492020043D59492020",
      INIT_37 => x"000000FFFFFFFFFFFFFFFFFFFFFFFFFFFFFF04315343565A4E4948464504203A",
      INIT_38 => x"300B2784AC1084AF1084EEAA558E10A0D08E84A7F086FB264A80A70F86F0FF8E",
      INIT_39 => x"2DA7D0DF8E10C0DFCE10FDFFB74444444443101F84EFD620ED26A0F08C00F089",
      INIT_3A => x"1084AF10AA558E1084EE2227A0F08C00F08930FB2A4AA66F0C862FA7F0862E6F",
      INIT_3B => x"2EA7D0DF8E10F186D520A5A70F88891F44444444101FD0DF8E1084EFE92684AC",
      INIT_3C => x"8EF32D0C814C80E7A66F0427A6E6211F4F2CE7A66F1420F92A4A0526A6E60C86",
      INIT_3D => x"9F6EC6DF9F6EC4DF9F6EC0DF9F6E62F816E2DFF753F9265A80A7A0A610C6F0FF",
      INIT_3E => x"0822CEDFBC8B300F27FFFF8CCCDFBE49584F4AAF80E64AAE431FCADF9F6EC8DF",
      INIT_3F => x"00FFB2FFC2FFBEFFBAFFB6FFC6FFB2FFC2DF9F6E42EE1F37F16E44AEC4EC1034"
      )

    port map (
      do   => rdata,
      dop(0) => dp,
      addr => addr,
      clk  => clk,
      di   => wdata,
      dip(0) => dp,
      en   => cs,
      ssr  => rst,
      we   => we
      );

  my_ram_2k : process ( rw )
  begin
    we    <= not rw;
  end process;

end architecture rtl;

