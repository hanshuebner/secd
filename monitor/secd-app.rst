ASxxxx Assembler V04.10  (Motorola 6809), page 1.
Hexidecimal [16-Bits]



                              1 	; extern	_acia_control
                              2 	; extern	_acia_data
                              3 	.area sysrom
                              4 	.globl _acia_putchar
   000A                       5 _acia_putchar:
   000A 34 40                 6 	pshs	u	;push register set
   000C 32 7F                 7 	leas	-1,s	;subhi: R:s = R:s + -1
   000E E7 5F                 8 	stb	-1,u	;movqi: R:b -> -1,u
   0010                       9 L2:
   0010 F6 E0 00             10 	ldb	_acia_control	;movqi: _acia_control -> R:b
   0013 C4 02                11 	andb	#2	;andqi: R:b &= #2
   0015 5D                   12 	tstb		;tstqi: R:b
   0016 26 02                13 	bne	L3	;length = 2
   0018 20 F6                14 	bra	L2	;length = 2
   001A                      15 L3:
   001A E6 5F                16 	ldb	-1,u	;movqi: -1,u -> R:b
   001C F7 E0 01             17 	stb	_acia_data	;movqi: R:b -> _acia_data
   001F 32 61                18 	leas	1,s	;addhi: R:s = R:s + #1
   0021 35 C0                19 	puls	u,pc	;pop register set
                             20 	.globl _acia_getchar
   0023                      21 _acia_getchar:
   0023 34 40                22 	pshs	u	;push register set
   0025                      23 L5:
   0025 F6 E0 00             24 	ldb	_acia_control	;movqi: _acia_control -> R:b
   0028 C4 01                25 	andb	#1	;andqi: R:b &= #1
   002A 5D                   26 	tstb		;tstqi: R:b
   002B 26 02                27 	bne	L6	;length = 2
   002D 20 F6                28 	bra	L5	;length = 2
   002F                      29 L6:
   002F F6 E0 01             30 	ldb	_acia_data	;movqi: _acia_data -> R:b
   0032 35 C0                31 	puls	u,pc	;pop register set
                             32 	.globl _acia_puts
   0034                      33 _acia_puts:
   0034 34 60                34 	pshs	y,u	;push register set
   0036 32 7E                35 	leas	-2,s	;subhi: R:s = R:s + -2
   0038 AF 5E                36 	stx	-2,u	;movhi: R:x -> -2,u
   003A                      37 L8:
   003A 6D D8 FE             38 	tst	[-2,u]	;tstqi: MEM:[-2,u]
   003D 27 0F                39 	beq	L7	;length = 2
   003F 31 5E                40 	leay	-2,u	;addhi: R:y = R:u + #-2
   0041 AE A4                41 	ldx	,y	;movhi: ,y -> R:x
   0043 E6 84                42 	ldb	,x	;movqi: ,x -> R:b
   0045 30 01                43 	leax	1,x	;addhi: R:x = R:x + #1
   0047 AF A4                44 	stx	,y	;movhi: R:x -> ,y
   0049 BD 00 0A             45 	jsr	_acia_putchar	;CALL: (VOIDmode) _acia_putchar (0 bytes)
   004C 20 EC                46 	bra	L8	;length = 2
   004E                      47 L7:
   004E 32 62                48 	leas	2,s	;addhi: R:s = R:s + #2
   0050 35 E0                49 	puls	y,u,pc	;pop register set
                             50 	; extern	_led
                             51 	.globl _blink
   0052                      52 _blink:
   0052 34 40                53 	pshs	u	;push register set
   0054 32 7F                54 	leas	-1,s	;subhi: R:s = R:s + -1
   0056 6F 5F                55 	clr	-1,u	;movqi: ZERO -> R:-1,u
ASxxxx Assembler V04.10  (Motorola 6809), page 2.
Hexidecimal [16-Bits]



   0058                      56 L11:
   0058 7F E0 E0             57 	clr	_led	;movqi: ZERO -> R:_led
   005B C6 01                58 	ldb	#1	;movqi: #1 -> R:b
   005D F7 E0 E0             59 	stb	_led	;movqi: R:b -> _led
   0060 20 F6                60 	bra	L11	;length = 2
                             61 	; extern	_secd_address_high
                             62 	; extern	_secd_mem
                             63 	.globl _clear_secd_memory
   0062                      64 _clear_secd_memory:
   0062 34 40                65 	pshs	u	;push register set
   0064 32 7C                66 	leas	-4,s	;subhi: R:s = R:s + -4
   0066 8E 00 00             67 	ldx	#0	;movhi: #0 -> R:x
   0069 AF 5E                68 	stx	-2,u	;movhi: R:x -> -2,u
   006B                      69 L14:
   006B AE 5E                70 	ldx	-2,u	;movhi: -2,u -> R:x
   006D 8C 00 FF             71 	cmpx	#255	;cmphi:
   0070 22 29                72 	bhi	L13	;length = 2
   0072 EC 5E                73 	ldd	-2,u	;movhi: -2,u -> R:d
   0074 F7 E1 41             74 	stb	_secd_address_high	;movqi: R:b -> _secd_address_high
   0077 8E 00 00             75 	ldx	#0	;movhi: #0 -> R:x
   007A AF 5C                76 	stx	-4,u	;movhi: R:x -> -4,u
   007C                      77 L17:
   007C AE 5C                78 	ldx	-4,u	;movhi: -4,u -> R:x
   007E 8C 00 FF             79 	cmpx	#255	;cmphi:
   0081 22 10                80 	bhi	L16	;length = 2
   0083 AE 5C                81 	ldx	-4,u	;movhi: -4,u -> R:x
   0085 30 89 E2 00          82 	leax	_secd_mem,x	;addhi: R:x = R:x + #_secd_mem
   0089 6F 84                83 	clr	,x	;movqi: ZERO -> R:,x
   008B AE 5C                84 	ldx	-4,u	;movhi: -4,u -> R:x
   008D 30 01                85 	leax	1,x	;addhi: R:x = R:x + #1
   008F AF 5C                86 	stx	-4,u	;movhi: R:x -> -4,u
   0091 20 E9                87 	bra	L17	;length = 2
   0093                      88 L16:
   0093 AE 5E                89 	ldx	-2,u	;movhi: -2,u -> R:x
   0095 30 01                90 	leax	1,x	;addhi: R:x = R:x + #1
   0097 AF 5E                91 	stx	-2,u	;movhi: R:x -> -2,u
   0099 20 D0                92 	bra	L14	;length = 2
   009B                      93 L13:
   009B 32 64                94 	leas	4,s	;addhi: R:s = R:s + #4
   009D 35 C0                95 	puls	u,pc	;pop register set
                             96 	.globl _lcd_init
   009F                      97 _lcd_init:
   009F 34 40                98 	pshs	u	;push register set
   00A1 35 C0                99 	puls	u,pc	;pop register set
                            100 	; extern	_lcd
                            101 	.globl _lcd_putc
   00A3                     102 _lcd_putc:
   00A3 34 40               103 	pshs	u	;push register set
   00A5 32 7F               104 	leas	-1,s	;subhi: R:s = R:s + -1
   00A7 E7 5F               105 	stb	-1,u	;movqi: R:b -> -1,u
   00A9 E6 5F               106 	ldb	-1,u	;movqi: -1,u -> R:b
   00AB F7 E0 F0            107 	stb	_lcd	;movqi: R:b -> _lcd
   00AE 32 61               108 	leas	1,s	;addhi: R:s = R:s + #1
   00B0 35 C0               109 	puls	u,pc	;pop register set
                            110 	.globl _lcd_puts
ASxxxx Assembler V04.10  (Motorola 6809), page 3.
Hexidecimal [16-Bits]



   00B2                     111 _lcd_puts:
   00B2 34 60               112 	pshs	y,u	;push register set
   00B4 32 7E               113 	leas	-2,s	;subhi: R:s = R:s + -2
   00B6 AF 5E               114 	stx	-2,u	;movhi: R:x -> -2,u
   00B8                     115 L23:
   00B8 6D D8 FE            116 	tst	[-2,u]	;tstqi: MEM:[-2,u]
   00BB 27 0F               117 	beq	L22	;length = 2
   00BD 31 5E               118 	leay	-2,u	;addhi: R:y = R:u + #-2
   00BF AE A4               119 	ldx	,y	;movhi: ,y -> R:x
   00C1 E6 84               120 	ldb	,x	;movqi: ,x -> R:b
   00C3 30 01               121 	leax	1,x	;addhi: R:x = R:x + #1
   00C5 AF A4               122 	stx	,y	;movhi: R:x -> ,y
   00C7 BD 00 A3            123 	jsr	_lcd_putc	;CALL: (VOIDmode) _lcd_putc (0 bytes)
   00CA 20 EC               124 	bra	L23	;length = 2
   00CC                     125 L22:
   00CC 32 62               126 	leas	2,s	;addhi: R:s = R:s + #2
   00CE 35 E0               127 	puls	y,u,pc	;pop register set
                            128 	.globl _program
   00D0                     129 _program:
   00D0 00                  130 	.byte	0
   00D1 00                  131 	.byte	0
   00D2 00                  132 	.byte	0
   00D3 20                  133 	.byte	32
   00D4 01                  134 	.byte	1
   00D5 00                  135 	.byte	0
   00D6 00                  136 	.byte	0
   00D7 20                  137 	.byte	32
   00D8 02                  138 	.byte	2
   00D9 00                  139 	.byte	0
   00DA 00                  140 	.byte	0
   00DB 20                  141 	.byte	32
   00DC 0D                  142 	.byte	13
   00DD 00                  143 	.byte	0
   00DE 00                  144 	.byte	0
   00DF 30                  145 	.byte	48
   00E0 15                  146 	.byte	21
   00E1 00                  147 	.byte	0
   00E2 00                  148 	.byte	0
   00E3 30                  149 	.byte	48
   00E4 00                  150 	.byte	0
   00E5 00                  151 	.byte	0
   00E6 01                  152 	.byte	1
   00E7 00                  153 	.byte	0
   00E8 05                  154 	.byte	5
   00E9 C0                  155 	.byte	-64
   00EA 00                  156 	.byte	0
   00EB 00                  157 	.byte	0
   00EC 01                  158 	.byte	1
   00ED 00                  159 	.byte	0
   00EE 00                  160 	.byte	0
   00EF 30                  161 	.byte	48
   00F0 02                  162 	.byte	2
   00F1 00                  163 	.byte	0
   00F2 00                  164 	.byte	0
   00F3 30                  165 	.byte	48
ASxxxx Assembler V04.10  (Motorola 6809), page 4.
Hexidecimal [16-Bits]



   00F4 00                  166 	.byte	0
   00F5 00                  167 	.byte	0
   00F6 02                  168 	.byte	2
   00F7 00                  169 	.byte	0
   00F8 09                  170 	.byte	9
   00F9 C0                  171 	.byte	-64
   00FA 01                  172 	.byte	1
   00FB 00                  173 	.byte	0
   00FC 00                  174 	.byte	0
   00FD 80                  175 	.byte	-128
   00FE 02                  176 	.byte	2
   00FF 00                  177 	.byte	0
   0100 00                  178 	.byte	0
   0101 C0                  179 	.byte	-64
   0102 02                  180 	.byte	2
   0103 00                  181 	.byte	0
   0104 0C                  182 	.byte	12
   0105 80                  183 	.byte	-128
   0106 01                  184 	.byte	1
   0107 00                  185 	.byte	0
                            186 	.globl _setup_secd_program
   0108                     187 _setup_secd_program:
   0108 34 40               188 	pshs	u	;push register set
   010A 32 7C               189 	leas	-4,s	;subhi: R:s = R:s + -4
   010C 7F E1 41            190 	clr	_secd_address_high	;movqi: ZERO -> R:_secd_address_high
   010F 6F 5F               191 	clr	-1,u	;movqi: ZERO -> R:-1,u
   0111                     192 L26:
   0111 E6 5F               193 	ldb	-1,u	;movqi: -1,u -> R:b
   0113 C1 37               194 	cmpb	#55	;cmpqi:
   0115 22 1C               195 	bhi	L27	;length = 2
   0117 E6 5F               196 	ldb	-1,u	;zero_extendqihi: -1,u -> R:d
   0119 4F                  197 	clra
   011A 1F 01               198 	tfr	d,x	;movhi: R:d -> R:x
   011C E6 89 00 D0         199 	ldb	_program,x	;movqi: _program,x -> R:b
   0120 E7 5E               200 	stb	-2,u	;movqi: R:b -> -2,u
   0122 E6 5F               201 	ldb	-1,u	;zero_extendqihi: -1,u -> R:d
   0124 4F                  202 	clra
   0125 ED 5C               203 	std	-4,u	;movhi: R:d -> -4,u
   0127 E6 5E               204 	ldb	-2,u	;movqi: -2,u -> R:b
   0129 AE 5C               205 	ldx	-4,u	;movhi: -4,u -> R:x
   012B E7 89 E2 00         206 	stb	_secd_mem,x	;movqi: R:b -> _secd_mem,x
   012F 6C 5F               207 	inc	-1,u	;addqi: -1,u ++
   0131 20 DE               208 	bra	L26	;length = 2
   0133                     209 L27:
   0133 C6 FF               210 	ldb	#-1	;movqi: #-1 -> R:b
   0135 F7 E1 41            211 	stb	_secd_address_high	;movqi: R:b -> _secd_address_high
   0138 C6 FF               212 	ldb	#-1	;movqi: #-1 -> R:b
   013A F7 E2 FC            213 	stb	_secd_mem+252	;movqi: R:b -> _secd_mem+252
   013D C6 7F               214 	ldb	#127	;movqi: #127 -> R:b
   013F F7 E2 FD            215 	stb	_secd_mem+253	;movqi: R:b -> _secd_mem+253
   0142 C6 03               216 	ldb	#3	;movqi: #3 -> R:b
   0144 F7 E2 FE            217 	stb	_secd_mem+254	;movqi: R:b -> _secd_mem+254
   0147 7F E2 FF            218 	clr	_secd_mem+255	;movqi: ZERO -> R:_secd_mem+255
   014A 32 64               219 	leas	4,s	;addhi: R:s = R:s + #4
   014C 35 C0               220 	puls	u,pc	;pop register set
ASxxxx Assembler V04.10  (Motorola 6809), page 5.
Hexidecimal [16-Bits]



                            221 	; extern	_secd_status
                            222 	.globl _main
   014E                     223 _main:
   014E 34 40               224 	pshs	u	;push register set
   0150 C6 01               225 	ldb	#1	;movqi: #1 -> R:b
   0152 F7 E1 40            226 	stb	_secd_status	;movqi: R:b -> _secd_status
   0155 BD 01 08            227 	jsr	_setup_secd_program	;CALL: (VOIDmode) _setup_secd_program (0 bytes)
   0158 C6 02               228 	ldb	#2	;movqi: #2 -> R:b
   015A F7 E1 40            229 	stb	_secd_status	;movqi: R:b -> _secd_status
   015D BD 00 52            230 	jsr	_blink	;CALL: (VOIDmode) _blink (0 bytes)
   0160 5F                  231 	clrb		;movqi: ZERO -> R:b
   0161 35 C0               232 	puls	u,pc	;pop register set
