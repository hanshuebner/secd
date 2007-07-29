\ dec2005 -*- Forth -*-


<----   cras601 -- AN -- 12jul2005

  -- Herordening en vernieuwing van de code in de cross assembler.

 Indeling:
  1. Hulpwoordjes
  2. Doers
  3. Multi-creating (nieuw)
  4. De assemblercommando's (alleen deze komen in META)

 Verder:

 - Losse DOES-delen, zoals in de Target assembler.
 - CREATING - Stroomlijning van groepen gelijksoortige definities.
 - Compiler security voor IF, ELSE, enz.
 - Alle ELSEs zijn "wegbezuinigd".
 - MODE is nu een VALUE
 - INITMODE is toegevoegd in ?ADRERR (nu ?ILLEGAL).
 - naamswijzigingen  voor de doers van opcodes. DONEG DOSEX DOBRA DOBEQ etc.
 
 Over een  Target assembler
 -------------------------

 De headerbouwer (onderdeel van CREATE) in de Metacompiler
 is nu zo aangepast dat naamgenoten een Homlink krijgen.
 De Metacompiler heeft zelf geen ZOEKmethode die daar rekening
 mee houdt, bij naamgenoten vindt hij altijd de nieuwste.

 # in assembler levert geen problemen op, want de Forth # speelt
in de target code verder geen rol.

\ (AN)
---->

\ MAIS crosassembler voor gebruik in metacompiler  FvdM
\ CopyRight (c) 1993  Bradforf J. Rodriguez
\ Copyright (c) 2003, 2004 HCC Forth GG
\
\ CVS identificatie
\ $Id: crossasm.f,v 1.1 2004/09/16 20:16:56 Administrator Exp $
\
\ CVS Changelog
\ $Log: crossasm.f,v $
\ Revision 1.1  2004/09/16 20:16:56  Administrator
\ Eerste entry in CVS op 16-9-2004  (lokale CVS repository).
\ RCS wordt nu niet langer door mij voor dit project gebruikt
\ Frans van der Markt
\
\
\
\ Versie 5   28-7-2004     adresberekening met CELLS ipv constante waarde (2)
\            15-8-2004     6 ## ( D) etc. vervangen door REG D etc. 
\
\  6809 assembler: utilities                ( 01 feb 93 bjr)
\
\ @ C@ ! C! , C,       work in the host-address
\ xC, x, xC!           work in the target address space during metacompiling

FORTH DEFINITIONS
ANEW -CRAS
HEX \ Until the end



\ -----------------  hulpwoordjes --------------------
: 8BIT?   -80 80 WITHIN ; \ [-80,7F)
: 5BIT?   -10 10 WITHIN ; \ [-10,0F)
: BYTESWAP ( x1 -- x2 ) \ byte swap on 16-bits value
   DUP   FF AND 8 LSHIFT  \ lo>hi
   SWAP  8 RSHIFT FF AND  \ hi>lo
   OR ;
30 VALUE MODE \ adressing mode: 0=immed, 10=direct, 20=indexed, 30=extended
: INITMODE ( -- ) 30 TO MODE ; \ Default value before starting an instruction
: ?ILLEGAL ( flag -- )  0= IF } INITMODE DECIMAL TRUE ABORT" Illegal addressing mode " ;
: INDEXREG ( regnr postbyte1 -- postbyte2 )
   20 TO MODE
   SWAP  1- 3 OVER U< ?ILLEGAL \ must be x,y,u, or s 
   5 LSHIFT OR ;               \ put reg # in postbyte


CREATE (REG
  8 ALLOT  S" ,ABDXYUS" (REG SWAP MOVE
  0 C, 2 C, 4 C, 6 C, 10 C, 20 C, 40 C, 40 C, ALIGN


: SCAN ( a n ch -- a2 n2 )    \ find ch in string a,n.
       \ ch is first char of reststring a2,n2 or n2=0
  >R
  BEGIN                         ( a n   R: ch )
        DUP           WHILE     ( a n )
        OVER C@ R@ <> WHILE     \ no match?
        1 /STRING               ( a+ n- )
  AGAIN               THEN THEN
  R> DROP ;


: >REGCODE ( ch -- regcode)
   [CHAR] Z OVER < BL AND -    \ maak hoofdletter
   8 TUCK (REG 2SWAP           \ 8 (REG 8 CH
   SCAN IF + C@ }
   TRUE ABORT" Registerlist?"  ;



: +MODE ( operand1 -- operand2 )  \ change 5x to 0x,  >> DOGENOP
   MODE +  DUP 0F0 AND 50 = IF 0F AND THEN ;
: PCREL ( operand postbyte -- )  \ PC relative  >> INDEXED
   SWAP HERE 2 + -  DUP 8BIT?    \ Relative offset 8 bit?
      IF  SWAP 0FE AND xC, xC, } \ Postbyte + offset8
   1-  SWAP xC, x, ;             \ Postbyte + offset16
: COFSET ( operand postbyte -- ) \ Constant offset  >> INDEXED
   OVER 0= IF 0F0 AND 4 OR xC, DROP }  \ no offset
   OVER 5BIT? OVER 10 AND 0=   ( 5bit and no indirection? )
   AND IF 60 AND SWAP 1F AND OR xC, }  \  5 bit offset
   OVER 8BIT? IF 0FE AND xC, xC, }     \  8 bit offset
   xC, x, ;                            \ 16 bit offset
: INDEXED ( operand? postbyte -- )  \ >> DOGENOP DOLEAOP
   DUP 8F AND           \ check postbyte for modes with operands
      DUP 89 = IF DROP  COFSET  }   \ Constant offset
      DUP 8D = IF DROP  PCREL   }   \ PC relative
      DUP 8F = IF DROP  xC, x,  }   \ Extended indirect
                  DROP  xC, ;       \ Simple modes: postbyte only
: IMMED ( operand opcode-pfa+ -- ) \ >> DOGENOP
   C@ 1- S>D ?ILLEGAL  \ 0    Test immedsize
   IF x, }             \ 2    Immediate operand16
   xC, ;               \ 1    Immediate operand8
: @+ ( adr -- adr+ x ) DUP CELL+ SWAP @ ;
: GENADR  ( adr+ -- ) \ General address instructions
   MODE INITMODE
   DUP  0 = IF DROP  IMMED         }   \ Immediate
   DUP 10 = IF DROP  DROP xC,      }   \ Direct
   DUP 20 = IF DROP  DROP INDEXED  }   \ Indexed
   DUP 30 = IF DROP  DROP x,       }   \ Extended
   ?ILLEGAL ;
<----
 Stack action of general addressing instructions
 (1) immediate, direct, extended:                operand --
 (2) all indexed except (3):                    postbyte --
 (3) const.offset, PC, extended indir: operand postbyte --
---->



\ ==================== de losse DOERS (AN) =====================
: DOSEX   DOES> C@ xC, INITMODE ; \ Lay 1 byte \ Inherent instructions
: DOSWI2  DOES> @ x, INITMODE ;   \ Lay cell \ Inherent instructions
: DOCWAI  ( operand -- )          \ 8 bit \ Immediate instructions
          DOES> MODE ?ILLEGAL C@ xC, xC, INITMODE ;
: DONEG   DOES> COUNT +MODE xC, GENADR ;  \ 2x 8 bit in body
: DOLDY   DOES> @+ +MODE x, GENADR ;      \ CELL & 8 bit in body
: DOEXG   DOES> C@ xC,  SWAP 10 * + xC, INITMODE ;  \ 8 bit in body, EXG and TFR
: DOLEA   DOES> MODE 20 - ?ILLEGAL   C@ xC, INDEXED INITMODE ;   \ 8 bit in body
: DOBEQ         \ 8 bit in body \ Conditional branches
   DOES> C@  SWAP HERE 2 + -    \ Distance
   INITMODE  DUP 8BIT?
   IF  SWAP xC, xC, }           \ 8 bit
   10 xC, SWAP xC, 2 - x, ;     \ 16 bit
: DOBRA          \ CELL in body \ Unconditional branches
   DOES>   @  SWAP HERE 2 + -   \ distance
   INITMODE
   DUP 8BIT?  IF  SWAP BYTESWAP xC, xC, } \ 8 bit: use short opcode
   SWAP xC, 1- x,  ;                      \ 16 bit: use long opcode
: DOKON DOES> C@ ;        \ 8 bit in body \ Conditions
: DO-)   DOES>  C@ INDEXREG ;             \ 8 bit in body \ Modes


\ ==================== multi-creating (AN) ================
\ Groepsgewijs woorden definiëren. \ -1 fungeert als afsluiter.
\ Bedenk: HX leest een getal (woord) uit de invoerstroom.

: CREATING1  ( doertoken -- )  \ 8 bit in body
  >R  BEGIN  POSTPONE HX  -1 OVER <>
  WHILE  CREATE R@ EXECUTE C, ALIGN  REPEAT R> 2DROP ;
: CREATING2  ( doertoken -- )  \ cell in body
  >R  BEGIN  POSTPONE HX  -1 OVER <>
  WHILE  CREATE R@ EXECUTE ,  REPEAT R> 2DROP ;
: CREATING11 ( doertoken -- ) \ Tweemaal 8 bit in body
  >R  BEGIN  POSTPONE HX  -1 OVER <>
  WHILE  POSTPONE HX CREATE R@ EXECUTE C, C, ALIGN
  REPEAT R> 2DROP ;
: CREATING21 ( doertoken -- ) \ cell & 8 bit in body
  >R  BEGIN  POSTPONE HX  -1 OVER <>
  WHILE  POSTPONE HX CREATE R@ EXECUTE , C, ALIGN
  REPEAT R> 2DROP ;

: SEX:  ['] DOSEX   CREATING1 ;  \ Inherent Addressing, 8
: SWI2: ['] DOSWI2  CREATING2 ;  \ Inherent Addressing, 16
: CWAI: ['] DOCWAI  CREATING1 ;  \ Immediate, 8
: NEG:  ['] DONEG   CREATING11 ; \ General instructions, 8&8 
: LDY:  ['] DOLDY   CREATING21 ; \ General instructions, 16&8 
: EXG:  ['] DOEXG   CREATING1 ;  \ TFR and EXG, 8
: LEA:  ['] DOLEA   CREATING1 ;  \ LEA-instructions, 8
: BEQ:  ['] DOBEQ   CREATING1 ;  \ Conditional branches, 8
: BRA:  ['] DOBRA   CREATING2 ;  \ Unconditional Branches, 16
: KON:  ['] DOKON   CREATING1 ;  \ Constants, Registers, 8
: -):   ['] DO-)    CREATING1 ;  \ Simple Indexed Modes, 8



META DEFINITIONS \ <<<<<<<<<<<<<<<<<<<<<<

\ -------- De assemblerwoordjes ------

\ Zet geen commentaren binnen in een lijst! (bijv. tussen NEG: en -1)

NEG:
0  40 NEG                              0  43 COM
0  44 LSR                  0  46 ROR   0  47 ASR
0  48 ASL
0  48 LSL    0  49 ROL    0  4A DEC
0  4C INC    0  4D TST    0  4E JMP   0  4F CLR
1  80 SUBA   1  81 CMPA   1  82 SBCA  2  83 SUBD
1  84 ANDA   1  85 BITA   1  86 LDA   0  87 STA
1  88 EORA   1  89 ADCA   1  8A ORA   1  8B ADDA
2  8C CMPX   0  8D JSR    2  8E LDX   0  8F STX
1 0C0 SUBB   1 0C1 CMPB   1 0C2 SBCB  2 0C3 ADDD
1 0C4 ANDB   1 0C5 BITB   1 0C6 LDB   0 0C7 STB
1 0C8 EORB   1 0C9 ADCB   1 0CA ORB   1 0CB ADDB
2 0CC LDD    0 0CD STD    2 0CE LDU   0 0CF STU   -1

LDY:
2 1083 CMPD  2 108C CMPY  2 108E LDY  0 108F STY
                          2 10CE LDS  0 10CF STS
2 1183 CMPU 2 118C CMPS                           -1

LEA:
  30 LEAX 31 LEAY 32 LEAS  33 LEAU                -1

EXG:
  1E EXG  1F TFR                                  -1

SEX:
12 NOP   13 SYNC 19 DAA  1D SEX
39 RTS   3A ABX  3B RTI  3D MUL  3F SWI
40 NEGA                  43 COMA
44 LSRA           46 RORA 47 ASRA
48 ASLA
48 LSLA  49 ROLA 4A DECA
4C INCA  4D TSTA          4F CLRA
50 NEGB                    53 COMB
54 LSRB           56 RORB 57 ASRB
58 ASLB
58 LSLB  59 ROLB 5A DECB
5C INCB  5D TSTB          5F CLRB                 -1

SWI2:
  103F SWI2  113F SWI3                            -1

CWAI:
1A ORCC  1C ANDCC
34 PSHS  35 PULS  36 PSHU  37 PULU  3C CWAI       -1

BRA:
  2016 BRA  8D17 BSR                              -1

BEQ:
        21 BRN  22 BHI  23 BLS  24 BHS  25 BLO
                                24 BCC  25 BCS
26 BNE  27 BEQ  28 BVC  29 BVS  2A BPL  2B BMI
2C BGE  2D BLT  2E BGT  2F BLE                    -1

<----
\ 6809 conditions  (Constanten)
KON:
 20 NVR  21 ALW  22 LS   23 HI
 24 LO   25 HS
 24 CS   25 CC   26 EQ   27 NE
 28 VS   29 VC   2A MI   2B PL
 2C LT   2D GE   2E LE   2F GT         -1
---->

\ Forth-achtige 6809 assembler condities (AN)
\ Deze woordjes (constanten) dekken ALLE condities.

KON:
   23 U>?   24 U<?   24 CS?
   26 =?    28 VS?
   2A 0<?   2C <?
   2F >?                    -1

: NO (  cond# -- cond#2 ) 1 XOR ; \ condition inversion

\ 6809 registers (Constanten)
KON:
0 D   1 X   2 Y   3 U
4 S   5 PC  8 A   9 B   0A CCR  0B DP
S SP  X W   Y IP  U RP                   -1

\ 6809 addressing modes
-):
80 )+  81 )++  82 -)  83 --)
84 )   85 B)   86 A)  8B D)    -1


\ -------- coda ------------
FORTH DEFINITIONS
\ 6809  structured conditionals with compiler controll
\ These conditionals will be redefined in META
: IF,     ( cond# -- ifadr -11 ) xC, 0 xC, HERE -11 ;
: AHEAD,  ( -- aheadadr -11 )    20 ( NEVER ) IF, ;
: THEN,   ( adr -11 -- )         -11 ?PAIR HERE OVER -
                                 DUP 8BIT? 0= ?ILLEGAL SWAP 1- xC! ;
: /THEN,  ( adr -11 x y -- x y ) 2SWAP THEN, ;
: BEGIN,  ( -- beginadr -22 )          HERE -22 ;
: UNTIL,  ( beginadr -22 cond# -- )    SWAP -22 ?PAIR xC, HERE 1+ -
                                       DUP 8BIT? 0= ?ILLEGAL xC, ;
: AGAIN,  ( beginadr -22 -- )          20 ( NVR ) UNTIL, ;
: ELSE,   ( ifadr -11 -- elseadr -11 ) AHEAD, /THEN, ;
: WHILE,  ( adr n cond# -- whileadr -11 adr n ) IF, 2SWAP ;
: REPEAT, ( whileadr -11 beginadr -22 -- )      AGAIN, THEN, ;


\ 6809 addressing modes
META DEFINITIONS
: # 0 TO MODE ;

: REG ( "lijst" -- regbyte )  \ voorbeelden:  REG D,X  of REG X of REG X,Y
   0 BL WORD DUP .NAAM
   COUNT 0                    ( 0=regbyte  adres  count )
   ?DO                        ( regbyte  adres )
      COUNT
      >REGCODE SWAP >R OR R>  ( regbyte2 adres ) \ Bouw regbyte op met OR
   LOOP TRACER IF SPACE THEN
   DROP # ;                   ( regbyte ) \ mode 0

: ALLREG 0FF # ;              \ voor push/pull van alle registers
: #)     SWAP 89 INDEXREG ;   ( rval n -- n postbyte ) \ indexregister + offset
: []
  MODE 20 = IF DUP 9D AND 80 = ?ILLEGAL
               10 + }         \ Indexed:  postbyte -- postbyte
  20 TO MODE 9F ;             \ Extended: n -- n postbyte
: DP)   10 TO MODE ;
: PC)   20 TO MODE 8D ;      ( n -- n postbyte )

\ 6809 Direct Threaded Code
: NEXT  Y )++ [] JMP ; 


FORTH DEFINITIONS \ <<<<<<<<<<<<<<<<<<<<<<<<<<<<
DECIMAL
CR .( cras601 loaded )
CR
