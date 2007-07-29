\ dec2005 -*- Forth -*-

\ MAIS AN601 TARGET CODE -- Albert Nijhof -- 06jun2005

HX 65 TO USERBYTES

\ HX 2000 TO ORIGINTARGA
NOTRACE
HEX \ throughout

<----
Put a TRACE before and a NOTRACE after a piece of code if you
wish to study the details of what happens when that code is metacompiled.

Zet TRACE voor en NOTRACE achter een stukje code als je wilt
bekijken wat er gebeurt tijdens het metacompileren van die code.


-- Direct-Threaded Forth model for Motorola 6809
   16 bit cell, 8 bit char, 8 bit (byte) adrs unit
   X = Forth W    free
   Y =       IP   Interpreter Pointer
   U =       RP   Return Stack Pointer
   S =       SP   Data Stack Pointer
   D =       TOS  Top of data stack

--  m e m o r y  m a p
 hex
 00~ 75      "USER Page"
       --- ---
       00     JMP COLD
       03     Dictionary with hx 10 topnfas
       23-75  Cold start data: space available
              for up to 32 users(64 bytes)
              and 6 vectors(18 bytes)
       --- ---
 75~ 80 Search order stack (CONTEXT..CURRENT)
 80~100 TIB           (hx 80 bytes)
100~180 Data stack    (hx 80 bytes)
180~200 Return stack  (hx 80 bytes)
200~280 Fly zone
280~300 Compiler stack
300     = HERE at Cold Start

        --- --- moving up:
        HERE ~      Ruimte voor BL-WORD (hx 20 bytes)
             ~ PAD  HOLD Buffer         (hx 20 bytes) (dalend)
        PAD = HERE + hx 40
        --- ---

HIMEM   = Einde van de RAM

--  TOPNFA = NFA of the most recently created Word

--  Four linked lists:

  Links point to the zero-labeled positions (see below).
  End of List is reached when Link=0

1) Words

  hx 10 Topnfa's (Threads) of the dictionary,
  in RAM: hx (03~23), in ROM: ORIGIN+(03~23).

  Word map (there is a Homlink only if Name is a homonym).
  | Homlink | Link | Homvocimm | Count + Name | Cf    | Body
  -5        -3     -1          0         1    n+1     n+4
  
2) Wordlists

  TOPVOC = Address of most recently created Wordlist.

  Wordlist (usually situated in a Vocabulary body)
  | Wid | Link |
  0     1      3

3) THROW Messages

  TOPMSG = Address of most recently created Message.

  Message
  | Msg# | Link | Count + Text |
  0      2      4         5    n+5

4) Prefixlists

  TOPPFX = Address of most recently created Prefixlist.

  Prefixlist
  | Link | doer-token | TO-action | +TO-action | INCR-action |
  -2     0            2           4            6             8


--  NEXT == Y )++ [] JMP   \ ip )++ ) jump

-- Interrupt vectors
  'SWI3 'SWI2 'FIRQ 'IRQ 'SWI 'NMI (3 bytes each)

  'SWI3 ( -- adr ) \ adr = FFF2 @
  'SWI2 ( -- adr ) \ adr = FFF4 @
  'FIRQ ( -- adr ) \ adr = FFF6 @
  'IRQ  ( -- adr ) \ adr = FFF8 @
  'SWI  ( -- adr ) \ adr = FFFA @
  'NMI  ( -- adr ) \ adr = FFFC @

  Default contents of these addresses: 3B 00 00 (3B = RTI).

  : !VECTOR ( routineaddress vector -- ) 1+ ! ;
  : ENABLE  ( vector -- ) 07E SWAP C! ;
  : DISABLE ( vector -- ) 03B SWAP C! ;

  Example of use:
  1AF0 'SWI3 !VECTOR   \ Address of interrupt routine into byte 2 en 3.
  'SWI3  ENABLE        \ 7E = JMP into byte 1.
  'SWI3  DISABLE       \ 3B = RTI into byte 1.

MaisForth Target code:
---->


:::MAIS:::

\ ----- 01 ----- cold start data

0 JMP        \ for JMP COLD -- See COLD ttt
DICTIONARY   \ 0003-0023 ttt
I-DATA       \ Space reservation for cold users values ttt See USERBYTES in META

\ At cold start the ROM data until here (C000-C0..)
\ will be copied to RAM (00-..)
 

\ ----- 02 ----- doers

FORTH:
CODE EXECUTE   D X TFR   REG D PULS   X ) JMP   END-CODE
CODE EXIT      REG Y PULU   NEXT END-CODE

INSIDE:
CODE EXIT-ON-TRUE ( flag -- )
  0 # CMPD   REG D PULS   =? NO IF   REG Y PULU   THEN   NEXT END-CODE
CODE EXIT-ON-FALSE ( flag -- )
  0 # CMPD   REG D PULS   =? IF   REG Y PULU   THEN   NEXT END-CODE
CODE DIVE ( -- )    \ See FLYER PARENTHESIZE
  Y X TFR   REG Y PULU   REG X PSHU   NEXT END-CODE
CODE DODOES   \ (an) 2004
  REG Y PSHU                  \ save IP
  REG Y PULS                  \ new IP = returnaddress = just after JSR DODOES
  REG X PULS  REG D PSHS  X D TFR   ( body ? -- ? body )
  NEXT END-CODE
DOER: DODOER   HERE-IS THINGUMAJIG EXIT ;
\ Voorwaartse referentie. De EXIT wordt later gepatcht. Zie !DOER
\ Het uiteindelijke resultaat:   DOER: DODOER !DOER ;
DOERCODE DO:      REG Y PSHU   REG Y PULS                   NEXT END-CODE
DOERCODE DOCREATE REG X PULS   REG D PSHS   X D TFR         NEXT END-CODE
DOERCODE DOVAR    REG X PULS   REG D PSHS   X D TFR         NEXT END-CODE
DOERCODE DOCCON   REG X PULS   REG D PSHS   X ) LDB   SEX   NEXT END-CODE \ C@
DOERCODE DOCON    REG X PULS   REG D PSHS   X ) LDD         NEXT END-CODE \ @
DOERCODE DOVAL    REG X PULS   REG D PSHS   X ) LDD         NEXT END-CODE \ @
DOERCODE DOIVAR   REG X PULS   REG D PSHS   X ) LDD         NEXT END-CODE \ @
DOERCODE DOIVAL   REG X PULS   REG D PSHS   X ) [] LDD      NEXT END-CODE \ @@
DOERCODE DOVARS   ASLB  ROLA   S )++ ADDD   NEXT END-CODE   \ SWAP CELLS +

\ ----- 03 ----- input output

\ Input and output for the MAIS board. (FvdM) 2003 ttt
TRACE
FORTH:
CODE EMIT?   ( -- flag )
    REG D PSHS
    ACIA-CONTROL LDA
    CLRB
    \ ACIA-CONTROL C@ 2 AND 2 =
    2 # ANDA
    =? NO IF
        DECB
    THEN
    SEX
    NEXT END-CODE

INSIDE:
CODE (EMIT   ( char -- )
    ACIA-CONTROL # LDX
    \ ACIA-CONTROL C@ 2 AND UNTIL
    BEGIN
        X ) LDA
        2 # ANDA
    =? NO UNTIL
    \ CH ACIA-DATA C!
    X 1 #) STB
    REG D PULS
    NEXT END-CODE

EXTRA:
CODE !USART ( baudbyte -- )   \ Set up on-board i/o, See COLD
    \ Fixed at 9600/8/n/1
    ACIA-CONTROL # LDX
    55 # LDA
    X ) STA
    REG D PULS
    NEXT  END-CODE

FORTH:
CODE KEY? ( -- flag )
    \ ACIA-CONTROL C@ 1 AND 1 =
    REG D PSHS
    ACIA-CONTROL LDA
    CLRB
    1 # ANDA
    =? NO IF
        DECB
    THEN
    SEX
    NEXT END-CODE

CODE KEY ( -- char )
    REG D PSHS
    ACIA-CONTROL # LDX
    \ ACIA-CONTROL C@ 1 AND UNTIL
    BEGIN
        X ) LDB
        1 # ANDB
    =? NO UNTIL
    \ ACIA-DATA C@
    X 1 #) LDB
    CLRA
    NEXT END-CODE
NOTRACE

\ ----- 04 ----- inline arguments


\ Inline arguments (AN) 2004
\ To be used in hi-level definitions:
INSIDE:
CODE INLINE# ( -- x )   \ See COMPILE() TO$() +TO$() INCR$()
  REG D PSHS
  U ) LDX               \ R@
  X )++ LDD             \ inline#
  U ) STX               \ skip
  NEXT END-CODE

<----
CODE INLINEC ( -- x )   \ Inline byte
  REG D PSHS
  U ) LDX               \ R@
  X )+ LDB   CLRA       \ inline#
  U ) STX               \ skip
  NEXT END-CODE
---->
CODE INLINE$ ( -- adr len )   \ See "(S) ."(S)
  REG D PSHS
  U ) LDX           \ R@
  X )+ LDB   CLRA   \ C@ (=len)
  REG X PSHS        \ adr
  ABX   U ) STX     \ skip
  NEXT END-CODE
CODE /INLINE$ ( -- )   \ See ABORT"(S)
  REG D PSHS
  U ) LDX                  \ R@
  X )+ LDB                 \ C@ (=len)
  X B) LEAX   U ) STX      \ skip
  REG D PULS   NEXT END-CODE

\ Words that need inline arguments (an)
INSIDE:
CODE GOTO() ( -- )   \ branch always. See AHEAD AGAIN
  Y ) LDY   NEXT END-CODE
CODE IF() ( x -- )          \ branch on zero.
  0 # CMPD   REG D PULS   =?
  IF     Y ) LDY   NEXT
  THEN   Y 2 #) LEAY   NEXT END-CODE
CODE IFZERO() ( x -- )         \ branch on non-zero. See IF & <FUSE
  0 # CMPD   REG D PULS   =? NO
  IF     Y ) LDY   NEXT
  THEN   Y 2 #) LEAY   NEXT END-CODE
CODE ()  ( -- x )    REG D PSHS   Y )++ LDD   NEXT END-CODE        \ See LITERAL
CODE (C) ( -- ch )   REG D PSHS   Y )+ LDB   SEX   NEXT END-CODE   \ See LITERAL

\ Prefixes - See TO-LIST
INSIDE:
CODE TO()   ( x -- )   Y )++ LDX              X ) STD   REG D PULS   NEXT END-CODE
CODE +TO()  ( x -- )   Y )++ LDX   X ) ADDD   X ) STD   REG D PULS   NEXT END-CODE
CODE INCR() ( -- )     Y )++ LDX   REG D PSHS
                       X ) LDD     1 # ADDD   X ) STD   REG D PULS   NEXT END-CODE 

\ DO LOOP (AN) 2004

\ --- A'DAM
INSIDE:
CODE DO() ( limit start -- )   \ R: leavea   8000-lim   start+8000-lim
  HERE-IS AMSTERDAM
  Y )++ LDX   REG X PSHU    \ inline leave address >R
  D X TFR                   \ start
  8000 # LDD   S )++ SUBD   \ 8000-limit
  REG D PSHU                \ >r
  X D) LEAX   REG X PSHU    \ start+8000-limit >r
  REG D PULS                \ new top
  NEXT END-CODE
CODE ?DO() ( limit start -- )   \ R: leavea   8000-lim   start+8000-lim
  S ) CMPD   AMSTERDAM BNE
  S 2 #) LEAS   REG D PULS   \ 2DROP
  Y ) LDY   NEXT END-CODE    \ leave address to IP
\ ---

\ --- R'DAM
INSIDE:
CODE LOOP()   \ R: leavea   8000-lim   start+8000-lim
  REG D PSHS   U ) LDD       \ r>
  1 # ADDD
  HERE-IS ROTTERDAM
  VS? NO
  IF   U ) STD   REG D PULS   \ >r
       Y ) LDY   NEXT         \ loop again
  THEN               \ overflow:
  Y 2 #) LEAY        \ loop ready
  U 6 #) LEAU        \ RDROP RDROP RDROP
  REG D PULS         \ new top
  NEXT END-CODE
CODE +LOOP() ( n -- )   \ R: leavea   8000-lim   start+8000-lim
  U ) ADDD              \ top u) + to top
  ROTTERDAM BRA
  END-CODE
\ ---

FORTH:
CODE LEAVE ( -- )   \ R: leavea   8000-lim   start+8000-lim 
  U 4 #) LEAU       \ RDROP RDROP
  REG Y PULU        \ R> TO IP
  NEXT END-CODE
CODE UNLOOP ( -- )   \ R: leavea   8000-lim   start+8000-lim
  U 6 #) LEAU        \ RDROP RDROP RDROP
  NEXT END-CODE
CODE I ( -- i )   REG D PSHS   U ) LDD      U 2 #) SUBD   NEXT END-CODE
CODE J ( -- j )   REG D PSHS   U 6 #) LDD   U 8 #) SUBD   NEXT END-CODE

\ ----- 05 ----- ttt

<----
 IVAL en IVAR
 de I staat voor indirectie. De "userpage" begint op 0000.
 Eerst een jump naar COLD, dan 16 draden (03-023)
 De koude offset t.o.v. ORIGIN is dus tevens warm RAM adres.
 IVAL gedraagt zich als een value. Het systeem kan hem veranderen,
 de programmeur kan dat niet rechtstreeks:
---->
\ indirecte values (an)
\ De programmeur kan deze grootheden alleen indirect wijzigen.
\ The programmer can only indirectly change these system values.
INSIDE:  0 IVAL TOPVOC   \  See WORDLIST VOC>NAMA (FORGET
         0 IVAL TOPMSG   \  See MSG" .MSG (FORGET
         0 IVAL TOPPFX   \  See O&P TO +TO INCR
       303 IVAL TOPNFA   \  Last created header in dictionary.
         0 IVAL HLD      \  See HOLD <# #>
         0 IVAL CONTEXT  \ 
       01F IVAL CS#      \  Relatieve CS-pointer. See CSP >CS CS>
         0 IVAL MSG#-2   \  See ABORT"(S) .MSG
        30 IVAL MODE     \  Assembler adressing mode: 0=immed, 10=direct, 20=indexed, 30=extended
         0 IVAL SECTION  \  Marks compiler discontinuity (for 0=IF)
         0 IVAL #TIMES   \  See TIMES
         0 IVAL #IB      \  Inputbuffer len
         0 IVAL IB       \  Inputbuffer adr
       200 IVAL THERE    \  Tijdelijke HERE -- See FLYER
EXTRA:   0 IVAL HOR      \  Telt karakter output, 0 = begin vd regel.
         0 IVAL VER      \ 
         0 IVAL HIMEM    \  hoogste RAMadres+1
         3 IVAL OK       \  See .OK
         0 IVAL DOT?     \  See DNUMBER? EVAL
FORTH: 300 IVAL HERE     \  See ALLOT
\ indirecte variabelen
INSIDE:  0 IVAR WRD  2 UALLOT   \ see WORD
FORTH:   0 IVAR >IN      \ ( -- adr )
        0A IVAR BASE     \ ( -- adr )
         0 IVAR STATE    \ ( -- adr )

\ Interrupt en Exception vectoren.
\ De pointers in FFF0-FFFF wijzen naar deze adressen.

EXTRA:
\ For ROM version
\ Interrupt vectors FFF0,FFF2,FFF4,FFF6,FFF8,FFFA,FFFC.
ORIGINHOSTA -10 +              \  later: FFF0
 ORIGINTARGA OVER !
2 + UOFFSET  OVER ! IVEC 'SWI3 \  FFF2
2 + UOFFSET  OVER ! IVEC 'SWI2 \  FFF4
2 + UOFFSET  OVER ! IVEC 'FIRQ \  FFF6
2 + UOFFSET  OVER ! IVEC 'IRQ  \  FFF8
2 + UOFFSET  OVER ! IVEC 'SWI  \  FFFA
2 + UOFFSET  OVER ! IVEC 'NMI  \  FFFC
DROP  -2 UALLOT   \ Alleen de byte met RTI wordt meegenomen.
\ Een vector neemt 3 userbytes ruimte in.

\ 'NMI is de laatste "user"!
\ Als je meer indirecte waarden wilt definiëren, voeg die dan in
\ voor de vectoren. De value USERBYTES in de metacompiler moet
\ dan aangepast worden:
\ userbytes  =  (aantal i-waarden)*2  +  (aantal vectoren)*3  -  2


\ --- constanten ---

FORTH:
ORIGINTARGA CONSTANT ORIGIN \ ttt
INSIDE: 075 CONSTANT FINDSTACK \ Begin of search-order stack
        07F CONSTANT CURRENT   \ End of search-order stack
        080 CONSTANT TIB       \ Terminal Input Buffer
        17E CONSTANT S0        \ End of parameter stack
        1FE CONSTANT R0        \ End of return stack
        200 CONSTANT FLYBUF    \ Flyer buffer
        2FC CONSTANT CS0       \ End of compilerstack
        07E CONSTANT TIBSIZE
EXTRA:    2 CONSTANT CELL
FORTH:   -1 CONSTANT TRUE
          0 CONSTANT FALSE
         20 CONSTANT BL

\ ----- 06 -----

\ memory operations

INSIDE:
CODE CLEAR-S   ' S0 >body @ # LDS   REG D PULS   NEXT END-CODE   \ See QUIT
CODE CLEAR-R   ' R0 >body @ # LDU                NEXT END-CODE   \ See QUIT
\ Get stack-pointer
CODE SP@   REG D PSHS   S D TFR   NEXT END-CODE   \ ?STACK DEPTH
CODE RP@   REG D PSHS   U D TFR   NEXT END-CODE   \ Not used
\ CODE SP!   D S TFR   REG D PULS   NEXT END-CODE   \ Not used
\ CODE RP!   D U TFR   REG D PULS   NEXT END-CODE   \ Not used

\ Store en Fetch
FORTH:
CODE C!   D X TFR   REG D PULS   X ) STB     REG D PULS   NEXT END-CODE
CODE !    D X TFR   REG D PULS   X ) STD     REG D PULS   NEXT END-CODE
CODE 2!   D X TFR   REG D PULS
        X )++ STD   REG D PULS   X ) STD     REG D PULS   NEXT END-CODE
CODE +!   D X TFR   REG D PULS
                    X ) ADDD     X ) STD     REG D PULS   NEXT END-CODE
EXTRA:
CODE C+!  D X TFR   REG D PULS
                    X ) ADDB     X ) STB     REG D PULS   NEXT END-CODE
CODE 1+!  D X TFR   X ) LDD
                    1 # ADDD     X ) STD     REG D PULS   NEXT END-CODE

FORTH:
CODE C@    D X TFR   X ) LDB    CLRA                    NEXT END-CODE
CODE @     D X TFR   X ) LDD                            NEXT END-CODE
CODE 2@    D X TFR   X )++ LDD   X ) LDX   REG X PSHS   NEXT END-CODE
CODE COUNT D X TFR   X )+ LDB   CLRA       REG X PSHS   NEXT END-CODE
EXTRA:
CODE @+    D X TFR   X )++ LDD             REG X PSHS   NEXT END-CODE

\ Return stack
FORTH:
CODE >R    REG D PSHU   REG D PULS   NEXT END-CODE
CODE R>    REG D PSHS   REG D PULU   NEXT END-CODE
CODE 2>R   REG X PULS   REG X PSHU   REG D PSHU   REG D PULS   NEXT END-CODE
CODE 2R>   REG D PSHS   REG D PULU   REG X PULU   REG X PSHS   NEXT END-CODE
CODE R@    REG D PSHS   U ) LDD   NEXT END-CODE
CODE 2R@   REG D PSHS   U 2 #) LDX   REG X PSHS   U ) LDD   NEXT END-CODE
EXTRA:
CODE RDROP    U 2 #) LEAU   NEXT END-CODE
CODE 2RDROP   U 4 #) LEAU   NEXT END-CODE

<---- \ Double exit:
INSIDE:
CODE DEXIT ( -- )   REG X,Y PULU   NEXT END-CODE   \ Same as RDROP+EXIT
---->

\ stack operations
FORTH:
CODE 2DROP   S 2 #) LEAS   REG D PULS   NEXT END-CODE
CODE 2DUP    S ) LDX   REG D PSHS   REG X PSHS   NEXT END-CODE
CODE 2NIP    REG X PULS   S 4 #) LEAS   REG X PSHS   NEXT END-CODE
CODE 2OVER   REG D PSHS   S 6 #) LDD   REG D PSHS   S 6 #) LDD   NEXT END-CODE
CODE 2SWAP   REG D PSHU   S ) LDX   S 4 #) LDD   S 4 #) STX   S ) STD   \ swap n2 n4:
             REG X PULU   S 2 #) LDD   S 2 #) STX   NEXT END-CODE       \ swap n1 n3
: 2TUCK   2SWAP 2OVER ; ( x1 x2 x3 x4 -- x3 x4 x1 x2 x3 x4 )
: 2ROT    2>R 2SWAP 2R> 2SWAP ;
\ : -2ROT     2SWAP 2>R 2SWAP 2R> ;

<----
CODE 2TUCK ...
CODE 2ROT ...
---->

FORTH:
CODE ?DUP   0 # CMPD   =? NO IF   REG D PSHS   THEN   NEXT END-CODE
CODE DROP   REG D PULS   NEXT END-CODE
CODE DUP    REG D PSHS   NEXT END-CODE
CODE OVER   REG D PSHS   S 2 #) LDD   NEXT END-CODE
CODE SWAP   S ) LDX   S ) STD   X D TFR   NEXT END-CODE
CODE TUCK   S ) LDX   S ) STD   REG X PSHS   NEXT END-CODE
CODE ROT    S ) LDX   S ) STD   S 2 #) LDD   S 2 #) STX   NEXT END-CODE
CODE -ROT   S 2 #) LDX   S 2 #) STD   S ) LDD   S ) STX   NEXT END-CODE

\ --- A'DAM
FORTH:
CODE NIP    HERE-IS AMSTERDAM   S 2 #) LEAS   NEXT END-CODE
CODE PICK   ASLB   S X TFR   ABX X ) LDD   NEXT END-CODE
CODE MIN    S ) CMPD   AMSTERDAM BLT   REG D PULS   NEXT END-CODE
CODE MAX    S ) CMPD   AMSTERDAM BGT   REG D PULS   NEXT END-CODE
EXTRA:
CODE UMIN   S ) CMPD   AMSTERDAM BLO   REG D PULS   NEXT END-CODE
CODE UMAX   S ) CMPD   AMSTERDAM BHI   REG D PULS   NEXT END-CODE
\ ---

\ comparison operations (an)
FORTH:
CODE 0<    A B TFR   SEX   A B TFR   NEXT END-CODE

\ --- R'DAM
FORTH:
CODE 0=    0 # CMPD   =?
           IF   HERE-IS ROTTERDAM   COMB   SEX   NEXT   \ B=0 -> D=-1.
           THEN   CLRA   CLRB   NEXT END-CODE
CODE 0>    0 # CMPD    =? IF   NEXT    THEN
           A B TFR   SEX   COMA   A B TFR   NEXT END-CODE
CODE =     S )++ SUBD   ROTTERDAM BEQ   CLRA   CLRB   NEXT END-CODE
\ ---

\ --- A'DAM
FORTH:
CODE <>    S )++ SUBD   =? NO IF   HERE-IS AMSTERDAM   -1 # LDD   THEN   NEXT END-CODE
CODE 0<>   0 # CMPD     AMSTERDAM BNE                 NEXT END-CODE
CODE U>    S )++ SUBD   AMSTERDAM BLO   CLRA   CLRB   NEXT END-CODE
CODE U<    S )++ SUBD   AMSTERDAM BHI   CLRA   CLRB   NEXT END-CODE
CODE >     S )++ SUBD   AMSTERDAM BLT   CLRA   CLRB   NEXT END-CODE
CODE <     S )++ SUBD   AMSTERDAM BGT   CLRA   CLRB   NEXT END-CODE
<----
EXTRA: \ (FvdM) 2004
CODE 0>=   TSTA         AMSTERDAM BPL   CLRA   CLRB   NEXT END-CODE
CODE <=    S )++ SUBD   AMSTERDAM BGE   CLRA   CLRB   NEXT END-CODE
CODE >=    S )++ SUBD   AMSTERDAM BLE   CLRA   CLRB   NEXT END-CODE
CODE U<=   S )++ SUBD   AMSTERDAM BHS   CLRA   CLRB   NEXT END-CODE
CODE U>=   S )++ SUBD   AMSTERDAM BLS   CLRA   CLRB   NEXT END-CODE
---->
\ ---

\ logical operations
FORTH:
CODE AND    S )+ ANDA   S )+ ANDB   NEXT END-CODE
CODE OR     S )+ ORA   S )+ ORB  NEXT END-CODE
CODE XOR    S )+ EORA   S )+ EORB   NEXT END-CODE
CODE INVERT COMA   COMB   NEXT END-CODE
CODE LSHIFT \ bjr
  D X TFR   REG D PULS   X ) LEAX   =? NO
  IF   BEGIN   LSLB   ROLA   X -1 #) LEAX   =?
       UNTIL
  THEN   NEXT END-CODE
CODE RSHIFT \ bjr
  D X TFR   REG D PULS   X ) LEAX   =? NO
  IF   BEGIN   LSRA   RORB   X -1 #) LEAX   =?
       UNTIL
  THEN   NEXT END-CODE

EXTRA:
CODE BYTESWAP ( swap bytes )   A B EXG   NEXT END-CODE

\ arithmetic operations
FORTH:
CODE 1+    1 # ADDD   NEXT END-CODE
CODE 1-    1 # SUBD   NEXT END-CODE
CODE 2*    ASLB   ROLA   NEXT END-CODE
CODE 2/    ASRA   RORB   NEXT END-CODE   \ arithmetic right shift
CODE +     S )++ ADDD   NEXT END-CODE
CODE -     S )++ SUBD   COMA   COMB   1 # ADDD   NEXT END-CODE
CODE D2*   D X TFR   REG D PULS   ASLB   ROLA
           REG D PSHS   X D TFR   ROLB   ROLA   NEXT END-CODE

\ --- A'DAM
FORTH:
CODE D2/   ASRA
           HERE-IS AMSTERDAM
           RORB   D X TFR   REG D PULS
           RORA   RORB   REG D PSHS   X D TFR   NEXT END-CODE
EXTRA:
CODE DU2/   LSRA   AMSTERDAM BRA   NEXT END-CODE
\ ---

\ --- R'DAM
FORTH:
CODE NEGATE   HERE-IS ROTTERDAM   COMA   COMB   1 # ADDD   NEXT END-CODE
CODE ABS   TSTA   ROTTERDAM BLT   NEXT END-CODE
EXTRA:
CODE ?NEGATE   TSTA   REG D PULS   ROTTERDAM BLT   NEXT END-CODE
<----
\ : ABS      DUP ?NEGATE ;
\ : ?NEGATE  ( x1 y -- x2 )   0< 0= ?EXIT NEGATE ;
---->
\ ---

\ --- R'DAM
FORTH:
CODE DNEGATE ( xlo xhi -- ylo yhi )   \ (AN) 2004
  HERE-IS ROTTERDAM
  REG D PSHS
  CLRB  SEX    D X TFR       \ 0
  S 2 #) SUBD   S 2 #) STD   \ ylo
  X D TFR   0 # SBCB   SEX   \ 0 -carry?
  S )++ SUBD                 \ yhi
  NEXT END-CODE
CODE DABS   TSTA   ROTTERDAM BLT   NEXT END-CODE
EXTRA:
CODE ?DNEGATE   TSTA   REG D PULS   ROTTERDAM BLT   NEXT END-CODE
<----
\ : DABS     DUP ?DNEGATE ;
EXTRA:
\ : ?DNEGATE ( xlo xhi y -- xlo2 xhi2 )   0< 0= ?EXIT DNEGATE ;
---->
\ ---

FORTH:
CODE D+  ( dx dy -- dz )   \ (AN) 2004
  D X TFR               \ yhi
  REG D PULS            \ ylo
  S 2 #) ADDD           \ xlo +to ylo
  S 2 #) STD            \ = zlo
  X D TFR               \ yhi
  0 # ADCB   0 # ADCA   \ yhi + carry?
  S )++ ADDD            \ xhi +to yhi = zhi
  NEXT END-CODE
CODE D- ( xlo xhi ylo yhi -- zlo zhi )   \ (AN) 2004
  REG D PSHS
  S 6 #) LDD   S 2 #) SUBD   S 6 #) STD   \ zlo
  S 4 #) LDD   0 # SBCB   0 # SBCA        \ xhi -carry?
  S ) SUBD                                \ zhi
  S 6 #) LEAS   NEXT END-CODE
CODE M+ ( dx ylo -- dz )
  S 2 #) ADDD           \ xlo +to ylo
  S 2 #) STD            \ = zlo
  REG D PULS            \ xhi
  0 # ADCB   0 # ADCA   \ xhi + carry?
  NEXT END-CODE


CODE UM* ( u1 u2 -- ud )   \ 16*16=32 unsigned multiply (c) 25apr95 bjr
  REG X,D PSHS                                         \ push temporary, u2
  S 5 #) LDA   S 1 #) LDB   MUL   S 2 #) STD           \ 1lo*2lo
  S 4 #) LDA   S 1 #) LDB   MUL                        \ 1hi*2lo
  S 2 #) ADDB   0 # ADCA   S 1 #) STD
  S 5 #) LDA   S ) LDB   MUL                           \ 1lo*2hi
  S 1 #) ADDD   S 1 #) STD   0 # LDA   ROLA            \ cy in A
  S ) LDB   S ) STA   S 4 #) LDA   MUL                 \ 2hi*1hi
  S ) ADDD                                             \ hi result in D
  S 2 #) LDX   S 4 #) LEAS   S ) STX   NEXT END-CODE   \ lo result
CODE UM/MOD ( ud u1 -- rem quot )   \ 32/16=16 divide (c) 25apr95 bjr
  REG D PSHS   10 # LDX                              \ save u1 in mem
  S 5 #) ASL   S 4 #) ROL                            \ initial shift (lo 16)
  BEGIN   S 3 #) ROL   S 2 #) ROL   S 2 #) LDD       \ shift left hi 16
       CS? IF                                        \ 1xxxx: 17 bits, subtract is ok
          S ) SUBD   S 2 #) STD   0FE # ANDCC        \ clear cy
       ELSE                                          \ 0xxxx: 16 bits, test subtract
          S ) SUBD   CS? NO IF   S 2 #) STD   THEN   \ cs=can't subtr
       THEN                                          \ cy=0 if sub ok, 1 if no subtract
          S 5 #) ROL   S 4 #) ROL                    \ rotate cy into result
          X -1 #) LEAX
  =? UNTIL                                           \ loop 16 times
  S 4 #) LDD   COMA   COMB                           \ invert to get true quot in D
  S 2 #) LDX   S 4 #) STX   S 4 #) LEAS              \ save rem, clean stack
  NEXT END-CODE

\ string operations
CODE FILL ( c-addr u char -- )   \ (c) 31mar95 bjr
  REG Y PSHU   REG X,Y PULS   \ D=char X=u Y=adr
  0 # CMPX   =? NO
  IF BEGIN   Y )+ STB   X -1 #) LEAX   =?
     UNTIL
  THEN   REG D PULS   REG Y PULU   NEXT END-CODE

EXTRA:
CODE S<>  ( a1 a2 len -- -1 | 1 | 0 )     \ string compare
  S 2 #) ADDD   S 2 #) LDX   S 2 #) STY   \ X=src D=end
  S ) LDY   S ) STD   CLRB                \ Y=dst B=0
  AHEAD
     BEGIN   X )+ LDA   Y )+ SUBA   =? NO
        IF   0 # SBCB   SEX   1 # ORB
             REG X,Y PULS   NEXT
        THEN
  /THEN      S ) CMPX   =?
     UNTIL
  SEX   REG X,Y PULS   NEXT END-CODE

FORTH:
CODE CMOVE ( c-addr1 c-addr2 u -- )      \ BJR*
  S 2 #) ADDD  S 2 #) LDX   S 2 #) STY   \ X=src D=end
  S ) LDY   S ) STD                      \ Y=dst
  AHEAD
     BEGIN   X )+ LDB   Y )+ STB
  /THEN      S ) CMPX   =?
     UNTIL   REG X,Y PULS   REG D PULS
  NEXT END-CODE
CODE CMOVE> ( c-addr1 c-addr2 u -- )    \ BJR*
  S 2 #) LDX   X D) LEAX   S 2 #) STY   \ X=src D=u
  S ) LDY   Y D) LEAY                   \ Y=dst
  AHEAD
     BEGIN   X -) LDB   Y -) STB
  /THEN      S ) CMPY   =?
     UNTIL
  REG X,Y PULS   REG D PULS
  NEXT
\ Exits for SKIP en SCAN (hereafter)

\ --- A'DAM & R'DAM
 HERE-IS AMSTERDAM   Y -1 #) LEAY
 HERE-IS ROTTERDAM   REG Y PSHS   REG Y PULU   X D TFR
 NEXT END-CODE
EXTRA:
CODE SKIP ( c-addr u ch -- c-addr' u' )   \ skip matching chars BJR
  REG Y PSHU   REG X,Y PULS        \ D=char X=u Y=adr
  0 # CMPX   =? NO
  IF   BEGIN   Y )+ CMPB   AMSTERDAM BNE
               X -1 #) LEAX   =?
       UNTIL
  THEN   ROTTERDAM BRA   END-CODE
CODE SCAN ( c-addr u ch -- c-addr' u' )   \ find matching char BJR
  REG Y PSHU   REG X,Y PULS       \ D=char X=u Y=adr
  0 # CMPX   =? NO
  IF   BEGIN   Y )+ CMPB   AMSTERDAM BEQ
               X -1 #) LEAX   =?
       UNTIL
  THEN   ROTTERDAM BRA   END-CODE
\ ---

\ ----- 07 -----

FORTH:
\ CODE ALIGNED ( a -- a )   NEXT END-CODE  IMMEDIATE
\ CODE ALIGN   ( -- )       NEXT END-CODE  IMMEDIATE
CODE CELL+   2 # ADDD   NEXT END-CODE
CODE CHAR+   1 # ADDD   NEXT END-CODE
CODE >BODY   3 # ADDD   NEXT END-CODE
EXTRA:
CODE CELL-   2 # SUBD   NEXT END-CODE
CODE CHAR-   1 # SUBD   NEXT END-CODE
CODE BODY>   3 # SUBD   NEXT END-CODE
FORTH:
CODE CELLS   ASLB   ROLA   NEXT END-CODE
CODE CHARS   NEXT END-CODE   IMMEDIATE
INSIDE:
CODE NAME>LINK ( nfa -- lfa )  3 # SUBD   NEXT END-CODE

FORTH:
: ROLL ( n -- x )
  >R R@ PICK
  SP@ DUP CELL+ R> 1+ CELLS CMOVE>
  DROP ;
: PAD       HERE 40 + ;
: ALLOT     +TO HERE ;
: ,         HERE !  CELL +TO HERE ;
: C,        HERE C! INCR HERE ;

EXTRA:
\ : NAME> ( nfa -- xt )   COUNT 1F AND + ;
\ : >NAME ( cfa -- nfa )   BEGIN 1- 60 OVER C@ AND 0= UNTIL ;
CODE NAME>   D X TFR   X )+ LDB   1F # ANDB   X B) LEAX   X D TFR   NEXT END-CODE
CODE >NAME   D X TFR
  BEGIN   60 # LDB   X -) ANDB   =?
  UNTIL
  X D TFR   NEXT END-CODE

INSIDE:
: !DOER ( DOERa -- )   TOPNFA NAME> 1+ ! ; \ de JSR staat er al
' !DOER THINGUMAJIG COMPILE! \ Patch in DODOER (Voorwaartse referentie)
\ : @IMM   ( nfa -- -1/+1 )   1- C@ 1 AND 2* 1- ;
\ : HOM?   ( nfa -- 0/-1 )   1- C@ 80 AND 0<> ;
\ : @VOC   ( nfa -- wid )   1- C@ 7E AND ;
CODE @IMM   D X TFR  X -)   LDB   1 # ANDB   ASLB   DECB   SEX   NEXT END-CODE
CODE HOM?   D X TFR  X -)   LDB   SEX   A B TFR   NEXT END-CODE
CODE @VOC   D X TFR  X -)   LDB   7E # ANDB   SEX   NEXT END-CODE
 
FORTH:
\ : WITHIN ( a x y -- flag )   OVER - >R - R> U< ;
CODE WITHIN (  a x y -- t/f )   \ a-x y-x u<?
  S ) SUBD   D X TFR            \ y-x
  S 2 #) LDD   S )++ SUBD       \ a-x
  S ) STX   S )++ SUBD          \ a-x - y-x
  0 # LDB                       \ dit beinvloedt U<? niet?
  U<? IF   DECB   THEN   SEX   NEXT END-CODE

\ ----- 08 -----

\ Compilerstack [HIMEM-80..HIMEM) (dalend) (AN) 2004
INSIDE:
: CSP ( -- a )        CS0 CS# CELLS 2* 7C AND - ;
: >CS ( x1 x2 -- )    INCR CS# CSP 2! ;
: CS> ( --  x1 x2 )   CSP 2@ -1 +TO CS# ;

FORTH:
: CS-PICK ( n -- )
  CS# >R
  NEGATE +TO CS# CS>
  R> TO CS# >CS ;  
: CS-ROLL ( q -- )  \ q in 0..1F
  >R
  R@ 0 ?DO CS> LOOP \ Haal elementen 0..n-1 van CS-stack
  R> CS> 2>R        \ Verplaats element nr n van CS-stack naar R
  0 ?DO >CS LOOP    \ Zet elementen n-1..0 terug op CS-stack
  2R> >CS ;         \ Verplaats element nr n van R naar CS-stack

FORTH:
\ : S>D      DUP 0< ;
CODE S>D   REG D PSHS   A B TFR   SEX   A B TFR   NEXT END-CODE

<----
: M* ( n1 n2 -- d ) \ signed 16*16->32 multiply (BJR)
  2DUP XOR >R
  SWAP ABS SWAP ABS UM* \ eerste SWAP kan weg
  R> ?DNEGATE ;
: SM/REM ( d1 n1 -- n2 n3 ) \ symmetric signed division (BJR)
  2DUP XOR >R
  OVER >R               \ Dhi
  ABS >R DABS R> UM/MOD
  SWAP R> ?NEGATE
  SWAP R> ?NEGATE ;
: FM/MOD      ( d1 n1 -- n2 n3 )  \ floored signed division (BJR)
  DUP >R  2DUP XOR >R >R
  DABS R@ ABS UM/MOD SWAP
  R> ?NEGATE SWAP R> 0<
  IF   NEGATE OVER               \ quotient negative
       IF                        \ if remainder nonzero
            R@ ROT - SWAP 1-     \ adjust rem,quot
       THEN
  THEN  RDROP ;
---->

: M* ( n1 n2 -- d )   \ signed 16*16->32 (AN)
  OVER ABS OVER ABS UM*
  2SWAP XOR ?DNEGATE ;
: SM/REM ( d n -- r q )   \ symmetric signed (AN)
  OVER >R >R              \ R: Dhi n
  DABS R@ ABS UM/MOD      ( r q )
  R> R@ XOR ?NEGATE SWAP
  R>        ?NEGATE SWAP ;   \ Dhi neg?
: FM/MOD ( d1 n1 -- n2 n3 )  \ floored signed (AN)
  >R TUCK                    \ dhi dlo dhi   r: n
  DABS R@ ABS UM/MOD         \ dhi r q
  SWAP R@ ?NEGATE            \ dhi q r*
  SWAP ROT R@ XOR 0<         \ r q neg?
  IF   NEGATE OVER           \ r q* r
       IF   1-               \ r q-1
            R@ ROT - SWAP    \ n-r q-1
       THEN
  THEN RDROP ;
: *      M* DROP ;
: /MOD   >R S>D R> FM/MOD ;
: /      /MOD NIP ;
: MOD    /MOD DROP ;
: */MOD  >R M* R> FM/MOD ;
: */     */MOD NIP ;

\ input/output

\ ----- 09 -----

FORTH:
: EMIT   ( c -- )   (EMIT INCR HOR ;
: CR     ( -- )     0D (EMIT 0A (EMIT FALSE TO HOR INCR VER ;
: SPACE  ( -- )     BL EMIT ;
: SPACES ( n -- )   BL SWAP 0 ?DO DUP EMIT LOOP DROP ;
: TYPE   ( a n -- ) 0 ?DO COUNT EMIT LOOP DROP ;
: PAGE   ( -- )     0C EMIT FALSE TO HOR FALSE TO VER ;

EXTRA:
: BACKSPACE ( -- )
  HOR 0= ?EXIT
  8 BL OVER (EMIT (EMIT (EMIT -1 +TO HOR ;

INSIDE:
: ACCEPTING ( n a i - i )             \ n a i       n=imax, a=adr, i=count
  KEY                                 \ n a i ch
  DUP BL <
  IF
     0D OVER = IF 2NIP DROP }            \ i           char=CR: ready, leave ACCEPTING
     8 = IF DUP IF BACKSPACE 1- THEN RE} \ n a i-      destructive backspace when i<>0
     BL                                  \ n a i bl    ctrl char is replaced by BL
  THEN
  OVER 4 PICK = IF DROP RE}              \ n a i       i=n: no action
  DUP 2OVER + C! EMIT 1+ RE (;)          \ n a i+      store and emit

FORTH:
: ACCEPT ( a n -- i )   \ i=teller (AN) 2004
  SWAP FALSE            \ n a i       n=imax, a=adr, i=count
  ACCEPTING ;

EXTRA:
<----
: DU/MOD ( ud1 u2 -- u3 ud4 ) \ 32/16->32 divide (BJR)
  >R 0 R@ UM/MOD
  ROT ROT R> UM/MOD ROT ;
: DU* ( ud1 u2 -- ud3 ) \ 32*16->32 multiply (BJR)
  DUP >R UM* DROP  SWAP R> UM* ROT + ;
---->

: DU/MOD ( ud1 u2 -- u3 ud4 )   \ 32/16->r=16,q=32 (AN)
  TUCK FALSE SWAP UM/MOD >R SWAP UM/MOD R> ;
: DU* ( ud1 u2 -- ud3 )   \ 32*16->32 (AN)
  TUCK UM* DROP >R UM* R> + ;

FORTH:
: HOLD   -1 +TO HLD  HLD C! ; ( char -- )   \ add char to output string
: <#     PAD TO HLD ;         ( -- )        \ begin numeric conversion

INSIDE:
: >DIGIT ( x -- char )   DUP 9 > 7 AND + 30 + ;

FORTH:
: #      BASE @ DU/MOD ROT >DIGIT HOLD ;   ( ud1 -- ud2 )
: #S     BEGIN # 2DUP OR 0= UNTIL ;        ( ud1 -- ud2 )
: #>     2DROP HLD PAD OVER - ;            ( ud1 -- c-addr u )
: SIGN   0< 0= ?EXIT 02D HOLD ;            ( n -- ) \ add minus sign if n<0

EXTRA: \ (AN)
: DU.STRING  ( du -- a n )   <# #S #> ;
: D.STRING   ( dn -- a n )   TUCK DABS <# #S ROT SIGN #> ;
: RTYPE      ( a n r -- )    2DUP MIN - SPACES TYPE ;
\ : LTYPE      ( a n l -- )    2DUP MIN 2SWAP TYPE - SPACES ;

EXTRA:
: DU.  ( du -- )     DU.STRING TYPE SPACE ;
: DU.R ( du r -- )   >R DU.STRING R> RTYPE ;

FORTH:
: D.   ( d -- )      D.STRING  TYPE SPACE ;
: U.   ( u -- )      0   DU. ;
: .    ( n -- )      S>D D.  ;
: D.R  ( d r -- )    >R     D.STRING  R> RTYPE ;
: U.R  ( u r -- )    >R 0   DU.STRING R> RTYPE ;
: .R   ( n r -- )    >R S>D D.STRING  R> RTYPE ;
: ?         @ . ;
: DECIMAL   0A BASE ! ;
: HEX       10 BASE ! ;

EXTRA:
: BINARY    2  BASE ! ;

FORTH:
: SOURCE ( -- adr n )   IB #IB ;    \  current input buffer
\ : /STRING ( a n i -- a+i n-i )   TUCK - >R + R> ; \ (AN)
CODE /STRING ( a n i -- a+i n-i )   \ (AN) 2004
  D X TFR                    \ i
  S 2 #) ADDD   S 2 #) STD   \ a+i
  S ) LDD   S ) STX          \ n->D i->S)
  S )++ SUBD                 \ n-i
  NEXT END-CODE

\ ----- 10 -----

\ CATCH and (THROW  (AN) 2004
INSIDE:
CODE CATCH( ( xt -- ? )
  REG S PSHU                    \ SP >R
  U -2 #) LEAX   REG X PSHU     \ RP-2 >R
  NEXT END-CODE
CODE )CATCH ( -- 0 )
  U 4 #) LEAU              \ wis gesavede RP en SP
  REG D PSHS   CLRA   CLRB \ goedkeuringsnul
  NEXT END-CODE

FORTH:
: CATCH CATCH( EXECUTE )CATCH ;

\ (THROW always throws and does NOT test on ZERO!
INSIDE:
CODE (THROW ( x -- )   \ (AN) 2004
    D X TFR               \ throw#
  BEGIN
     U D TFR              \ RP
     U )++ CMPD   =?
  UNTIL
     REG S PULU           \ restore SP
     X D TFR              \ throw#
     REG Y PULU   NEXT END-CODE

FORTH:
: ABORT ( ? -- )   -1 (THROW ;

<----
INSIDE:
CODE (LOWER ( ch -- ch2 )  \ (AN)
       CHAR A # CMPB   U<? NO   \ A...
  IF   CHAR Z # CMPB   U>? NO   \ A..Z
  IF   020 # ADDB
  THEN   THEN   NEXT END-CODE 

EXTRA:
: LOWER ( a n -- )   0 ?DO DUP C@ (LOWER OVER C! 1+ LOOP DROP ;
---->

INSIDE:
CODE (UPPER ( ch -- ch2 )  \ (AN)
       CHAR a # CMPB   U<? NO   \ a...
  IF   CHAR z # CMPB   U>? NO   \ a..z
  IF   020 # SUBB
  THEN   THEN   NEXT END-CODE 

EXTRA:
: UPPER ( a n -- )   0 ?DO DUP C@ (UPPER OVER C! 1+ LOOP DROP ;

FORTH:
: COMPARE ( a1 n1 a2 n2 -- 0\-1\+1 )
  ROT 2DUP - >R UMIN         \ a1 a2 n r: n1-n2
  S<> ?DUP IF RDROP }
  R> DUP 0= ?EXIT
  0> 2* 1+ ;
: MOVE ( a1 a2 u -- )   \ (AN) 2004
  2DUP +        \ a1 a2 u a2+u
  2OVER         \ a1 a2 u a2+u a1 a2
  WITHIN IF CMOVE }
  CMOVE> ;

EXTRA:
: PLACE ( src n dst -- )   \ copy to counted string
  2DUP C! CHAR+ SWAP MOVE ;

\ ----- 11 -----

FORTH:
: WORD ( char -- a )        \ (AN) 2004
  >R                        \                        r: char
  SOURCE >IN @              \ BUFA BUFQ POS
  /STRING TUCK              \ rest adr rest
  R@ SKIP                   \ rest worda arest
  OVER SWAP                 \ rest a a arest
  R> SCAN                   \ rest a wordz zrest     r: --
  >R                        \ rest a wordz           r: zrest
  OVER -                    \ rest a wordz-a
  2DUP WRD 2!               \ Voor QUIT en voor DNUMBER? in EVAL
  HERE PLACE                \ rest
  R> DUP 0<> +              \ rest zrest*            r: --
  - >IN +!
  HERE ;
: PARSE ( char -- a n )     \ (AN) 2004
  >R                        \                          r: char
  SOURCE >IN @              \ BUFA BUFQ POS
  /STRING 2DUP              \ a arest a arest
  R> SCAN                   \ a arest stringend zrest  r: --
  2>R R>                    \ a arest zrest            r: stringend
  DUP 0<> + - >IN +!
  R> OVER - ;               \ a n                      r: --

EXTRA:
CODE ?STACK ( -- )  \ See S0 (AN) 2004
  REG D PSHS   S D TFR
  TSTB   0<? NO
  IF   REG D PULS   NEXT
  THEN                                ( sp=100..17F )
  -4 # LDB               ( sp=x80..xFF, x=1 underflow, x=0 overflow )
  TSTA =?
  IF   INCB   THEN   SEX              ( -3 for overflow? )
  ' (THROW TARGA JMP   END-CODE
: ?BASE ( -- )   BASE @ 2 49 WITHIN ?EXIT DECIMAL -3E (THROW ;
: ?PAIR ( x y -- )   = ?EXIT -16 (THROW ;
: ?COMP ( -- )   STATE @ ?EXIT -0E (THROW ;

FORTH:
: COMPILE, ( xt -- )   ?COMP HERE ! CELL +TO HERE ;

INSIDE:
: COMPILE() ( -- )   INLINE# COMPILE, ;

FORTH:
: [ ( -- )   FALSE STATE ! ; IMMEDIATE
: ] ( -- )   TRUE STATE ! ;

\ FLYER for state smart words (AN) 2004
INSIDE:
: SAFE-THERE ( -- a )      \ Reset THERE when not in Flybuf..+40
  40 THERE FLYBUF - U<
  IF FLYBUF TO THERE
  THEN THERE ; 
: FLYER ( -- ) \ R: caller --  THERE  rest-van-FLY  Caller
  STATE @ ?EXIT
  SAFE-THERE
    HERE TO THERE
  DUP TO HERE
  R> 2>R               \ Adres van tijdelijke code
  ] DIVE               \ Maak nu de Caller af en keer terug naar hier.
  POSTPONE EXIT        \ Plak EXIT achter de tijdelijke code.
  POSTPONE [
  HERE THERE TO HERE TO THERE      \ Herstel HERE
  ;                    \ Spring nu naar de tijdelijke code.

<----
INSIDE:
CODE "(S) ( -- a n )
  REG D PSHS
  Y )+ LDB    CLRA
  REG Y PSHS
  Y B) LDY    NEXT END-CODE
---->

INSIDE:
\ : C"(S) ( -- a )   INLINE$ DROP 1- ;
: "(S) ( -- a n )   INLINE$ ;
: ."(S) ( -- )      INLINE$ TYPE ;

FORTH:
: .( ( <txt"> -- )   [CHAR] ) PARSE TYPE ; IMMEDIATE

EXTRA:
: WORD,  ( ch -- )   WORD C@ 1+ ALLOT ;
: PARSE, ( ch -- )   PARSE HERE OVER 1+ ALLOT PLACE ;

INSIDE:
: ABORT"(S) ( flag -- ) \ (AN) 2004
  IF R@ TO MSG#-2 -2 (THROW
  THEN /INLINE$ ;

\ --- R'DAM & A'DAM
FORTH:
: ABORT" ( <txt"> -- )   FLYER POSTPONE ABORT"(S)
  HERE-IS ROTTERDAM
  [CHAR] " PARSE, ; IMMEDIATE 
EXTRA:
: " ( <txt"> -- a n |-- )
  HERE-IS AMSTERDAM
  FLYER POSTPONE "(S)
  [ ROTTERDAM 22 ] AGAIN (;) IMMEDIATE
FORTH:
: S" ( <txt"> -- a n |-- )                [ AMSTERDAM 22 ] AGAIN (;) IMMEDIATE
: ." ( <txt"> -- )   FLYER POSTPONE ."(S) [ ROTTERDAM 22 ] AGAIN (;) IMMEDIATE
\ : C" ( <txt"> -- )   FLYER POSTPONE C"(S) [ ROTTERDAM 22 ] AGAIN (;) IMMEDIATE
EXTRA:
: MSG" ( n <ccc"> -- )
  HERE SWAP , TOPMSG , TO TOPMSG
  [ ROTTERDAM 22 ] AGAIN (;)
\ ---

FORTH:
: DEPTH ( -- n ) SP@ S0 SWAP - 2/ ;

\ ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
\ ----------------- assembler hulpwoordjes --------------------

INSIDE:
: 8BIT?   -80 80 WITHIN ;
: INITMODE ( -- )   \ Default value before starting an instruction
  30 TO MODE ;      \ zie ?ILLEGAL & Doers
: ?ILLEGAL ( flag -- )   0= ?EXIT -3F (THROW ;
: INDEXREG ( regnr postbyte1 -- postbyte2 )   \ zie  DO)MODE  #)
   20 TO MODE
   SWAP  1-  3 OVER U< ?ILLEGAL   \ must be x,y,u, or s (0..3)
   5 LSHIFT OR ;                  \ put reg # in postbyte
<----
    ,  A  B  D  X  Y  U  S
    0  2  4  6  10 20 40 40
---->
:  REGCODE ( ch -- regcode)            \ zie  REG
   [CHAR] Z OVER < BL AND - >R         \ UPPER
   S" ,ABDXYUS87654321"
   [ -8 ALLOT 2 , 406 , 1020 , 4040 , ]
   2/ TUCK R>                          \ 8 List 8 Ch
   SCAN IF + C@ }
   -3F (THROW (;)
: +MODE ( operand1 -- operand2 )   \ change 5x to 0x
   MODE +  DUP 0F0 AND 50 <> ?EXIT 0F AND ;
: PCREL ( operand postbyte -- )   \ PC relative  zie INDEXED
   SWAP HERE 2 + -  DUP 8BIT?     \ Relative offset 8 bit?
   IF  SWAP 0FE AND C, C, }       \ Postbyte + offset8
   1-  SWAP C, , ;                \ Postbyte + offset16
: COFSET ( operand postbyte -- ) \   Constant offset  zie INDEXED
   OVER 0= IF 0F0 AND 4 OR C, DROP }   \ no offset
   OVER -10 10 WITHIN OVER 10 AND 0=   \ 5bit and no indirection?
   AND IF 60 AND SWAP 1F AND OR C, }   \  5 bit offset
   OVER 8BIT? IF 0FE AND C, C, }       \  8 bit offset
   C, , ;                              \ 16 bit offset
: INDEXED ( operand? postbyte -- )
   DUP 8F AND                        \ check postbyte for modes with operands
      DUP 89 = IF DROP  COFSET  }    \ Constant offset
      DUP 8D = IF DROP  PCREL   }    \ PC relative
      DUP 8F = IF DROP  C, ,    }    \ Extended indirect
                  DROP  C, ;         \ Simple modes: postbyte only
: IMMED ( operand opcode-pfa+ -- )
   C@ 1- S>D ?ILLEGAL   \ 0
   IF , }               \ 2
   C, ;                 \ 1

\ ==================== de DOERS (AN) =====================

\ Inherent instructions
INSIDE:
DOER: DOSEX   C@ C, INITMODE ; \ Lay 1 byte
DOER: DOSWI2   @ , INITMODE ; \ Lay cell
DOER: DOCWAI ( operand -- )   \ 8 bit, Immediate instructions
   MODE ?ILLEGAL C@ C, C, INITMODE ;
<----
 Stack action of general addressing instructions
 (1) immediate, direct, extended:                operand --
 (2) all indexed except (3):                    postbyte --
 (3) const.offset, PC, extended indir: operand postbyte --
---->
: GENADR ( adr+ -- )
   MODE INITMODE
   DUP  0 = IF DROP  IMMED         }   \ Immediate
   DUP 10 = IF DROP  DROP C,       }   \ Direct
   DUP 20 = IF DROP  DROP INDEXED  }   \ Indexed
   DUP 30 = IF DROP  DROP ,        }   \ Extended
   ?ILLEGAL ;
DOER: DONEG   \ 2x 8 bit in body, General address instructions
   COUNT +MODE C, GENADR ;
DOER: DOLDY   \ 16 & 8 bit in body, General address instructions
   @+ +MODE , GENADR ;
DOER: DOEXG   \ 8 bit in body, R to R instructions
   C@ C, SWAP 4 LSHIFT ( 10 * ) + C, INITMODE ;
DOER: DOLEA   \ 8 bit in body, Lea instructions
   MODE 20 - ?ILLEGAL
   C@ C, INDEXED INITMODE ;
DOER: DOBEQ   \ 8 bit in body, Conditional branches
   C@  SWAP HERE 2 + -       \ Distance
   INITMODE
   DUP 8BIT?
   IF  SWAP C, C, }          \ 8 bit
   10 C, SWAP C, 2 - , ;     \ 16 bit
DOER: DOBRA   \ 16 bit in body, Unconditional branches
   @  SWAP HERE 2 + -                     \ distance
   INITMODE
   DUP 8BIT?  IF  SWAP BYTESWAP C, C, }   \ 8 bit: use short opcode
   SWAP C, 1- , ;                         \ 16 bit: use long opcode
\ DOER: DOCCON C@ ;   \ 8 bit in body, Conditions, Registers
DOER: DO-) C@ INDEXREG ;   \ 8 bit in body \ Modes

\ -------- De assemblerwoordjes ------

\ Zet geen commentaren binnen in een lijst!
ASSEMBLER:
NEG:
0  40 NEG                             0  43 COM
0  44 LSR                 0  46 ROR   0  47 ASR
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
2 1183 CMPU 2 118C CMPS   -1
LEA:   30 LEAX 31 LEAY 32 LEAS  33 LEAU  -1
EXG:    1E EXG  1F TFR  -1
SEX:
12 NOP   13 SYNC 19 DAA  1D SEX
39 RTS   3A ABX  3B RTI  3D MUL  3F SWI
40 NEGA                  43 COMA
44 LSRA          46 RORA 47 ASRA
48 ASLA
48 LSLA  49 ROLA 4A DECA
4C INCA  4D TSTA         4F CLRA
50 NEGB                  53 COMB
54 LSRB          56 RORB 57 ASRB
58 ASLB
58 LSLB  59 ROLB 5A DECB
5C INCB  5D TSTB         5F CLRB   -1
SWI2:  103F SWI2  113F SWI3   -1
CWAI:    1A ORCC  1C ANDCC
34 PSHS  35 PULS  36 PSHU  37 PULU  3C CWAI  -1
BRA:  2016 BRA  8D17 BSR  -1
BEQ:     21 BRN  22 BHI  23 BLS
24 BHS   25 BLO
24 BCC   25 BCS  26 BNE  27 BEQ
28 BVC   29 BVS  2A BPL  2B BMI
2C BGE   2D BLT  2E BGT  2F BLE  -1
<----
\ 6809 conditions  (Constanten)
CON:
 20 NVR  21 ALW  22 LS   23 HI
 24 LO   25 HS
 24 CS   25 CC   26 EQ   27 NE
 28 VS   29 VC   2A MI   2B PL
 2C LT   2D GE   2E LE   2F GT   -1
---->
\ 6809 conditions, (AN):
\ Forth-achtige 6809 assembler condities.
\ Deze woordjes dekken ALLE condities.
CON:      23 U>?
 24 U<?   24 CS?
 26 =?
 28 VS?   2A 0<?
 2C <?    2F >?    -1
: NO ( cond# -- cond#2 )   1 XOR ;

\ 6809 registers (Constanten)
CON:
0 D       1 X      2 Y      3 U
4 S       5 PC     8 A      9 B
                  0A CCR   0B DP   -1

\ 6809 addressing modes
-):
80 )+     81 )++   82 -)    83 --)
84 )      85 B)    86 A)    8B D)     -1

\ ================ EINDE ASSEMBLER DEEL I ==================


INSIDE:
: PARENTHESIZE ( -- )   ."  (" DIVE ." ) " ;

FORTH:
: .S ( -- )
  ?STACK PARENTHESIZE SPACE
  DEPTH 0= ?EXIT
  DEPTH  BEGIN DUP PICK . 1-
               DUP 0= UNTIL DROP ;

EXTRA:
: U.S ( -- )   \ Unsigned version of .S
  ?STACK PARENTHESIZE SPACE
  DEPTH 0= ?EXIT
  DEPTH  BEGIN DUP PICK U. 1-
               DUP 0= UNTIL DROP ;

EXTRA:
: .MSG ( n -- )   \  msg-body: msg# | link | text..
  -3 OVER U< IF 1+ 0= ?EXIT                \ msg#=-1
                SPACE MSG#-2 COUNT TYPE }  \ msg#=-2
  TOPMSG
     AHEAD
  BEGIN    CELL+ @          \ n 'msg
     /THEN DUP @            \ n 'msg msg#
  WHILE    2DUP @ =
  UNTIL
  THEN                   \ n 'msg
  CELL+ CELL+ COUNT TYPE
  ?DUP 0= ?EXIT
  PARENTHESIZE ." Message # " 0 .R ;

INSIDE:
: .OK ( -- )                      \ (AN) 2005
  ?BASE ?STACK
  OK 1 AND  IF   STATE @ IF   ."  ok"
                         ELSE ."  OK"
                         THEN
            THEN
  CR
  OK 2 AND  IF   .S
            ELSE OK 4 AND IF U.S THEN
            THEN
  OK 8 AND  0= ?EXIT
            0A BASE @ = ?EXIT
            BASE @ DUP DECIMAL 0 .R BASE ! ." ) " ;

\ ----- 12 -----
\ Inputstream

FORTH:
: QUERY ( -- a n )
  TIB DUP TO IB TIBSIZE ACCEPT TO #IB
  0 >IN ! SPACE ;

FORTH:
: REFILL ( -- t/f )   TIB IB = IF .OK QUERY TRUE } FALSE ;

EXTRA:
: WORD> ( ch -- a ) \ a is never a nullstring (AN) 2004
  BEGIN DUP WORD DUP C@ IF NIP }
        DROP >R REFILL 0= IF -10 (THROW THEN
        R>
  AGAIN (;)

INSIDE:
CODE THREAD ( blword -- draadadres )   \ Len 2* Z xor 2* A xor
  D X TFR               \ Counted stringadres
  X ) LDA   A B TFR     \ count
  ASLB   X A) EORB      \ laatste karakter erbij
  ASLB   X 1 #) EORB    \ eerste karakter erbij
  HX 0F # ANDB   ASLB   \ offset in dradenlijst
  3 # ADDB   SEX        \ dictionary adres = 0003
  NEXT END-CODE
: FINDNAME ( blword -- nfa? )   \ nfa? is a valid nfa or zero.  (AN) 2004
  DUP C@ 1+ 20 MIN            \ blword len+1
  2DUP UPPER
  OVER THREAD                 \ blword len+1 lfa
  AHEAD
     BEGIN NAME>LINK          \ blword len+1 lfa
  /THEN    @ DUP              \ blword len+1 nfa/0
     WHILE DUP 2OVER S<> 0=   \ blword len+1 nfa found?
     UNTIL
     THEN                     \ blword len+1 nfa/0
  NIP NIP ;
: FINDWORD ( blword nfa? widstring widcount -- xt imm | blword 0 )
  2>R                            \ a nfa    r: widstring widcount
  DUP
  IF FALSE SWAP                  \ a 0 nfa
     AHEAD
       BEGIN NAME>LINK
             CELL- @             \ a NFA? nfa*
     /THEN   2R@ 2OVER NIP @VOC  \ a 0 nfa widstring widcount wid
             SCAN NIP            \ a 0 nfa rest
             R> OVER - >R
             IF   NIP DUP        \ a NFA* nfa ( this one is OK )
             THEN
             DUP HOM? R@ AND     \ a NFA? nfa meer?
       0= UNTIL
     DROP                       \ a NFA?
     DUP IF NIP                 \ NFA
            DUP NAME>           \ NFA xt
            SWAP @IMM           \ xt imm
         THEN                   \ xt imm | blword 0
  THEN 2RDROP ;

FORTH:
: FIND ( blword -- xt imm )        \ (an) 2004
       ( blword -- blword 0 )
  DUP FINDNAME                 \ blword nfa?
  DUP 0= ?EXIT
  CONTEXT CURRENT OVER -       \ blword nfa? widstring widcount
  FINDWORD ;                   \ xt imm | blword 0
: SEARCH-WORDLIST ( a n wid -- xt imm )
                  ( a n wid -- false )
  >R HERE PLACE               ( -- )  \ r: wid
  HERE DUP FINDNAME           \ blword nfa?
  R> OVER                     \ blword nfa? wid
  IF HERE NAME> TUCK C! 1     \ blword nfa? widstring widcount=1
     FINDWORD                 \ xt imm | blword 0
     DUP ?EXIT                \ xt imm
     FALSE                    \ blword 0 dummy
  THEN DROP NIP ;             \ 0

INSIDE:
: !SECTION ( -- )   HERE TO SECTION ;
: LIT, (  x -- )   \ Compile x as a literal
  DUP 80 -80 WITHIN IF POSTPONE () , !SECTION }
  POSTPONE (C) C, !SECTION ;

FORTH:
: LITERAL  ( x -- ? )           STATE @ 0= ?EXIT LIT, ; IMMEDIATE
: 2LITERAL ( xlo xhi -- ? ? )   STATE @ 0= ?EXIT SWAP LIT, LIT, ; IMMEDIATE

EXTRA:
: >OK ( x -- ) TO OK ;


\ ----- 13 -----

EXTRA:
: DIGIT> ( char -- n true | char false )   \ (AN) 2004
  >R R@ [CHAR] 0 -
  9 OVER U<
  IF      10 OVER U<
    WHILE 7 -
  THEN    DUP BASE @ U< IF TRUE RDROP }   \ tot de 9 en vanaf de A
    THEN  DROP R> FALSE ;                 \ het ongeldige stukje tussen de 9 en de A

FORTH:
: >NUMBER ( dx adr u -- dx2 adr2 u2 )
  DUP 0= ?EXIT
  OVER C@ DIGIT>
  IF   >R 2SWAP BASE @ DU*
       R> M+ 2SWAP 1 /STRING
       RE
  THEN DROP ;

INSIDE:
: MINUS-SIGN? ( a n -- a n false | a+1 n-1 true )   \ Behandel een eventueel minteken.
  DUP
  IF   OVER C@ [CHAR] - = IF 1 /STRING TRUE }
  THEN FALSE ;
: >DOTNUMBER ( a n -- xlo xhi a2 q )
   \ q= -1 : empty string or only dot.
   \ q= 0  : ok, string is converted.
   \ q= +x : wrong character in the string.
  FALSE DUP 2SWAP                \ 0 0 a n
  1- DUP 0=                      \ length=1?
  IF   OVER C@ [CHAR] . = OR     \ do not accept "only dot"
  THEN            S>D ?EXIT      \ empty string or only dot, q=-1
  1+ >NUMBER
  DUP TO DOT? DUP 0=  ?EXIT      \ ok (no dot)
  OVER C@ [CHAR] . <> ?EXIT      \ wrong character
  DUP TO DOT? 1 /STRING >NUMBER ;

EXTRA:
: DNUMBER? ( a n -- xlo xhi true |-- ? ? false )   \ (AN) 2004
  MINUS-SIGN? >R
  >DOTNUMBER NIP          \ xlo xhi q
  IF  FALSE RDROP }       \ ? ? false
  R> ?DNEGATE TRUE ;      \ xlo xhi true

INSIDE:
: EVAL ( BLWORD -- ) \ (AN) 2004
  FIND ?DUP IF STATE @ AND 0< IF , } EXECUTE }
  DROP WRD 2@
  DNUMBER? IF DOT? IF POSTPONE 2LITERAL } DROP POSTPONE LITERAL }
  -3D (THROW (;)
: OK-LOOP ( -- )
  S0 R0 CELL- CELL- !      \ When entering QUIT with numbers on stack.
  BEGIN BL WORD> EVAL AGAIN (;)

FORTH:
: QUIT ( -- )
  CLEAR-R
  BEGIN
        POSTPONE [ QUERY
        ['] OK-LOOP CATCH
        CR INITMODE
        DUP INVERT 0= IF WRD 2@ TYPE SPACE THEN ( -1? )
        .MSG SPACE CLEAR-S
  AGAIN (;)
CODE THROW ( x -- )   \ (AN) 2004
    0 # CMPD   =?   IF   REG D PULS   NEXT   THEN
  -38 # CMPD   =?   IF   REG D PULS   ' QUIT TARGA JMP   THEN
  ' (THROW TARGA JMP
  END-CODE

INSIDE:
: INTERPRET ( a n -- )   \ For EVALUATE -- (AN) 2004
  TO #IB TO IB  0 >IN !
     AHEAD
  BEGIN    EVAL
     /THEN BL WORD DUP C@ 0=
  UNTIL    DROP ;

FORTH:
: EVALUATE ( a n -- )
  SOURCE 2>R >IN @ >R 
  ['] INTERPRET CATCH
  R> >IN ! 2R> TO #IB TO IB
  THROW ;

INSIDE:
: ?FOUND ( t/f -- )  ?EXIT -0D (THROW (;)

FORTH:
: ' ( <name> -- xt | ABORT )   BL WORD> FIND ?FOUND ;
: CHAR   ( <word> -- ch )      BL WORD> 1+ C@ ;
: [CHAR] ( <word> -- )         CHAR POSTPONE LITERAL ; IMMEDIATE

EXTRA:
: CTRL   CHAR 1F AND POSTPONE LITERAL ; IMMEDIATE

FORTH:
: ( ( <tekst> -- )   [CHAR] ) PARSE 2DROP
  >IN @ #IB U< ?EXIT
  >IN @ IF SOURCE + 1- C@ [CHAR] ) = ?EXIT THEN
  REFILL ?RE ; IMMEDIATE
: \ ( <tekst> -- )   #IB >IN ! ;  IMMEDIATE

\ ----- 14 -----
\ ---
FORTH:
: CREATE ( <name> -- )   \ (AN) 2004
  BL WORD>
  HERE-IS AMSTERDAM
  FINDNAME DUP
  >R
  HERE 3 R@ IF CELL+ THEN ALLOT
       DUP HERE OVER C@ 1+ CMOVE>
  !                               \ eventually !homlink
  0                               \ homvocimm byte
  R> IF   CR ." Redefining "
          HERE COUNT TYPE SPACE
          80 OR                   \ homvocimm byte
     THEN
  HERE 1- C!                      \ !homvocimm
  HERE DUP THREAD                 \ a th
  DUP @ HERE NAME>LINK !          \ !link ---
  HERE SWAP !                     \ new top of the thread
  HERE 1-
  CURRENT C@ OVER C@ OR SWAP C!   \ !voc ---
  HERE TO TOPNFA                  \ new topnfa
  C@ 1+ ALLOT                     \ allot name field
  FALSE JSR                       \ allot code field
  DOCREATE !SECTION ;
INSIDE:
: CREA ( stradr len -- )   HERE PLACE HERE [ AMSTERDAM 22 ] AGAIN (;)
\ ---

FORTH:
: RECURSE ( -- )   TOPNFA NAME> COMPILE, ; IMMEDIATE

EXTRA:
: HIDE     TOPNFA DUP  C@ 80 OR SWAP C! ;
: REVEAL   TOPNFA DUP  C@ 7F AND SWAP C! ;

FORTH:
: IMMEDIATE   TOPNFA 1- 1 OVER C@ OR SWAP C! ;
: ['] ( <name> -- )   ' POSTPONE LITERAL ; IMMEDIATE
: [COMPILE] ( <name> -- )   ' COMPILE, ; IMMEDIATE
: POSTPONE ( <name> -- )   \ POSTPONE the action following word
  BL WORD> FIND DUP ?FOUND
  0< IF COMPILE() COMPILE() !SECTION CELL +TO SECTION THEN   \ non-immediate
  COMPILE, ; IMMEDIATE
<----
: ENVIRONMENT?   \ c-addr u -- i*x true    system query
  2DROP 0 ;      \          -- false
---->

EXTRA:
: STOP? ( - true/false )
  KEY? DUP 0= ?EXIT
  DROP KEY
  BL OVER = IF DROP KEY THEN
  1B OVER = -1C AND THROW
  BL <> ;

\ ----- 15 -----


FORTH:
: : ( <name> -- )
  CREATE DO: ] HIDE
  TRUE FALSE >CS ;
: :NONAME
  HERE
  ['] DO: >BODY JSR
  ]
  FALSE FALSE >CS
  !SECTION ;
: CONSTANT ( x <name> -- )
  CREATE DUP 80 -80 WITHIN IF DOCON , }
  DOCCON C, ;
: VARIABLE ( <name -- )      CREATE DOVAR CELL ALLOT ;
: VALUE    ( x <name> -- )   CREATE DOVAL , ;

INSIDE:
DOER: DOSTRING   1+ COUNT ;

EXTRA:
: STRING ( n <name> -- )
  CREATE DOSTRING FF AND 1 MAX DUP C, FALSE C, ALLOT ;

INSIDE:
: TO$() ( a n inl-body -- )
  INLINE# DUP 1+ >R
  C@ UMIN
  R> PLACE ;
: +TO$() ( a n inl-body -- )
  INLINE# DUP 1+ >R
  C@ R@ C@ - UMIN
  R@ COUNT + SWAP
  DUP R> C+!
  MOVE ;
: INCR$() ( ch <name> -- )
  INLINE# DUP 1+ >R
  C@   R@ C@
  > IF R@ COUNT + C! 1 R> C+! }
  DROP RDROP ;
PFXLIST ] DOSTRING TO$() +TO$() INCR$() [
PFXLIST ] DOVAL    TO()  +TO()  INCR() [
: PFXLIST   TOPPFX , HERE TO TOPPFX ;
: PFX ( offset-in-pfxlist <name> -- )   \ (AN) 2004
  ' >BODY
  DUP CELL- @ BODY>             \ n data-body doer-xt
  TOPPFX                        \ n data-body doer-xt pfx-list
  BEGIN 2DUP @ =                \ juiste type?
        IF  NIP CELL+ ROT + @   \ data-body pfx-actie
            FLYER
          \ DUP >NAME @IMM 0< IF EXECUTE }
            , , }
        CELL- @  DUP 0=         \ volgende pfx-list
  UNTIL -20 (THROW (;)

FORTH:
: TO   ( <name> -- )   0 PFX ; IMMEDIATE
EXTRA:
: +TO  ( <name> -- )   2 PFX ; IMMEDIATE
: INCR ( <name> -- )   4 PFX ; IMMEDIATE

EXTRA:
: VARIABLES ( n <name> -- )   CREATE CELLS ALLOT DOVARS ;

\ ----- 16 -----

INSIDE:
: <FUSE ( 3-inline-tokens -- )
 ?COMP R>
 @+ HERE CELL- @ =
 SECTION HERE 1- U< AND
 IF   -2 ALLOT CELL+ @+ ,
 ELSE @+ , CELL+
 THEN >R ;
\ When xt1 is not the last compiled word: compile xt2
\ Otherwise: overwrite compiled xt1 with xt3
\ See ?EXIT IF UNTIL ?RE

EXTRA:
: ?EXIT   <FUSE 0= EXIT-ON-TRUE EXIT-ON-FALSE ; IMMEDIATE

\ --- A'DAM
FORTH:
: IF    ( -- sysif )   <FUSE 0= IF() IFZERO()
  HERE-IS AMSTERDAM HERE DUP , 1 >CS ; IMMEDIATE
: AHEAD ( -- sysif )           POSTPONE GOTO() [ AMSTERDAM 22 ] AGAIN (;) IMMEDIATE
\ ---

FORTH:
: WHILE ( sys -- sysif sys )   POSTPONE IF 1 CS-ROLL ; IMMEDIATE
: THEN  ( syfif -- )           ?COMP CS> 1 ?PAIR HERE SWAP ! !SECTION ; IMMEDIATE
: BEGIN ( -- sysbegin )        ?COMP HERE 2 >CS !SECTION ; IMMEDIATE
: UNTIL ( sysbegin -- )        CS> 2 ?PAIR <FUSE 0= IF() IFZERO()   , ; IMMEDIATE
: AGAIN ( sysbegin -- )        CS> 2 ?PAIR POSTPONE GOTO() , ; IMMEDIATE
: ELSE  ( sysif1 -- sysif2 )   POSTPONE AHEAD 1 CS-ROLL POSTPONE THEN ; IMMEDIATE
: REPEAT ( sysif sysbegin -- ) POSTPONE AGAIN POSTPONE THEN ; IMMEDIATE

\ --- R'DAM
FORTH:
: DO  ( -- sysdo )   POSTPONE DO() HERE-IS ROTTERDAM HERE DUP , 3 >CS ; IMMEDIATE
: ?DO ( -- sysdo )   POSTPONE ?DO() [ ROTTERDAM 22 ] AGAIN (;) IMMEDIATE
\ ---

\ --- A'DAM
FORTH:
: LOOP ( sysdo -- )
  CS> 3 ?PAIR POSTPONE  LOOP()
  HERE-IS AMSTERDAM DUP CELL+ , HERE SWAP ! ; IMMEDIATE
: +LOOP ( sysdo -- )
  CS> 3 ?PAIR POSTPONE +LOOP() [ AMSTERDAM 22 ] AGAIN (;) IMMEDIATE
\ ---

: ; ( sys: -- )
  CS> FALSE ?PAIR IF REVEAL THEN POSTPONE EXIT  POSTPONE [ ; IMMEDIATE

EXTRA:
: }   ( sysif -- )   POSTPONE EXIT POSTPONE THEN ; IMMEDIATE

\ --- A'DAM
EXTRA:
: RE  ( -- )   POSTPONE GOTO() HERE-IS AMSTERDAM TOPNFA NAME> >BODY , ; IMMEDIATE
: ?RE ( -- )   <FUSE 0= IFZERO() IF() [ AMSTERDAM 22 ] AGAIN (;) IMMEDIATE
\ ---

EXTRA:
: RE} ( sysif -- )   POSTPONE RE   POSTPONE THEN ; IMMEDIATE

INSIDE:
DOER: DOONLY
C@ CURRENT 1-    2DUP C!
1-   DUP TO CONTEXT   C! ;
DOER: DOVOC   C@ CONTEXT C! ;

FORTH:
  MAKEONLY ONLY        \ 0

ONLY:
  VOCABULARY FORTH     \ 2
  VOCABULARY INSIDE    \ 4
  VOCABULARY EXTRA     \ 6
  VOCABULARY ASSEMBLER \ 8

\ Search order words (an)

FORTH:
: WORDLIST ( -- v#=wid )
  HERE
  TOPVOC DUP C@ 2 + C, ,
  DUP TO TOPVOC C@ ;

ONLY:
: ALSO ( -- )
  FINDSTACK CONTEXT U< 0= -31 AND THROW
  CONTEXT C@  -1 +TO CONTEXT
  CONTEXT C! ;
: PREVIOUS ( -- )
  CONTEXT 1+ CURRENT U< 0= -32 AND THROW
  INCR CONTEXT ;
: DEFINITIONS   CONTEXT C@ CURRENT C! ;
: GET-CURRENT ( -- wid )   CURRENT C@ ;
: SET-CURRENT ( wid -- )   CURRENT C! ;

INSIDE:
: VOCNAME ( wid -- a n )
  TOPVOC
  BEGIN 2DUP C@ =
        IF NIP BODY> >NAME COUNT 1F AND
        }  1+ @ DUP 0=
  UNTIL 2DROP S" ?" ;

EXTRA:
: .VOC ( wid -- )  VOCNAME TYPE ;

ONLY:
: ORDER ( -- )   \ (AN) 2004
  PARENTHESIZE
  CONTEXT CURRENT OVER -
  0 DO COUNT .VOC SPACE
  LOOP ." : " C@ .VOC ;
: FRESH   ONLY EXTRA ALSO FORTH ALSO ;

EXTRA:
: VOCABULARY   CREATE WORDLIST DROP DOVOC ;

INSIDE:
: !TOPNFA ( -- )
  FALSE 23 3                    \ DICTIOARY
  DO         I @ ORIGIN - UMAX
  CELL +LOOP ORIGIN + TO TOPNFA ;
: CURTAIL ( fence here linkfield distance -- fence here linkfield2 )
  >R
  AHEAD
     BEGIN
        R@ +    \  object-adr + distance = linkfield-adr
        @
  /THEN
        DUP 2OVER WITHIN 0=
     UNTIL RDROP ;
: (FORGET ( fence  -- )
  HERE 23 3                      \ DICTIONARY
  DO  I @ -3 CURTAIL I !
      CELL
  +LOOP
  TOPVOC  1 CURTAIL TO TOPVOC
  TOPMSG  2 CURTAIL TO TOPMSG
  TOPPFX -2 CURTAIL TO TOPPFX
  - ALLOT !TOPNFA ;

\ --- A'DAM
FORTH:
: FORGET ( <name> -- )
  BL WORD> COUNT CURRENT C@ SEARCH-WORDLIST ?FOUND
  >NAME                                \ NFA
  HERE-IS AMSTERDAM
  DUP NAME>LINK SWAP HOM? 2 AND -      \ fence
  HERE OVER U< -0F AND THROW (FORGET ; \ OK for RAM and ROM version
EXTRA:
: REMOVE ( -- )   \ Remove last word when hidden (AN) 2004
  TOPNFA C@ 80 AND 0= ?EXIT
  REVEAL TOPNFA DUP COUNT TYPE SPACE           \ NFA
  [ AMSTERDAM 22 ] AGAIN (;)   \ See FORGET
\ ---

INSIDE:
DOER: DOMARKER
  DUP @ (FORGET                   \ vergeet vanaf oldhere
  CELL+ COUNT DUP TO CONTEXT      \ herstel CONTEXT = adres < 100
  CURRENT OVER - 1+ MOVE ;        \ herstel zoekstack-vocs

FORTH:
: MARKER ( <name> -- )   \ (AN) 2004
  HERE CREATE DOMARKER
  ,                                  \ oldhere
  CONTEXT DUP C,                     \ save CONTEXT = adres < 100
  HERE CURRENT CONTEXT - 1+
  DUP ALLOT MOVE ;                   \ save zoekstack-vocs

EXTRA:
: ANEW   ( <name> -- )   \ (AN) 2004
  >IN @ >R
  BL WORD DUP C@ 0= -20 AND THROW \ no refill because of saving >IN
  FIND 0<> AND ?DUP
  IF   DUP 1+ @ BODY>
       ['] DOMARKER = AND ?DUP IF EXECUTE THEN     
  THEN R> >IN ! MARKER ;

\ ----- 17 -----

INSIDE:
: !HIMEM ( -- )   \ test eerste cell per 2K RAM (AN) 2004
  -800 TO HIMEM
  BEGIN  800 +TO HIMEM
         HIMEM @             ( x )     \ lees
         DUP INVERT HIMEM !  ( x )     \ store geinverteerde x
         HIMEM @             ( x xi? ) \ lees het terug
         OVER HIMEM !        ( x xi? ) \ zet correcte x terug
         INVERT <>           ( vlag )  \ ongelijk?
  UNTIL ; \ laagste niet bestaande RAM adres staat nu in HIMEM

FORTH:
: UNUSED ( -- n )   HIMEM 20 - HERE - ;

EXTRA:
CODE COLD ( ? -- )   \ cold start Forth system (AN) 2004
  CLRA      A DP TFR          \ initial DP, direct page
  ' S0 >BODY @ # LDS           \ initial SP
           REG D PULS
  ' R0 >BODY @ # LDU           \ initial RP
  ' DO: 3 + TARGA JSR          \ Overgang naar hilevel code
 END-CODE
 ]
 ORIGIN 0 [ UOFFSET ] LITERAL CMOVE
 !HIMEM  !TOPNFA 0 TO CS#
 SAFE-THERE DROP
 FRESH DEFINITIONS
 7F !USART
 CR 0 .MSG
 CR ." Copyright (c) 2005 HCC Forth-gg"
 CR HIMEM 0A RSHIFT  9 .R ."  kB RAM"
 CR CR QUIT [

INSIDE:
: (DOES>  ( -- ) R> !DOER ;   \ TOPNFA NAME> 1+ ! ;

FORTH:
: DOES>
  CS> FALSE OVER ?PAIR >CS
  POSTPONE (DOES>
  ['] DODOES JSR
  !SECTION ; IMMEDIATE
: CODE ( <name> -- )  CREATE -3 ALLOT ASSEMBLER HIDE TRUE 5 >CS ;
: ;CODE
  CS> FALSE ?PAIR 5 >CS
  POSTPONE (DOES>
  ASSEMBLER
  POSTPONE [ ; IMMEDIATE

EXTRA:
: DOER: ( <name> -- ) : DODOER ['] DODOES JSR ;
: DOERCODE ( <name> -- )  CODE 3 ALLOT DODOER ;

ASSEMBLER:
: END-CODE
  CS> 5 ?PAIR IF REVEAL THEN
  PREVIOUS ALSO ;

<----
INSIDE:
DOER: DOIGNORE ( a -- )
  DUP C@ 1+ 2>R
  BEGIN BL WORD> 2R@ S<> 0=
  UNTIL 2RDROP ;
EXTRA:
: IGNORE ( <name> <name> -- )   \ Skipper and delimiter, (AN) 2004
  CREATE BL WORD> C@ 1+ ALLOT DOIGNORE IMMEDIATE ;
\ Voorbeeld:
\ IGNORE <<< >>>  \ FORTH will now skip text between <<< and >>>
\ IGNORE AAA ZZZ  \ ZZZ is Case sensitive!
---->

\ Interrupt vectoren

EXTRA:
: !VECTOR ( routineadres vec -- )   1+ ! ;   \ vb: C4A5 'SWI3 !VECTOR 
: ENABLE  ( vec -- )   07E SWAP C! ;   \ ( JMP )   'SWI3  ENABLE
: DISABLE ( vec -- )   03B SWAP C! ;   \ ( RTI )   'SWI3  DISABLE

EXTRA:
: MANY ( -- )   >IN @ STOP? AND >IN ! ;
: TIMES ( n -- )
  #TIMES 1+ >R
  0 TO #TIMES
  R@ =               \ Last time?
  STOP?              \ User interrupt?
  OR IF RDROP }      \ No repeat
  R> TO #TIMES       \ Repeat
  0 >IN ! ;


\ ----- 18 -----

<----
: /WORDS \ Per draad (an) 2004
  3 10 0                     \ 3 = DICTIONARYadr
  DO CR I .                 \ .DRAADNR
     DUP @     0 >R
     BEGIN   DUP COUNT 7F AND 
             DUP HOR + 4E > IF CR ELSE SPACE THEN
             TYPE
             R> 1+ >R
             NAME>LINK @
     DUP 0= UNTIL DROP ."  -- " R> .
     2 +
     NOMORE? IF LEAVE THEN
  LOOP DROP ;
---->

\ (AN) 2004 -- WORDS

INSIDE:
: WORDSKIPPER ( lfa wid -- nfa? )
  SWAP                   \ wid lfa
     AHEAD
  BEGIN    NAME>LINK     \ wid lfa
     /THEN @             \ wid nfa/0
           DUP
  WHILE    2DUP @VOC =   \ wid nfa flag
  UNTIL
  THEN                   \ wid nfa/0
  NIP ;
: (WORDS ( x y -- ) \ (AN) 2004
  SAFE-THERE 2!
  THERE 24 + DUP 20 -          \ T24 T4
  3                            \ DICTIONARYadr
  OVER 20 CMOVE                \ Store the threads at THERE+4
  2DUP                         \ T24 T4 T24 T4
  DO   I THERE 2@ EXECUTE I !  \ Skipper
       CELL
  +LOOP
  CR 0 >R                      \ Woordenteller
  BEGIN              \ T24 T4
     FALSE -1                  \ Voor Relatieve-NFA en Draadadres
     2OVER
     DO I @                               \ NFA?
           IF   OVER I @ ORIGIN - U<      \ Hoogste?
                IF   2DROP I @ ORIGIN - I \ RelatiEve-NFA Draada
                THEN
           THEN CELL
     +LOOP           \ Grootste-relatieve-NFA Draadadres | 0 -1
     NIP                      \ T24 T4 Draadadres-or-True
     S>D STOP?                \ Klaar of Stoppen?
     OR IF DROP 2DROP CR R> PARENTHESIZE 0 .R }       \ \ \ \ \ e x i t
     3C HOR U< IF CR THEN     \ Positie op de regel
     R> 1+ >R                 \ Woordenteller
     DUP @                    \ Draada NFA
     DUP COUNT                \ Draada NFA a n
     DUP 20 < IF   BL
              ELSE 1F AND [CHAR] ~
              THEN EMIT TYPE SPACE
     NAME>LINK                \ Draada Lfa
     THERE 2@ EXECUTE         \ Draada Next-NFA
     SWAP !
  AGAIN (;)

ONLY:
: WORDS    CONTEXT C@ ['] WORDSKIPPER (WORDS ;

EXTRA:
: ALLWORDS   ['] @      ['] EXECUTE     (WORDS ;
\ : DWORDS   CURRENT C@ ['] WORDSKIPPER (WORDS ;

INSIDE:
: X.R! ( -- n )   FF S>D DU.STRING NIP THERE C! ;   \ Zie .ADR .ASC
: .ADR ( a -- )   THERE C@ 2* U.R ;
: .BYTE ( c -- )  THERE C@ .R ;
: .ASC  ( ch -- ) DUP 7F < AND BL MAX EMIT ;
\ DUMP voor alle grondtallen, met noodstop.
FORTH:
: DUMP ( a n -- )   \ (AN) 2004
  X.R!                                     \ Zie .ADR
  BASE @ 10 MIN DUP 6 < IF 2* THEN >R      \ aantal bytes per regel
  OVER + SWAP                              \ tot vanaf
  BEGIN DUP CR .ADR SPACE                  \ tot vanaf
        R@ 0 DO DUP I + C@ .BYTE SPACE
        LOOP ." |"                         \ tot vanaf
        R@ 0 DO COUNT .ASC
        LOOP ." | "                        \ tot vanaf*
        2DUP SWAP - R@ U<                           \ einde bereikt?
        STOP? OR
  UNTIL 2DROP RDROP ;


\ Decompiler (AN) 2004
INSIDE:
: CFA?? ( adr -- vlag )
  300 OVER U<
  OVER ORIGIN HERE WITHIN AND
  SWAP 1- DUP C@ 21 7F WITHIN AND AND  DUP 0= ?EXIT
  1                         ( adr teller )
  BEGIN >R 1- R> OVER C@    ( adr-1 teller char )
        2DUP = IF 2DROP 0<> }  \ exit with true-flag
        21 7F WITHIN
  WHILE 1+ BL OVER AND       ( adr teller+1  x )
  UNTIL
  THEN  2DROP FALSE ;
: CFA? ( adr -- vlag )
  DUP CFA?? AND   DUP 0= ?EXIT
  >NAME   TOPVOC C@ OVER @VOC < 0= AND
  DUP 0= ?EXIT
  NAME>LINK @          DUP 0= IF 1- }
  DUP C@ 0 20 WITHIN IF NAME> CFA?? }
  DROP FALSE ;

: .HEAD ( a -- )   \ hier begint een header
  DUP S"   --  " 2>R 2R@ TYPE
  >NAME COUNT TYPE
  2R@ TYPE
  DUP 1+ @ BODY>
  DUP CFA?                        \ doer?
  IF   DUP ." doer "
       >NAME COUNT TYPE
  THEN
  DROP 2R> TYPE
  >NAME @VOC .VOC ."  Word" ;
: .TOKEN ( a cfa -- a )   \ Gecompileerd token
  OVER 1 AND 2* 2* 4 + SPACES
  >NAME COUNT TYPE ;
: DECOM ( a -- )
  CR  DUP .ADR ." : "
  DUP COUNT DUP .BYTE SPACE .ASC SPACE
         C@ DUP .BYTE SPACE .ASC SPACE
  DUP @ .ADR BL OVER 1 AND IF 0E + THEN EMIT SPACE
  DUP CFA? IF   DUP .HEAD 1+ }
  DUP @ CFA?
  IF DUP @ .TOKEN
     1+
     DUP CFA? ?EXIT
     DUP @ CFA? ?EXIT
     1+ } 
  1+ ;

EXTRA:
: MSEE ( a -- ) X.R!   \ Used by .ADR .ASC
  BEGIN DECOM STOP? UNTIL DROP ;

FORTH:
: SEE   ' MSEE ;

\ ----- 19 -----
\  tijdelijke BASE (AN) 2004

INSIDE:
DOER: DOFFBASE
  BASE @ >R
  C@ BASE !
  BL WORD>
  ['] EVAL CATCH
  R> BASE ! THROW ;

\ In metacompiler:
\ : FFBASE ( tempbase <name> -- )   XHEADER MET-DOER DOFFBASE C, XIMMEDIATE ;

INSIDE:
: FFBASE ( tempbase <name> -- )   CREATE DOFFBASE C, IMMEDIATE ;   \ (AN) 2004

ONLY:
10 FFBASE HX   \ direct hexadecimal
0A FFBASE DM   \ direct decimal
 2 FFBASE BN   \ direct binary

ONLY:
: [THEN] ; IMMEDIATE

INSIDE:
: [CONDITIONAL] ( 0 -- )   \ (AN) 07dec2005
     AHEAD
  BEGIN    DROP
     /THEN BL WORD> DUP 1+ C@ [CHAR] [ =
  UNTIL               \ Yes, first char = [
  COUNT 1 /STRING 2DUP UPPER
  2DUP S" THEN]"  COMPARE 0=  IF 2DROP  0= ?EXIT RE}
  2DUP S" ELSE]"  COMPARE 0=  IF 2DROP  ?DUP 0= ?EXIT RE}
  2DUP S" IF]"    COMPARE 0=  IF 2DROP  DUP 1+ RE}
       S" AHEAD]" COMPARE 0=  IF        DUP 1+ THEN
  RE (;)

ONLY:
: [ELSE]  ( -- )     0 [CONDITIONAL] ; IMMEDIATE
: [AHEAD] ( -- )     POSTPONE [ELSE] ; IMMEDIATE
: [IF] ( vlag -- )   ?EXIT POSTPONE [ELSE] ; IMMEDIATE

FORTH:
: MS ( x -- ) 0 ?DO 12 0 DO LOOP LOOP ;

\ =========== ASSEMBLER CODA ==========

\ 6809 addressing modes
ASSEMBLER:
: #   0 TO MODE ;
: REG ( "lijst" -- regbyte )   \ voorbeelden:  REG D,X  REG X  REG X,Y
  0 BL WORD
  COUNT 0                    ( 0=regbyte  adres  count )
  ?DO                        ( regbyte  adres )
       COUNT
       REGCODE SWAP >R OR R> ( regbyte2 adres ) \ Bouw reg byte op
  LOOP
  DROP FLYER LIT, POSTPONE # ; IMMEDIATE
: ALLREG   0FF # ;             \ voor push/pull van alle registers
: DP)   10 TO MODE ;        \ DP relative
: #)     SWAP 89 INDEXREG ;   ( rval n -- n postbyte ) \ indexregister + offset
: PC)   20 TO MODE 8D ;      ( n -- n postbyte ) \ pc relative
: []
  MODE
  20 = IF  DUP 9D AND
           80 = ?ILLEGAL
           10 + }             \ Indexed:  postbyte -- postbyte
  20 TO MODE 9F ;             \ Extended: n -- n postbyte

\ 6809  structured conditionals with compiler controll
: IF    ( cond# -- cs: ifadr 6 )   C, 0 C, HERE 6 >CS ;
: AHEAD ( -- cs: aheadadr 6 )      20 ( NVR ) IF ;
: THEN  ( cs: adr 6 -- )
  CS> 6 ?PAIR HERE OVER -
  DUP 8BIT? 0= ?ILLEGAL SWAP 1- C! ;
: BEGIN  ( c": -- beginadr 7 )          HERE 7 >CS ;
: UNTIL  ( cond# cs: beginadr 7 -- )    CS> 7 ?PAIR SWAP C, HERE 1+ -
                                        DUP 8BIT? 0= ?ILLEGAL C, ;
: AGAIN  ( cs: beginadr 7 -- )          20 ( NVR ) UNTIL ;
: ELSE   ( cs: ifadr 6 -- elseadr 6 )   AHEAD 1 CS-ROLL THEN ;
: REPEAT ( cs: whileadr 6 beginadr 7 -- )   AGAIN THEN ;
: WHILE  ( cond# cs: adr n -- whileadr 6 adr n )   IF 1 CS-ROLL ;
: NEXT  Y )++ [] JMP ;   \ 6809 Direct Threaded Code

\ ----- 20 -----
\ THROW messages

FORTH:

   0 MSG" MaisForth an601" \ Default message

' TOPMSG 3 + @ ORIGINHOSTA + @ 4 +
' MSG#-2   3 + @ ORIGINHOSTA + !   \ Default pointer in msg#-2
         -3 MSG" Stack overflow"
         -4 MSG" Stack underflow"
( -13 ) -0D MSG" Can't find"
( -14 ) -0E MSG" Only compiling"
( -15 ) -0F MSG" Protected"
( -16 ) -10 MSG" End of input"
( -22 ) -16 MSG" Structure error"
( -28 ) -1C MSG" User interrupt"
( -32 ) -20 MSG" Invalid name argument"
( -49 ) -31 MSG" Search order overflow"
( -50 ) -32 MSG" Search order underflow"
( -61 ) -3D MSG" What's this?"
( -62 ) -3E MSG" BASE is reset to decimal"
( -63 ) -3F MSG" Illegal addressing mode"
\ ( -64 ) -40 MSG" Ivalid Baud rate"

\ store starting adres on last memory address - 2 

' COLD ORIGINHOSTA -2 + COMPILE!     \ Resetvector vullen 
' COLD ORIGINHOSTA 1 + COMPILE!      \ Jump naar COLD (op ORIGIN)

;;;MAIS;;;

<---- ANS:
Throw#   Reserved for
---      --- 
 -1      ABORT
 -2      ABORT"
 -3      stack overflow
 -4      stack underflow
 -5      return stack overflow
 -6      return stack underflow
 -7      do-loops nested too deeply during execution
 -8      dictionary overflow
 -9      invalid memory address
 -10     division by zero
 -11     result out of range
 -12     argument type mismatch
 -13     undefined word
 -14     interpreting a compile-only word
 -15     invalid FORGET
 -16     attempt to use zero-length string as a name
 -17     pictured numeric output string overflow
 -18     parsed string overflow
 -19     definition name too long
 -20     write to a read-only location
 -21     unsupported operation (e.g., AT-XY on a too-dumb terminal)
 -22     control structure mismatch
 -23     address alignment exception
 -24     invalid numeric argument
 -25     return stack imbalance
 -26     loop parameters unavailable
 -27     invalid recursion
 -28     user interrupt
 -29     compiler nesting
 -30     obsolescent feature
 -31     >BODY used on non-CREATEd definition
 -32     invalid name argument (e.g., TO xxx)
 -33     block read exception
 -34     block write exception
 -35     invalid block number
 -36     invalid file position
 -37     file I/O exception
 -38     non-existent file
 -39     unexpected end of file
 -40     invalid BASE for floating point conversion
 -41     loss of precision
 -42     floating-point divide by zero
 -43     floating-point result out of range
 -44     floating-point stack overflow
 -45     floating-point stack underflow
 -46     floating-point invalid argument
 -47     compilation word list deleted
 -48     invalid POSTPONE
 -49     search-order overflow
 -50     search-order underflow
 -51     compilation word list changed
 -52     control-flow stack overflow
 -53     exception stack overflow
 -54     floating-point underflow
 -55     floating-point unidentified fault
 -56     QUIT
 -57     exception in sending or receiving a character
 -58     [IF], [ELSE], or [THEN] exception
---->
