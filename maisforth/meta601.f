\ dec2005 -*- Forth -*-


\ maisforth metacompiler - Albert Nijhof - 06jun2005

\ META I

MARKER -META
FORTH ALSO DEFINITIONS
DECIMAL

\ <---- Intro, uitbreiding van de Host Forth ---->
\ Onderstaande 2 grootheden moeten met de hand ingevuld worden
\ voordat het metacompileren begint. Zie begin van de Target file.

HEX  C000 VALUE ORIGINTARGA \ Startadres van de nieuwe Forth.
HEX   5F VALUE USERBYTES    \ ORIGIN until ORIGIN+USERBYTES: area with cold data.
DECIMAL

\ Error messages
: ?NOTYET     ABORT"  Bestaat nog niet " ;    \ (KOMPILE (MET-DOER xPOSTPONE x'
: ?UNKNOWN    ABORT"  Wat is dit? " ;         \ >NUM HERE-IS
: ?INPUT      ABORT"  Geen input " ;          \ BL-WORD x[CHAR]
: ?INTERRUPTED ABORT"  Afgebroken " ;          \ WAIT/GO :::MAIS:::
: ?STACK      DEPTH 0< ABORT"  Stack leeg " ; \ .STACK
: ?USERSPACE  ABORT"  Te weinig userbytes " ; 
: ?PREFIX     ABORT"  Niet geschikt voor prefixes " ;
: ?PAIR   ( x y - ) <> ABORT" Afgekeurd " ;

\ Short for 'EXIT THEN'
: } POSTPONE EXIT POSTPONE THEN ; IMMEDIATE

\ Add text to dictionary as a counted string. Zie IGNORE xHEADER x" x."
: STRING, ( a n -- )
  HERE SWAP C, COUNT DUP ALLOT MOVE ALIGN ;

\ Read next word, doing a REFILL if necessary.
: BL-WORD ( -- countedstring )
  BEGIN  BL WORD DUP C@ IF } DROP REFILL 0= ?INPUT AGAIN ;

: DOIGNORE        \ Ignore text until closing
  DOES> COUNT     \     string is encountered.
  BEGIN BL-WORD COUNT 2OVER COMPARE 0= UNTIL 2DROP ;
      
: IGNORE ( <startstring> <sluitstring> -- )
  CREATE IMMEDIATE DOIGNORE BL WORD COUNT STRING, ;

IGNORE <---- ----> \ Skip any text between <---- and ---->

<----  Forth skips the following lines.
       Forth slaat de volgende regels over.

DOIGNORE is alvast een voorbeeld van een DOES-deel dat
eerder gedefiniëerd wordt dan het CREATE-deel.
In de Target Forth kun je met deze werkwijze voorwaartse
referenties vermijden.

DOIGNORE is a DOES-part that is defined before
the definition of the CREATE-part. This method makes it
possible to avoid forward references in the Target. 
---->


\ Destructive MARKER
: ANEW ( <naam> -- )
  >IN @ >R
  BL WORD FIND IF DUP EXECUTE THEN DROP
  R> >IN ! MARKER ;

\ Converting a string into a number 
\ Getallen inlezen
\ Behandel een eventueel minteken.
: MINUS-SIGN? ( a n -- a n false | a+1 n-1 true )
  DUP
  IF  OVER C@ [CHAR] - =
      IF 1 /STRING TRUE
      }  FALSE
  THEN ;

: NUM? ( blword -- xlo true )
       ( blword -- ? false )
  COUNT MINUS-SIGN? >R DUP
  IF   FALSE DUP 2SWAP >NUMBER 0= NIP NIP \ xlo t/f
  THEN R> IF SWAP NEGATE SWAP THEN ;

\ Counted string --> single number (minteken wordt geaccepteerd)
: >NUM ( blword -- x ) \ DOFFBASE WINTERPRET
  NUM? 0= ?UNKNOWN ;

<----
>NUM zet een counted string om in een getal.
Alleen single getallen, positief of negatief.
---->

\ Tijdelijke BASE
: DOFFBASE
  DOES> ( body-met-base <ccc> -- x )
        ( body-met-base <ccc> -- )
      BASE @ >R
      @ BASE !          \ hhh
      BL-WORD
      DUP NUM?
      IF NIP STATE @ IF POSTPONE LITERAL THEN
         R> BASE ! }
      DROP FIND
      DUP 0= IF R> BASE ! 0= ?UNKNOWN THEN
      STATE @ 0<> = IF COMPILE, ELSE EXECUTE THEN
      R> BASE ! ;

: FFBASE ( tempbase -- ) CREATE , IMMEDIATE DOFFBASE ;

DECIMAL
16 FFBASE HX
10 FFBASE DM
 2 FFBASE BN


<----
ORIGINHOSTA is het beginadres (32bits) van de image die in de Host
ge-meta-compileerd wordt. Dit adres wordt automatisch bepaald
bij het starten van de metacompiler. Zie :::MAIS:::
---->

       0 VALUE ORIGINHOSTA \ Zie :::MAIS:::



\ adresformaten
<---- qqq
HOSTA maakt van een 16bits Target adres een 32bits Host adres.
TARGA maakt van een 32bits Host adres een 16bits Target adres.
---->

: HOSTA ( xa - a)  ORIGINTARGA - ORIGINHOSTA + ; \ Zie xFIND
: TARGA ( a - xa ) ORIGINHOSTA - ORIGINTARGA + ; \ Zie xCOMPILE, xCOMPILE!

\ Host cel = 32 bits, Target cel = 16 bits.
\ Host needs alignment, Target doesn't.

VARIABLE xSTATE   0 xSTATE !


: WAIT/GO ( -- ) \ Voor .HERE TARGDUMP
  KEY? 0= IF }
  2 0 DO KEY HX 1B = LOOP
  OR ?INTERRUPTED ;        \ Stop bij [ESC]

: .STACK  ( -- ) \ Voor .HERE
  ?STACK 
  ." ( "  DEPTH IF 0 DEPTH 2 - DO I PICK . -1 +LOOP THEN
  ." ) " ; 
: DOTCELL    ( x -- )       0 <# # # # # #> TYPE ;
: DOTBYTE    ( x -- )       0 <# # # #> TYPE ;
: RTYPE ( adr len r -- )    OVER MAX OVER - >R TYPE R> SPACES ;

TRUE VALUE TRACER
: TRACE TRUE TO TRACER ;
: NOTRACE FALSE TO TRACER ;

: .HERE: xSTATE @ IF } CR HERE TARGA DOTCELL  DM 11 SPACES ;

: .CELL      ( x -- )       TRACER IF DOTCELL 2 SPACES } DROP ;
: .CELL,     ( x -- )       TRACER IF .HERE: DOTCELL ." ,  " } DROP ;
: .CELLSTORE ( x hosta -- ) TRACER IF SWAP DOTCELL ."  ->"
                                      TARGA DOTCELL 2 SPACES } 2DROP ;

: .BYTE      ( ch -- )      TRACER IF DOTBYTE 2 SPACES } DROP ;
: .BYTE,     ( ch -- )      TRACER IF DOTBYTE ." ,  " } DROP ;
: .BYTESTORE ( x hosta -- ) TRACER IF SWAP DOTBYTE ."  ->"
                                      TARGA DOTCELL 2 SPACES } 2DROP ;

: .NAAM ( a -- )     TRACER IF COUNT 8 RTYPE 2 SPACES } DROP ;
: .STRING ( a n -- ) TRACER IF .HERE: DUP DOTBYTE [CHAR] " EMIT
                               TYPE [CHAR] " EMIT 2 SPACES } 2DROP ;
: .HERE  ( -- )      TRACER IF   .STACK CR HERE TARGA .
                                 xSTATE @ IF 3 SPACES THEN
                            THEN WAIT/GO ; 

\ --- DUMP ---

0 VALUE DUMPKOL
0 VALUE DUMPADR
: VISIBLE?   ( ch -- vlag ) HX 21 HX 7E WITHIN ;
: VISIBLEMIT  ( c -- )      BL MAX HX 7E MIN EMIT ;
: .MORETEXT  ( a -- )       DUP 1- C@ VISIBLE? 0= IF DROP }
                            BEGIN COUNT DUP VISIBLE? WHILE EMIT REPEAT 2DROP ;
: DUMPLINE ( -- )
  CR DUMPADR DUP . TARGA .
  DUMPADR BASE @ 0 DO COUNT DUMPKOL .R LOOP DROP
  ."  |"
  DUMPADR BASE @ 0 DO COUNT VISIBLEMIT LOOP DUP TO DUMPADR .MORETEXT
  ." |" ;

: TARGDUMP ( hosta n -- ) \ Werkt bij elke waarde van BASE
  OVER TO DUMPADR +
  HX 0FF S>D <# #S #> 1+ TO DUMPKOL DROP
  BEGIN DUMPLINE WAIT/GO
        DUMPADR OVER BASE @ OVER + WITHIN UNTIL DROP ; 

<----
\  programma om geheugen weg te schrijven naar een binaire file (FM 27JUL04)
VARIABLE FID \ filehandle,  file id

: MAKEBINFILE ( hosta n -- ) \ make a binary file
  S" work/6809.bin" W/O BIN CREATE-FILE ABORT" Cannot create file!"
  DUP FID ! \ address count fid
  WRITE-FILE ABORT" Error writing file!"
  FID @ CLOSE-FILE DROP 
; 
---->

\ 16bits  f e t c h   &   s t o r e  &  c o m m a 

: x@ ( hosta -- n )   COUNT 8 LSHIFT SWAP C@ OR ;    \ Voor NFA>LFA x@ in xFIND
: x! ( n hosta -- )   OVER 8 RSHIFT OVER C! 1+ C! ;  \ Wordt herdefinieerd
: x, ( n -- )         DUP .CELL, HERE x! 2 ALLOT ;   \ n = 16-bits getal
: xC, ( ch -- )       DUP .BYTE, C, ;
: xSTRING, ( a n -- )
  2DUP .STRING HERE SWAP C, COUNT DUP ALLOT MOVE ;   \ Allot as counted string
: xCELLS ( n -- 2n ) 2* ;
: x! 2DUP .CELLSTORE x! ;
: xC! ( n hosta -- ) 2DUP .BYTESTORE C! ;
<---- qqq
 x-woorden zijn de woorden die voor de Target
 anders moeten functioneren dan voor de Host.
 We maken alleen x-woorden als dat noodzakelijk is,
 of om output te kunnen tracen. ( mmm)
---->

VOCABULARY META

<---- EINDE VAN META1 ---->
CR .(  Nu wordt de crossassembler geladen ) \ sss

<----
 S" maiswork\cras601.F" INCLUDED \ mmm  voor Windows minforth
 S" maiswork/cras601.f" INCLUDED \ mmm voor Linux minforth
 S" cras601.f" included \ mmm voor Linux gforth
---->

S" cras601.f" INCLUDED  \ voor Win32Forth

\ -----------------------------  meta II -------------------------

<---- META II - an - 19mei04 ---->

FORTH DEFINITIONS

\ W I N T E R P R E T

DECIMAL

<---- H e a d e r  b o u w e n ---->
0 VALUE xTOPNFA
: NFA>CFA ( nfa -- cfa )   COUNT HX 7F AND + ;
: NFA>LFA ( nfa -- lfa )   3 - ;
: CFA>NFA ( cfa -- nfa ) BEGIN 1- DUP C@ 20 < UNTIL ;
: x>BODY  ( xt -- body )   3 + ;
: @IMM    ( nfa -- 1/-1 )  1- C@ 1 AND 2* 1- ;

CREATE WORDA HX 22 ALLOT ALIGN \ Voor de opslag vh resultaat van BL WORD
: >WORDA ( a n -- )  DUP WORDA C! WORDA 1+ SWAP MOVE ;

: DRAAD# ( bl-word -- nr ) \ (Len 2* LastChar XOR 2* FirstChar XOR)
  DUP 1+ C@ SWAP        \ begin
  DUP C@ OVER + C@ SWAP \ eind
  C@                    \ count
  2* XOR 2* XOR
  HX 0F AND ;

: DRAAD ( bl-word -- adr ) \ nnn
  DRAAD# 2* ORIGINHOSTA 3 + + ;

: xFIND ( a -- xt 1/-1 -- a 0 ) \ nnn
  DUP DRAAD                  \ -- a draadadres
  x@                         \ -- a targtopnfa?
  DUP IF                     \ -- a xnfa
  BEGIN HOSTA                \ -- a nfa
        2DUP                 \ -- a nfa a nfa
        OVER C@ 1+           \ -- a nfa a nfa n+1
        TUCK COMPARE 0=      \ -- a nfa gevonden?
        IF  NIP DUP NFA>CFA  \ -- nfa xt
            SWAP @IMM }      \ -> xt 1/-1   (Gevonden, klaar)
        NFA>LFA x@           \ -- a link@   (Volgende)
        DUP 0=               \ -> a 0?       (Einde vd keten? klaar)
  UNTIL
  THEN ;

: REDEFINING  ( cstring - ) xFIND NIP IF CR ." --- Redefining: " THEN ;
: xCOMPILE,   ( hosta - )         TARGA  x, ;

0 VALUE CURRENTVOC



: xHEADER        \ h e a d e r  aanmaken zonder codeveld \ nnn
  TRACER IF CR CR THEN
  BL-WORD COUNT >WORDA              \ n a a m  inlezen
  WORDA xFIND >R
  R@ IF CR ." --- Redefining:" THEN \ bestaat-ie al?
  SPACE
  R@ IF DUP CFA>NFA xCOMPILE, THEN   \ h o m l i n k ,
  DROP
  WORDA COUNT TYPE 2 SPACES         \ n a a m  afdrukken
\  WORDA DRAAD# ." /" .
  WORDA DRAAD
     DUP x@ x,                      \ l i n k , (naar vorig woord)
     CURRENTVOC
     R> IF HX 80 OR THEN
     xC,                            \ hom-voc-imm byte ,
     HERE TARGA SWAP x!             \ nieuwe draadtop
     HERE TO xTOPNFA                \ algemene top
  WORDA COUNT xSTRING, ;            \ n a a m ,


\ ----- i n t e r p r e t -----

0 VALUE SECTION  \ For optimizer. Marks discontinuity in compiled code.
: !SECTION HERE TO SECTION ;

: GET-NAME ( <naam> -- ) \ Compile <naam> as a string
  BL WORD COUNT >WORDA WORDA COUNT POSTPONE SLITERAL ;
: FIND-IT ( a n -- cfa-hosta )  >WORDA  WORDA .NAAM  WORDA xFIND 0= ?NOTYET ;
: TOKEN ( <naam> -- cfa-hosta )  GET-NAME POSTPONE FIND-IT ; IMMEDIATE
:  KOMPILE ( <naam> -- cfa, )  POSTPONE TOKEN POSTPONE xCOMPILE, ; IMMEDIATE

: xLITERAL ( getal -- ? ) xSTATE @
   IF   DUP HX 80 HX -80 WITHIN IF KOMPILE () x, !SECTION }
        KOMPILE (C) xC, !SECTION
   THEN ;
<----  Late binding (pseudo voorwaartse referenties) qqq
() is the name (in Target) of the word that puts
  an immediately following number on the stack.
Lees KOMPILE ccc  als COMPILE" ccc"
waarbij de string ccc pas tijdens het metacompileren
in de Target wordt opgezocht.
Evenzo TOKEN ccc. Tijdens het metacompileren wordt ccc opgezocht.
---->

META DEFINITIONS
GET-CURRENT          CR .S .( GET-CURRENT )
FORTH    DEFINITIONS
CONSTANT META-WID    CR .S

: IN-META? ( worda -- xt imm? -- 0 ) COUNT META-WID SEARCH-WORDLIST ;

0 VALUE KLAAR?

\ --------------------------------------
\ --------------------------------------
: WINTERPRET ( BL-WORD -- ) \ qqq
  COUNT >WORDA              \ resultaat in WORDA
  WORDA .NAAM
  xSTATE @
  IF   WORDA xFIND
       0< IF xCOMPILE, }        \ Compileer
       DROP                     \ Niet gevonden
  THEN
  WORDA IN-META?  IF EXECUTE }  \ Executeer
  WORDA >NUM xLITERAL ;         \ Getal

: METACOMPILING ( -- ) \ qqq
  BEGIN .HERE
        BL-WORD WINTERPRET
        KLAAR?
  UNTIL ."  K l a a r   " ;
\ --------------------------------------
\ --------------------------------------

<---- metacompiler aan en uit zetten ---->

: :::MAIS::: ( -- ) FORTH \ nnn qqq
  0 TO KLAAR?
  S" ANEW -MAIS" EVALUATE          \ Destructieve marker
  HX 10 ALLOT                       \ Voor interruptvectoren
  HERE HX FFF OVER AND - HX 1000 + \ Start op eerstvolgende HEX xxxxx000
  TO ORIGINHOSTA                   \ Begin van de image
  ORIGINHOSTA HERE - ALLOT
    BASE @ >R HEX                  \ Info afdrukken
      CR ." ORIGINHOSTA " HERE .
      CR ." ORIGINTARGA " ORIGINTARGA .
    R> BASE !
    CR ." type . if you want to continue "
    [CHAR] . KEY <> ?INTERRUPTED      \ Doorgaan?
    CR
  0 xSTATE !                       \ Initiatie
  HERE HX 4000 0 FILL              \ Imagegebied schoonvegen
  METACOMPILING ;

\ METACOMPILING wordt verlaten als KLAAR? True is gemaakt (in ;;;MAIS;;;)

HEX
: CHECKSUM, ( -- ) \ voeg enkele bytes toe aan de image zodat checksum=0.
  HERE 8 0 FILL ALIGN 0 ,
  0 HERE ORIGINHOSTA
  ?DO I x@ xOR 2 +LOOP HERE 2 - x! .HERE
  0 , ;
DECIMAL

: ;;;MAIS;;; ALIGN CHECKSUM, TRUE TO KLAAR? ;

<---- qqq
 :::MAIS::: en ;;;;MAIS;;;; zijn respectievelijk
 eerste en laatste commando van de Target code.
---->

: xHX POSTPONE HX xLITERAL ; IMMEDIATE
: xDM POSTPONE DM xLITERAL ; IMMEDIATE
: xBN POSTPONE BN xLITERAL ; IMMEDIATE


CR  .(   EINDE VAN META II )

\ -----------------------------  meta III -------------------------
\ Meta III - an - 19mei04


DECIMAL

<---- d e f i n i ë r e n d e  w o o r d e n ---->


HX 0BD CONSTANT (JSR)
HX 07E CONSTANT (JMP)
HX 03B CONSTANT (RTI)

: xIMMEDIATE xTOPNFA 1- DUP C@ 1 OR SWAP xC! ;


: DOER, ( DOERtoken -- )
  (JSR) xC,                           \ 6809 JSR-extended opcode
  x>BODY      \ >DOERbody
  xCOMPILE,   \ Adres van DOERroutine
  !SECTION ;

: MET-DOER  ( <doernaam> -- ) \ Compileer Jsr-Doer in cfa achter HEADER
  POSTPONE TOKEN POSTPONE DOER, ; IMMEDIATE

: x[   0 xSTATE !  ;
: x]  -1 xSTATE !  ;

: xHIDE   xTOPNFA HX 80 OVER C@ OR  SWAP xC! ;
: xREVEAL xTOPNFA HX 7F OVER C@ AND SWAP xC! ;

: x: ( <naam> -- )
  xHEADER MET-DOER DO:
  xHIDE x]  HX 1111 ;


: x; ( -- )
  HX 1111 ?PAIR  KOMPILE EXIT  xREVEAL x[ ;

: xDOER: ( <naam> -- )
  xHEADER MET-DOER DODOER
  (JSR) xC, KOMPILE DODOES
  xHIDE x] HX 1111 ;

\ IGNORE NO-CODING END-CODE  \ *** voor xCODE en DOERCODE
\ : xCODE xHEADER  POSTPONE NO-CODING ;  \ Als er geen assembler is
\ : xDOERCODE ( <naam> -- ) xHEADER MET-DOER DODOER POSTPONE NO-CODING ;

  : xCODE xHEADER  HX -1111 ;            \ Normale versie
  : xDOERCODE ( <naam> -- ) xHEADER MET-DOER DODOER HX -1111 ;

: xEND-CODE HX -1111 ?PAIR ;

: xCREATE   ( <naam> -- )         xHEADER MET-DOER DOCREATE ;
: xVARIABLE ( <naam> -- )         xHEADER MET-DOER DOVAR 0 x,  ;
: xVALUE    ( n <naam> -- )       xHEADER MET-DOER DOVAL x, ;
: xCONSTANT ( n <naam> -- )
  DUP HX 80 HX -80 WITHIN
  IF xHEADER MET-DOER DOCON x, }
  xHEADER MET-DOER DOCCON xC, ;
: xFFBASE ( tempbase <name> -- )  xHEADER MET-DOER DOFFBASE xC, xIMMEDIATE ;



\ ----- Users

0 VALUE UOFFSET
: COLD-UHERE ( -- hosta ) UOFFSET ORIGINHOSTA + ;

: UALLOT ( n -- )  UOFFSET + TO UOFFSET
  TRACER IF ."  UOFFSET wordt " UOFFSET . THEN  ;
: ?USERBYTES ( -- ) USERBYTES UOFFSET < ?USERSPACE ;

: DICTIONARY (  -- )
  HERE HX 20 ALLOT HX 20 0 FILL 
  TRACER IF ." 10 cellen gereserveerd voor dictionary " THEN ;

: I-DATA ( -- )
  HERE ORIGINHOSTA - TO UOFFSET
  HERE USERBYTES UOFFSET -
  DUP ALLOT
  TRACER IF DUP . ." bytes gereserveerd voor koude data " THEN
  0 FILL  ;

: xIVAL ( x <naam> -- )
  ?USERBYTES
  xHEADER MET-DOER DOIVAL
  UOFFSET x,
  COLD-UHERE  x!     \ Store x in de koude User
  1 xCELLS UALLOT ;

: xIVAR ( x <naam> -- )
  ?USERBYTES
  xHEADER MET-DOER DOIVAR
  UOFFSET x,
  COLD-UHERE  x!     \ Store x in de koude User
  1 xCELLS UALLOT ;

: xIVEC ( <naam> -- )
  ?USERBYTES
  xHEADER MET-DOER DOIVAR
  UOFFSET x,
  (RTI) COLD-UHERE xC! 3 UALLOT ;   \ (rti), 0, 0, -- 3 bytes in koude User

: x'    ( <ccc> -- cfa-hosta )
  BL-WORD
  DUP .NAAM
  xFIND 0= ?NOTYET ;

: xRECURSE ( -- )
  xTOPNFA NFA>CFA xCOMPILE, ;


: xMAKEONLY ( <ccc> -- )
  xHEADER MET-DOER DOONLY
  0 xC,  \ voc#
  0 x,   \ voc-link
  HERE TARGA 3 -
  TOKEN TOPVOC
  x>BODY x@ ORIGINHOSTA + x! ;

: xVOCABULARY ( -- )
  xHEADER MET-DOER DOVOC
  TOKEN TOPVOC x>BODY x@
  ORIGINHOSTA + >R                   \ Voc-Link
  R@ x@ HOSTA C@ 2 + xC,             \ Voc#
  R@ x@ x,                           \ Voc-Link,
  HERE TARGA 3 - R> x! ;             \ Nieuwe Voc-Link


: xMSG" ( n <ccc"> -- )
  x,                                  \ Msg#,
  TOKEN TOPMSG x>BODY x@
  ORIGINHOSTA + >R                    \ Msg-Link
  R@ x@ x,                            \ Msg-Link,
  HERE 4 - TARGA R> x!                \ Nieuwe Msg-Link
  HX 22 PARSE xSTRING, ;

: PFXLIST                  \ PREFIXLIST
  TOKEN TOPPFX x>BODY x@
  ORIGINHOSTA + >R
  R@ x@ x,
  HERE TARGA R> x! ;
  
: ONLY:      0 TO CURRENTVOC ;
: FORTH:     2 TO CURRENTVOC ;
: INSIDE:    4 TO CURRENTVOC ;
: EXTRA:     6 TO CURRENTVOC ;
: ASSEMBLER: 8 TO CURRENTVOC ;

<----
 De even getallen zijn wid's, zij corresponderen met
 de volgorde van deze definities in de TARG-file:
FORTH:
  MAKEONLY ONLY        \ 0
ONLY:
  VOCABULARY FORTH     \ 2
  VOCABULARY INSIDE    \ 4
  VOCABULARY EXTRA     \ 6
  VOCABULARY ASSEMBLER \ 8
---->


\ ---- a n d e r e  r o d e  w o o r d e n ----

: xPOSTPONE ( <ccc> -- )
  BL-WORD DUP .NAAM
  xFIND DUP 0= ?NOTYET
  0< IF KOMPILE COMPILE() HERE 2 + TO SECTION THEN xCOMPILE, ;

: x" ( <ccc"> -- ) KOMPILE "(S) HX 22 PARSE xSTRING, ;
: x." ( <ccc"> -- ) KOMPILE ."(S) HX 22 PARSE xSTRING, ;

: xCHAR ( -- ch )
  BL-WORD DUP .NAAM
  COUNT 0= ?INPUT
  C@ ;

: x[CHAR] ( -- ch ) ( -- )
  xCHAR xLITERAL ;

: x[']  ( <naam> -- ) x' TARGA xLITERAL  ;


: PREFIXOBJECT, ( <ccc> -- ) \ test op DOIVAL
  x'
  DUP 1+ x@
  TOKEN DOIVAL
                3 + TARGA
  <> ?PREFIX
  x>BODY x@ x, ;         \ user-offset,

: xTO   KOMPILE TO()   PREFIXOBJECT, ; ( <ccc> -- )
: x+TO  KOMPILE +TO()  PREFIXOBJECT, ; ( <ccc> -- )
: xINCR KOMPILE INCR() PREFIXOBJECT, ; ( <ccc> -- )


<----  b e s t u r i n g s w o o r d e n ---->

: xCOMPILE! ( hosta1 hosta2 - ) >R TARGA R> x! ;

: OPTIM-IF \ optimize: 0= IF() becomes IFZERO()
  TOKEN 0= TARGA
  HERE 2 - x@ =
  IF   SECTION HERE 1- U<
       IF   -2 ALLOT KOMPILE IFZERO() }
  THEN     KOMPILE IF() ;

: x?EXIT
  TOKEN 0= TARGA
  HERE 2 - x@ =
  IF   SECTION HERE 1- U<
       IF   -2 ALLOT KOMPILE EXIT-ON-FALSE }
  THEN     KOMPILE EXIT-ON-TRUE ;

: OPTIM?RE
  TOKEN 0= TARGA
  HERE 2 - x@ =
  IF   SECTION HERE 1- U<
       IF   -2 ALLOT KOMPILE IF() }
  THEN     KOMPILE IFZERO() ;

: xIF    ( -- IFa 11 )    OPTIM-IF HERE 0 x, HX 11 ;
: xAHEAD ( -- AHEADa 11 ) KOMPILE  GOTO() HERE 0 x, HX 11 ;
: xBEGIN ( -- BEGINa 22 ) HERE HX 22 !SECTION ;

: xTHEN  ( IFa 11 -- )    HX 11 ?PAIR HERE SWAP xCOMPILE! !SECTION ;
: x/THEN  ( IFa 11 x y -- )  2SWAP xTHEN ;
: xUNTIL ( BEGINA 22 -- ) HX 22 ?PAIR OPTIM-IF xCOMPILE, ;
: xAGAIN ( BEGINa 22 -- ) HX 22 ?PAIR KOMPILE  GOTO() xCOMPILE, ;

: xELSE   ( IFa 11 -- AHEADa 11 )     xAHEAD x/THEN ;
: xWHILE  ( x n -- IFa 11 x n )       xIF 2SWAP ;
: xREPEAT ( WHILEa 11 BEGINa 22 -- )  xAGAIN xTHEN ;
: x}      ( IFa 11 -- )               KOMPILE EXIT xTHEN ;

: xRE     ( -- ) KOMPILE GOTO() xTOPNFA NFA>CFA x>BODY xCOMPILE, ;
: x?RE     ( -- ) OPTIM?RE       xTOPNFA NFA>CFA x>BODY xCOMPILE, ;
: xRE}     ( IFa 11 -- ) xRE xTHEN ;

\ for assembler
: xIF,     xSTATE @ IF xIF }     IF, ;
: xAHEAD,  xSTATE @ IF xAHEAD }  AHEAD, ;
: xBEGIN,  xSTATE @ IF xBEGIN }  BEGIN, ;
: xTHEN,   xSTATE @ IF xTHEN }   THEN, ;
: x/THEN,  xSTATE @ IF x/THEN }  /THEN, ;
: xUNTIL,  xSTATE @ IF xUNTIL }  UNTIL, ;
: xAGAIN,  xSTATE @ IF xAGAIN }  AGAIN, ;
: xELSE,   xSTATE @ IF xELSE }   ELSE, ;
: xWHILE,  xSTATE @ IF xWHILE }  WHILE, ;
: xREPEAT, xSTATE @ IF xREPEAT } REPEAT, ;

\ Formal end of colon definition, without compiling EXIT
: (;) ( 1111 -- )  HX 1111 ?PAIR  xREVEAL x[ ;

\ : FORWARDER ( -- NESTA 44 )  KOMPILE >R() HERE 0 x, HX 44 ;
\ : LIMIT ( NESTA 44 -- ) HX 44 ?PAIR KOMPILE (EXIT
\                         HERE SWAP xCOMPILE! !SECTION ;
\ META: FORWARDER FORWARDER ( -- NESTA 44 )
\ META: LIMIT LIMIT ( NESTA 44 -- )

\ DO..LOOP

: xDO    ( -- adr 33 )  KOMPILE DO()  HERE 0 x, HX 33 ;
: x?DO   ( -- adr 33 )  KOMPILE ?DO()  HERE 0 x, HX 33 ;

: LOOPCODA  ( DOadr 33 -- )
  HX 33 ?PAIR
  DUP 2 + xCOMPILE,
  HERE SWAP xCOMPILE! ;

: xLOOP  ( DOadr 33 -- )  KOMPILE LOOP()  LOOPCODA ;
: x+LOOP ( DOadr 33 -- )  KOMPILE +LOOP() LOOPCODA ;


<---- Extra ---->


\ labels

: LABEL: ( 'naam' -- )  CREATE 0 , HX -1234 ,  DOES> @ ;

: HERE-IS ( <naam in FORTH> -- ) \ vul een label
  HERE
  BL-WORD DUP .NAAM
  FIND 0= ?UNKNOWN
  >BODY
  HX -1234 OVER CELL+ @ ?PAIR
  ! ;


 LABEL: AMSTERDAM
 LABEL: ROTTERDAM
 LABEL: THINGUMAJIG

META
HX B000 CONSTANT ACIA-CONTROL   \ : ACIA-CONTROL X ) ;
HX B001 CONSTANT ACIA-DATA      \ : ACIA-DATA    X 1 #) ;
FORTH

\ Voor de assembler in de target Forth ================

\ ==================== multi-creating (AN) ================
\ Groepsgewijs woorden definiëren.
\ -1 fungeert als afsluiter.
\ Bedenk: HX leest een getal (woord) uit de invoerstroom.

: CREATING1  ( doertoken -- )  \ 8 bit in body
  >R
  BEGIN  POSTPONE HX  -1 OVER <>
  WHILE  xHEADER R@ DOER, xC,
  REPEAT R> 2DROP ;

: CREATING2  ( doertoken -- )  \ 16 bit in body
  >R
  BEGIN  POSTPONE HX  -1 OVER <>
  WHILE  xHEADER R@ DOER, x,
  REPEAT R> 2DROP ;

: CREATING11 ( doertoken -- ) \ Tweemaal 8 bit in body
  >R ." ~ "
  BEGIN  POSTPONE HX  -1 OVER <>
  WHILE  POSTPONE HX xHEADER R@ DOER, xC, xC,
  REPEAT R> 2DROP ;

: CREATING21 ( doertoken -- ) \ 8 bit & 16 bit in body
  >R
  BEGIN  POSTPONE HX  -1 OVER <>
  WHILE  POSTPONE HX xHEADER R@ DOER, x, xC,
  REPEAT R> 2DROP ;

META DEFINITIONS FORTH
: SEX:  TOKEN DOSEX   CREATING1 ;  \ Inherent Addressing, 8
: SWI2: TOKEN DOSWI2  CREATING2 ;  \ Inherent Addressing, 16
: CWAI: TOKEN DOCWAI  CREATING1 ;  \ Immediate, 8
: NEG:  TOKEN DONEG   CREATING11 ; \ General instructions, 8&8 
: LDY:  TOKEN DOLDY   CREATING21 ; \ General instructions, 16&8 
: EXG:  TOKEN DOEXG   CREATING1 ;  \ TFR and EXG, 8
: LEA:  TOKEN DOLEA   CREATING1 ;  \ LEA-instructions, 8
: BEQ:  TOKEN DOBEQ   CREATING1 ;  \ Conditional branches, 8
: BRA:  TOKEN DOBRA   CREATING2 ;  \ Unconditional Branches, 16
: CON:  TOKEN DOCCON  CREATING1 ;  \ Constants, Registers, Conditions 8
: -):   TOKEN DO-)    CREATING1 ;  \ Simple Indexed Modes, 8

FORTH DEFINITIONS


\ ============= herdefinities in META ==================

: DOMETA: DOES> @ EXECUTE ;

<----
: META: ( META-name FORTH-name )
  META-WID SET-CURRENT
  CREATE DOMETA: ' ,
  FORTH DEFINITIONS ;
---->

: META-WORDS: \ List, on every line: new (META) name & FORTH name
  META-WID SET-CURRENT
  BEGIN  \ REFILL 0= ?INPUT \ vorige versie
         POSTPONE \
         >IN @ SOURCE NIP U< 0= IF REFILL 0= ?INPUT THEN \ hhh
         CREATE DOMETA: ' DUP ,
         ['] ;;;MAIS;;; =
  UNTIL  DEFINITIONS ;

\ Wil je iets veranderen? LET OP:
\ Begin op iedere regel met een META-naam en een FORTH-woord,
\ de rest van de regel wordt niet gelezen. Geen lege regels!.
\ De laatste META-naam moet ;;;MAIS;;; zijn.

\ You want to change something? ATTENTION:
\ Start every line with a META name and a FORTH word,
\ the rest of the line will not be read. No empty lines!
\ The last META name in the list must be ;;;MAIS;;;

\ meta-name  forth-name   (Redefine all these Forth words in META)
META-WORDS:
  TRACE      TRACE       \ ------------- Special metacompiler directives
  NOTRACE    NOTRACE
  ALLOT      ALLOT
  UALLOT     UALLOT
  UOFFSET    UOFFSET
  I-DATA     I-DATA
  DICTIONARY DICTIONARY 
  THINGUMAJIG  THINGUMAJIG  ( -- hosta )
  AMSTERDAM    AMSTERDAM    ( -- hosta )
  ROTTERDAM    ROTTERDAM    ( -- hosta )
  HERE-IS      HERE-IS
  ORIGINHOSTA  ORIGINHOSTA
  ORIGINTARGA  ORIGINTARGA
  ONLY:      ONLY:       \ ------------- Set current target wordlist
  FORTH:     FORTH:
  INSIDE:    INSIDE:
  EXTRA:     EXTRA:
  ASSEMBLER: ASSEMBLER:
  CODE       xCODE       \ ------------- Defining words
  :          x:
  DOER:      xDOER:       ( <name> -- )
  DOERCODE   xDOERCODE    ( <name> -- )
  CREATE     xCREATE      ( <name> -- ) \ see TO-LIST
  VARIABLE   xVARIABLE    \ not used
  VALUE      xVALUE       ( x <name> -- )
  CONSTANT   xCONSTANT    ( x <name> -- )
  IVAR       xIVAR        ( x <name> -- )
  IVAL       xIVAL        ( x <name> -- )
  IVEC       xIVEC        ( x <name> -- )
  VOCABULARY xVOCABULARY  ( <name> -- )
  MAKEONLY   xMAKEONLY    ( <name> -- )
  PFXLIST    PFXLIST
  FFBASE     xFFBASE      ( base <name> -- )
  END-CODE   xEND-CODE
  ;          x;
  (;)        (;)        \ Formal end of hilevel definition without EXIT - after AGAIN
  RECURSE    xRECURSE   \ ------------- Compiler words
  POSTPONE   xPOSTPONE
  S"         x"
  ."         x."
  CHAR       xCHAR
  [CHAR]     x[CHAR]
  [']        x[']
  LITERAL    xLITERAL   \ Compile () or (c)
  HX         xHX
  DM         xDM
  BN         xBN
  +TO        x+TO
  TO         xTO
  INCR       xINCR
  IMMEDIATE  xIMMEDIATE  
  MSG"       xMSG"        ( msg# txtadr txtlen -- )
  IF         xIF,         \ ------------- Controll words. IF absorbs 0=
  AHEAD      xAHEAD,
  BEGIN      xBEGIN,
  THEN       xTHEN,
  /THEN      x/THEN,
  UNTIL      xUNTIL,      \ UNTIL absorbs 0=
  AGAIN      xAGAIN,
  ELSE       xELSE,
  WHILE      xWHILE,      \ WHILE absorbs 0=
  REPEAT     xREPEAT,
  }          x}
  DO         xDO
  ?DO        x?DO
  LOOP       xLOOP
  +LOOP      x+LOOP
  RE         xRE
  ?RE        x?RE
  RE}        xRE}
  ?EXIT      x?EXIT
  <----      <----       \ ------------- Comment words
  \          \
  (          (
  [          x[          \ ------------- Other interactive tools
  ]          x]
  HEX        HEX
  DECIMAL    DECIMAL
  .S         .S
  +          +
  -          -
  ,          x,           ( x )
  !          x!           ( x hosta )
  COMPILE!   xCOMPILE!    ( hosta hosta )
  C,         xC,          ( ch )
  C!         xC!
  @          x@
  '          x'           ( -- hosta )
  >BODY      x>BODY       ( hosta -- hosta )
  HERE       HERE         ( -- hosta )
  TARGA      TARGA
  HOSTA      HOSTA
  (RTI)      (RTI)        ( -- hosta )
  CELLS      xCELLS
  DUP        DUP
  DROP       DROP
  OVER       OVER
  OR         OR 
  RSHIFT     RSHIFT
  ACIA-CONTROL ACIA-CONTROL   ( -- targa )
  ACIA-DATA    ACIA-DATA ( -- targa )
  ;;;MAIS;;;   ;;;MAIS;;;

\  (JMP)      (JMP)        ( -- hosta )
\  (JSR)      (JSR)        ( -- hosta )

\ ;;;MAIS;;; moet onderaan staan.
\ ;;;MAIS;;; has to be the last item in the list.



: NOMORE? ( -- t/f )
  KEY? DUP
  IF   DROP KEY
       DUP BL = IF DROP KEY THEN
       BL <>
  THEN ;

CREATE VERDELING HX 10 ALLOT ALIGN
: .VERDELING CR
  VERDELING HX 10 0 DO COUNT 3 .R LOOP DROP ;

: /WORDS \ Per draad
  ORIGINHOSTA 3 +
  HX 10 0
  DO   CR I .                 \ .Draadnr
       DUP x@                 \ nfa-targa
       0 >R                   \ woordteller
       BEGIN   R@ HX 0C MOD 0= IF CR THEN SPACE
               HOSTA
               DUP COUNT HX 1F AND TYPE SPACE 
               R> 1+ >R       \ woordteller 
               NFA>LFA x@     \ nfa-targa?
               DUP 0=
       UNTIL   DROP
               ." (" R> DUP I VERDELING + C!
               0 .R ." )"
       2 +                    \ volgende draadadres
       WAIT/GO
  LOOP DROP .VERDELING ;
: xWORDS NOTRACE
  ORIGINHOSTA 3 + PAD HX 20 MOVE  \ Dictionary -> 60..80
  0 >R
  BEGIN  -1 0  \ Draadadres en NFA-Origin
         PAD HX 20 + PAD
         DO     I x@
                IF   DUP I x@ ORIGINTARGA -
                     < IF 2DROP I DUP x@ ORIGINTARGA - THEN
                THEN
         2 +LOOP
         WAIT/GO OVER 0< IF 2DROP ."  -- " R> . }
         R@ HX 0C MOD IF SPACE ELSE CR THEN
         DROP DUP x@ HOSTA
         DUP COUNT HX 7F AND SPACE TYPE R> 1+ >R 
         NFA>LFA x@ SWAP x!
  AGAIN ;

\ an - 2005
\ RAM data versleutelen (in hostforth) en ontcijferen (in maisforth)
\ ---------------------------------
\ Nodig in HostForth

HEX

: 3>4    ( adr -- adr+3 )
  DUP C@                        2 RSHIFT    21 + EMIT
  COUNT  3 AND 4 LSHIFT OVER C@ 4 RSHIFT OR 21 + EMIT
  COUNT  F AND 2 LSHIFT OVER C@ 6 RSHIFT OR 21 + EMIT
  COUNT 3F AND                              21 + EMIT ;


: QQTEXT ( a n -- ) \ a,n is het te verzenden RAM gebied.
  HEX CR ." HEX "     OVER >R
  0 ?DO I F AND 0=
        IF  I IF SPACE I . THEN CR ." Q "
             WAIT/GO
        THEN 3>4
         3 +LOOP  R> - SPACE . ;

: MAKEQQ ORIGINHOSTA HERE 1 CELLS - OVER - PAGE QQTEXT ;

HEX
: ROMIMAGE ( -- )
 C000 TO ORIGINTARGA
 S" targ601.f" INCLUDED          \ laad target code
 HERE
    ORIGINHOSTA 4000 + OVER - 
    DUP ALLOT
 0 FILL
 ORIGINHOSTA 10 - HERE 10 - 10 MOVE
 S" an601.bin" BIN R/W OPEN-FILE THROW ( id )
 DUP ORIGINHOSTA 4000 ROT WRITE-FILE THROW
 CLOSE-FILE THROW
;

DECIMAL
CR .(   metacompiler loaded   ) 

