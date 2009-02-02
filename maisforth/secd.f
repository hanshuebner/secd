\ Hans' stuff

\ SECD interface
EXTRA:
B140 CONSTANT SECD-STATUS
B141 CONSTANT SECD-ADDRESS-HIGH
B200 CONSTANT SECD-RAM-BASE

EXTRA:
: .SECD-STATUS ( -- )
    ." SECD: "
    SECD-STATUS C@
    DUP 1 AND 0= IF ." RUNNING " ELSE ." STOPPED " THEN
    1 RSHIFT 3 AND
    DUP 0 = IF ." RUNNING" THEN
    DUP 1 = IF ." HALTED" THEN
    DUP 2 = IF ." GC" THEN
    3 = IF ." UNKNOWN" THEN
    CR
;

: .SECD-PAGE ( N -- )
    SECD-ADDRESS-HIGH C!
    BASE @
    HEX
    SECD-RAM-BASE 100 DUMP
    BASE !
;

: SECD-RAM-TEST ( -- )
    0 SECD-ADDRESS-HIGH C!
    HX FF 0 DO
        I SECD-RAM-BASE I + C!
    LOOP
    0 .SECD-PAGE
;

B0E0 CONSTANT LED

: ON ( N -- )
    1 SWAP LSHIFT INVERT LED C@ AND LED C! ;
: OFF ( N -- )
    1 SWAP LSHIFT LED C@ OR LED C! ;

: NAP 300 MS ;

: LED-DEMO
    BEGIN
        5 0 DO  I ON  NAP  LOOP
        5 0 DO  I OFF NAP  LOOP
    KEY? UNTIL
    KEY DROP
;
