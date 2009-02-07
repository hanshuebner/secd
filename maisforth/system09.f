\ System09 words

HEX

\ VDU stuff

B020 constant vdu-char
B021 constant vdu-color
B022 constant vdu-hcursor
B023 constant vdu-vcursor
B024 constant vdu-voffset

variable x-pos 0 x-pos c!
variable y-pos 0 y-pos c!
variable color 0 color c!

: at-xy-vdu ( x y -- )
    y-pos !
    x-pos !
;

decimal

: emit-vdu ( c -- )
    x-pos @ vdu-hcursor c!
    y-pos @ vdu-vcursor c!
    color @ vdu-color c!
    vdu-char c!
    x-pos @ 80 = if
        0 x-pos !
        1 y-pos +!
    else
        1 x-pos +!
    then
;

: type-vdu ( s n -- )
    0 do
        dup i + c@ emit-vdu
    loop
    drop
;

: cls ( -- )
    0 x-pos !
    0 y-pos !
    0 color !
    80 26 * 0 do
        32 emit-vdu
    loop
    0 x-pos !
    0 y-pos !
    7 color !
;

: liebesschwur ( -- )
    cls
    0 3 at-xy-vdu
    s" Hallo Suesse, guten Morgen!" type-vdu
    30 8 at-xy-vdu
    s" Ich " type-vdu
    1 color !
    s" liebe " type-vdu
    7 color !
    s" Dich!" type-vdu
    60 13 at-xy-vdu
    s" Dein Hans" type-vdu
    0 color !
    0 20 at-xy-vdu
    s" ." type-vdu
;

liebesschwur

\ SECD interface

hex
B140 constant secd-status
B141 constant secd-address-high
B200 constant secd-ram-base
decimal

: .secd-status ( -- )
    ." SECD: "
    secd-status c@
    dup 1 and 0= if ." running " else ." stopped " then
    1 rshift 3 and
    dup 0 = if ." running" then
    dup 1 = if ." halted" then
    dup 2 = if ." gc" then
    3 = if ." unknown" then
    cr
;

: .secd-page ( n -- )
    secd-address-high c!
    base @
    hex
    secd-ram-base 100 dump
    base !
;

