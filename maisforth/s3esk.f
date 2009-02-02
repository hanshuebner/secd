hex
B020 constant vdu
vdu constant vdu-char
vdu 1 + constant vdu-color
vdu 2 + constant vdu-hcursor
vdu 3 + constant vdu-vcursor
vdu 4 + constant vdu-voffset
decimal

: str-vdu
    0 do
        i vdu-hcursor c!
        dup c@ vdu-char c!
        1 +
    loop drop ;

hex
B030 constant leds
55 leds c!

hex
B040 constant spi-lsb
B041 constant spi-msb
B042 constant spi-status
B043 constant spi-config

FF spi-config c!

hex
: spi-send
    100 /mod
    spi-msb c!
    spi-lsb c!
    3 spi-status c! ;

: spi-test
    begin
        FFFF 0 do
            i spi-send
        loop
        key?
    until
    key drop ;

: matrix-init
    C00 spi-send \ shutdown
    A0F spi-send \ intensity
    900 spi-send \ no decode
    B07 spi-send \ scan all digits
    100 spi-send \ clear digit 1
    200 spi-send \ clear digit 2
    300 spi-send \ clear digit 3
    400 spi-send \ clear digit 4
    500 spi-send \ clear digit 5
    600 spi-send \ clear digit 6
    700 spi-send \ clear digit 7
    800 spi-send \ clear digit 8
    C01 spi-send \ exit shutdown
;

: light-show
    8 0 do
        5 0 do
            i 1 + 100 * dup
            1 j lshift +
            spi-send
            600 ms
            spi-send
        loop
    loop ;

: big-lights
    begin
        light-show
    key? until
    key drop ;