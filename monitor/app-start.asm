;;; initialization code
        .area   sysrom
start:
        lds     #0x3FFE
        ldu     #0x2FFE
        jmp     _main
_outc:
        exg     a,b
        jmp     0xfcab
_inch:
        exg     a,b
        jsr     0xfc80
        exg     a,b