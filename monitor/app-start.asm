;;; initialization code
        .area   sysrom
start:
        lds     #16000
        ldu     #15000
        jmp     _main
_outc:
        exg     a,b
        jmp     0xfcab