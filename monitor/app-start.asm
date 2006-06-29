;;; initialization code
        .area   sysrom
start:
        lds     #16000
        ldu     #15000
        jmp     _main
