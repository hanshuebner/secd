;;; initialization code
        .area   sysrom
start:
        lds     #stack
        jmp     _main
;;; interrupt vector table
        .area   svec
        ;; 
        .word   start
        .word   start
        .word   start
        .word   start
        .word   start
        .word   start
        .word   start
        .word   start
        