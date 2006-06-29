set_search_path
(`` .
 `.././TACTICS/` .
 `.././wordn/` .
 (library_pathname() ^ `/integer/`) .
 (library_pathname() ^ `/group/`) .
 (tl (search_path())));;

map loadf [ `load_all`
          ; `SYM`];;
%-----------------------------------------------------------------------
|  Some useful abbreviations of rules, tactics and conversions.
------------------------------------------------------------------------%
let in_conv       =                  DEPTH_CONV o CHANGED_CONV
and re_conv       =                REDEPTH_CONV o CHANGED_CONV
and in1_conv      =             ONCE_DEPTH_CONV o CHANGED_CONV
and in_conv_tac   = CONV_TAC  o      DEPTH_CONV o CHANGED_CONV
and re_conv_tac   = CONV_TAC  o    REDEPTH_CONV o CHANGED_CONV
and in1_conv_tac  = CONV_TAC  o ONCE_DEPTH_CONV o CHANGED_CONV
and in_conv_rule  = CONV_RULE o      DEPTH_CONV o CHANGED_CONV
and re_conv_rule  = CONV_RULE o    REDEPTH_CONV o CHANGED_CONV
and in1_conv_rule = CONV_RULE o ONCE_DEPTH_CONV o CHANGED_CONV
;;

let port  = PURE_ONCE_REWRITE_TAC
and prt   = PURE_REWRITE_TAC
and ort   = ONCE_REWRITE_TAC
and rt    = REWRITE_TAC
and poart = PURE_ONCE_ASM_REWRITE_TAC
and part  = PURE_ASM_REWRITE_TAC
and oart  = ONCE_ASM_REWRITE_TAC
and art   = ASM_REWRITE_TAC
;;

let rr    = REWRITE_RULE
and prr   = PURE_REWRITE_RULE
and orr   = ONCE_REWRITE_RULE
and porr  = PURE_ONCE_REWRITE_RULE
;;

let port1 x = PURE_ONCE_REWRITE_TAC [x];;

let poke rule = POP_ASSUM \th. ASSUME_TAC (rule th);;
