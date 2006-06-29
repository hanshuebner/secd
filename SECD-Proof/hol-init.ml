set_search_path
(`` .
 `./TACTICS/` .
 `./buses/` .
 `./wordn/` .
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
and in1_conv      =             ONCE_DEPTH_CONV 
and in_conv_tac   = CONV_TAC  o      DEPTH_CONV o CHANGED_CONV
and re_conv_tac   = CONV_TAC  o    REDEPTH_CONV o CHANGED_CONV
and in1_conv_tac  = CONV_TAC  o ONCE_DEPTH_CONV 
and in_conv_rule  = CONV_RULE o      DEPTH_CONV o CHANGED_CONV
and re_conv_rule  = CONV_RULE o    REDEPTH_CONV o CHANGED_CONV
and in1_conv_rule = CONV_RULE o ONCE_DEPTH_CONV 
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

let port1 th = port[th]
and prt1 th = prt[th]
and porr1 th = porr[th]
and prr1 th = prr[th]
and poarr = PURE_ONCE_ASM_REWRITE_RULE
and parr  = PURE_ASM_REWRITE_RULE
and oarr  = ONCE_ASM_REWRITE_RULE
and arr   = ASM_REWRITE_RULE
;;

let poke rule = POP_ASSUM \th. ASSUME_TAC (rule th);;
letrec trash n = (n = 0) => ALL_TAC | (POP_ASSUM (K ALL_TAC) THEN (trash (n-1)));;

% ================================================================= %
letrec IMP_RES_n_THEN n (ttac:thm_tactic) thm =
  (n = 0) => ttac thm
           | (TRY o (IMP_RES_THEN (IMP_RES_n_THEN (n - 1) ttac))) thm;;
% ================================================================= %

