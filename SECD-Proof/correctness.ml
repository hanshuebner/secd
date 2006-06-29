% SECD verification                                                 %
%                                                                   %
% FILE:         correctness.ml                                      %
%                                                                   %
% DESCRIPTION:  The top level correctness proof.                    %
%                                                                   %
% USES FILES:   correctness_*.th, wordn & integer libraries         %
%               liveness                                            %
%                                                                   %
% Brian Graham 20.01.91                                             %
%                                                                   %
% Modifications:                                                    %
% 16.01.92 - BtG - DEC28 assumptions discharged.                    %
% ================================================================= %
new_theory `correctness`;;

map new_parent
 [ `correctness_AP`
 ; `correctness_RAP`
 ; `correctness_DUM`
 ; `correctness_RTN`
 ; `correctness_LD`
 ; `correctness_LDC`
 ; `correctness_LDF`
 ; `correctness_SEL`
 ; `correctness_JOIN`
 ; `correctness_CAR`
 ; `correctness_CDR`
 ; `correctness_CONS`
 ; `correctness_ATOM`
 ; `correctness_ADD`
 ; `correctness_SUB`
 ; `correctness_EQ`
 ; `correctness_LEQ`
 ; `correctness_STOP`
 ; `correctness_init`
 ; `liveness`
 ];;

loadf `wordn`;;
map load_library
[ `integer`
];;

letrec truncate i l =
 if i=0 then [] else hd l.truncate(i-1)(tl l);;

letrec seg (m,n) l =
 (if m<0 or n<m then fail
  if m=0 then truncate ((n-m)+1) l
         else seg (m-1,n-1) (tl l)
 ) ? failwith `seg`;;

load_theorem `liveness` `liveness`;;
load_theorem `mu-prog_proof0` `thm_initial_state`;;
map (load_definition `when`)
    [ `when`
    ];;
map (load_theorem `when`)
    [ `TimeOf_TRUE`
    ];;
map (load_definition `constraints`)
    [ `is_major_state`
    ; `valid_program_constraint`
    ];;
map (load_theorem `constraints`)
    [ `state_abs_thm`
    ; `valid_program_lemma`
    ];;
map (load_definition `top_SECD`)
    [ `SYS_spec`
    ; `NEXT`
    ];;
map (load_theorem `top_SECD`)
    [ `states_distinct`
    ];;
map (load_theorem `mem_abs`)
 [ `opcode_mem_abs_lemma`
 ];;
load_theorem `modulo_ops` `MINUS_ID`;;

map (load_definition `val_defs`)
[ `val`
];;
map (load_theorem `val_theorems`)
[ `iVal_F_b`
; `val_0_F_bus`
; `bv_thm`
; `DEC28_thm1`
; `DEC28_thm2`
];;

loadt `COND_CASES_THEN`;;

% ================================================================= %
let mtime = ":num"
and ctime = ":num";;
let w9_mvec = ":^mtime->word9";;

let mem14_32 = ":word14->word32";;
let m14_32_mvec = ":^mtime->^mem14_32";;

let state = ":bool # bool";;

% ================================================================= %
% This defines a relation on the inputs and outputs.                %
% ================================================================= %
let SYS_imp = (hd o tl o hyp)(theorem `phase_lemmas1` `phase_lemma_0`);;

let clock_Constraint = "clock_constraint SYS_Clocked";;
let free_list_Constraint = "well_formed_free_list memory mpc free s e c d";;
let valid_codes_Constraint =
   "valid_codes_constraint memory mpc c";;
let valid_program_Constraint =
   "valid_program_constraint memory mpc button_pin s e c d";;
let reserved_words_Constraint = "reserved_words_constraint mpc memory";;
% ================================================================= %
let DEC28_assum1 =
"!w28. (POS (iVal (Bits28 w28)))==>
        (PRE(pos_num_of(iVal(Bits28 w28))) =
           pos_num_of(iVal(Bits28((atom_bits o DEC28) w28))))"
and DEC28_assum2 =
"!w28.(POS (iVal (Bits28 w28)))==>
     ~(NEG (iVal (Bits28 ((atom_bits o DEC28) w28))))";;

timer true;;
% ================================================================= %
% The form of the correctness theorem for the LD instruction is     %
% not quite consistent with the way the goal will appear.           %
% There are introduced variables essentially used to abbreviate     %
% large terms, which must be eliminated.                            %
% ================================================================= %
load_theorem `correctness_LD` `correctness_LD`;;

let correctness_LD =
 UNDISCH_ALL
 (rr[]
 (SPEC "memory
  (TimeOf(is_major_state mpc)t)
  (car_bits
   (memory
    (TimeOf(is_major_state mpc)t)
    (cdr_bits
     (memory
      (TimeOf(is_major_state mpc)t)
      (c(TimeOf(is_major_state mpc)t))))))"
  (GEN "arg_cons_cell:word32"
  (SPECL [ "(memory:^m14_32_mvec)(TimeOf(is_major_state mpc)t)(cdr_bits arg_cons_cell)"
         ; "(memory:^m14_32_mvec)(TimeOf(is_major_state mpc)t)(car_bits arg_cons_cell)"]
  (GENL [ "n_cell:word32"
        ; "m_cell:word32" ]
  (SPECL [ "iVal(Bits28(atom_bits n_cell))"
         ; "iVal(Bits28(atom_bits m_cell))"]
  (GENL [ "n:integer"
        ; "m:integer"
        ](itlist DISCH (filter (\t. (free_in "n:integer" t)
		                 or (free_in "m:integer" t)
                                 or (free_in "n_cell:word32" t)
                                 or (free_in "m_cell:word32" t)
                                 or (free_in "arg_cons_cell:word32" t))
		       (hyp correctness_LD))
          correctness_LD))))))))
;;

% ================================================================= %
% typical proof ...                                                 %
% ================================================================= %
let iVal_tactic =
 in1_conv_tac wordn_CONV
 THEN port[theorem `dp_types` `Bits28_Word28`]
 THEN port[iVal_F_b]
 THEN port[INT_ONE_ONE]
 THEN prt[val_0_F_bus]
 THEN rt[val; bv_thm; ADD_CLAUSES]
 THEN re_conv_tac num_CONV
 THEN rt[ADD_CLAUSES]
 THEN REFL_TAC
 ;;

let [iVal_1; iVal_2; iVal_3; iVal_4; iVal_5; iVal_6; iVal_7; iVal_8; iVal_9
    ; iVal_10; iVal_11; iVal_12; iVal_13; iVal_14; iVal_15; iVal_16; iVal_17
    ; iVal_18; iVal_19; iVal_20; iVal_21] = 
map (\gl. prove (gl,iVal_tactic))
 [ "iVal(Bits28 #0000000000000000000000000001) = INT 1"
 ; "iVal(Bits28 #0000000000000000000000000010) = INT 2"
 ; "iVal(Bits28 #0000000000000000000000000011) = INT 3"
 ; "iVal(Bits28 #0000000000000000000000000100) = INT 4"
 ; "iVal(Bits28 #0000000000000000000000000101) = INT 5"
 ; "iVal(Bits28 #0000000000000000000000000110) = INT 6"
 ; "iVal(Bits28 #0000000000000000000000000111) = INT 7"
 ; "iVal(Bits28 #0000000000000000000000001000) = INT 8"
 ; "iVal(Bits28 #0000000000000000000000001001) = INT 9"
 ; "iVal(Bits28 #0000000000000000000000001010) = INT 10"
 ; "iVal(Bits28 #0000000000000000000000001011) = INT 11"
 ; "iVal(Bits28 #0000000000000000000000001100) = INT 12"
 ; "iVal(Bits28 #0000000000000000000000001101) = INT 13"
 ; "iVal(Bits28 #0000000000000000000000001110) = INT 14"
 ; "iVal(Bits28 #0000000000000000000000001111) = INT 15"
 ; "iVal(Bits28 #0000000000000000000000010000) = INT 16"
 ; "iVal(Bits28 #0000000000000000000000010001) = INT 17"
 ; "iVal(Bits28 #0000000000000000000000010010) = INT 18"
 ; "iVal(Bits28 #0000000000000000000000010011) = INT 19"
 ; "iVal(Bits28 #0000000000000000000000010100) = INT 20"
 ; "iVal(Bits28 #0000000000000000000000010101) = INT 21"
];;

let less_thans = prove
 ("(1 < 2) /\
   (2 < 3) /\
   (3 < 4) /\
   (4 < 5) /\
   (5 < 6) /\
   (6 < 7) /\
   (7 < 8) /\
   (8 < 9) /\
   (9 < 10) /\
   (10 < 11) /\
   (11 < 12) /\
   (12 < 13) /\
   (13 < 14) /\
   (14 < 15) /\
   (15 < 16) /\
   (16 < 17) /\
   (17 < 18) /\
   (18 < 19) /\
   (19 < 20) /\
   (20 < 21)",
   REPEAT (CONJ_TAC
	   THEN ((CONV_TAC(RAND_CONV num_CONV)
			  THEN MATCH_ACCEPT_TAC LESS_SUC_REFL)
		 ORELSE ALL_TAC))
  );;

letrec gen_trans thl =
 (thl = [])
 => []
  | (length thl = 1)
    => thl
     | (hd thl) 
       . gen_trans ((MATCH_MP LESS_TRANS (CONJ(hd(tl thl)) (hd thl))) 
                    . (tl(tl thl)));;

let generate_inequalities n =
  (n < 2) => []
           | map (EQF_INTRO o SYM_RULE o (MATCH_MP LESS_NOT_EQ))
                 (gen_trans (rev (seg (0,n-2) (CONJUNCTS less_thans))));;

% ================================================================= %
let or_and_distrib = prove
("!a b c. (a \/ b) /\ c = (a /\ c) \/ (b /\ c)",
 REPEAT GEN_TAC THEN BOOL_CASES_TAC "c:bool" THEN rt[]);;

% ================================================================= %
let OR_ASSOC = prove
("!a b c. (a \/ b) \/ c = a \/ b \/ c",
 REPEAT GEN_TAC THEN BOOL_CASES_TAC "a:bool" THEN rt[]);;

% ================================================================= %
let solve_instruction_tac = (\ (iVal_thm,num,thm). \th.
           SUBST1_TAC (is_conj(concl th) => CONJUNCT1 th | th)
	   THEN REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC th
	   THEN SUBST1_TAC iVal_thm
	   THEN SUBST1_TAC (EQT_INTRO (REFL "INT ^(mk_const (string_of_int num, ":num"))"))
     	   THEN port[COND_CLAUSES]
           THEN port[INT_ONE_ONE]
	   THEN port (generate_inequalities num)
	   THEN prt[COND_CLAUSES]
	   THEN (MATCH_ACCEPT_TAC thm
                 ORELSE ALL_TAC)
      );;

letrec solve_all_instructions_tac lst =
 (lst = [])
 => ASSUME_TAC
  | DISJ_CASES_THEN2
    (solve_instruction_tac (hd lst))
    (\th. (is_disj (concl th))
          => (solve_all_instructions_tac (tl lst) th)
	   | (solve_instruction_tac (hd(tl lst)) th)
    );;
%< 
letrec solve_all_instructions_tac lst th =
 (lst = [])
 => ASSUME_TAC th
  | ((DISJ_CASES_THEN2
    (solve_instruction_tac (hd lst))
    (\th. (is_disj (concl th))
           => (solve_all_instructions_tac (tl lst) th)
	    | (solve_instruction_tac (hd(tl lst)) th))
     th)
     ORELSE ASSUME_TAC th);;
>%
timer false;;

let lst =
[ iVal_1, 1, correctness_LD
; iVal_2, 2, theorem `correctness_LDC` `correctness_LDC`
; iVal_3, 3, theorem `correctness_LDF` `correctness_LDF`
; iVal_4, 4, theorem `correctness_AP` `correctness_AP`
; iVal_7, 7, theorem `correctness_RAP` `correctness_RAP`
; iVal_5, 5, theorem `correctness_RTN` `correctness_RTN`
; iVal_6, 6, theorem `correctness_DUM` `correctness_DUM`
; iVal_8, 8, theorem `correctness_SEL` `correctness_SEL`
; iVal_9, 9, theorem `correctness_JOIN` `correctness_JOIN`
; iVal_10, 10, theorem `correctness_CAR` `correctness_CAR`
; iVal_11, 11, theorem `correctness_CDR` `correctness_CDR`
; iVal_12, 12, theorem `correctness_ATOM` `correctness_ATOM`
; iVal_13, 13, theorem `correctness_CONS` `correctness_CONS`
; iVal_14, 14, theorem `correctness_EQ` `correctness_EQ`
; iVal_15, 15, theorem `correctness_ADD` `correctness_ADD`
; iVal_16, 16, theorem `correctness_SUB` `correctness_SUB`
; iVal_20, 20, theorem `correctness_LEQ` `correctness_LEQ`
; iVal_21, 21, theorem `correctness_STOP` `correctness_STOP`
];;

timer true;;
% ================================================================= %
% The top level correctness goal.  It will be attacked by splitting %
% it up into 1 + 6 + 21 (or more) cases, corresponding to:          %
%        - the initial state (0:^ctime)                             %
%        - the 6 transitions controlled by the button input         %
%        - the 21 transition for SECD machine instructions          %
% ================================================================= %
set_goal
 ( [ "!t:^mtime.
      (state_abs(mpc t) = top_of_cycle) ==>
      (!x:word14. garbage_bits((memory t) x) = #00)"
   ; DEC28_assum2
   ; DEC28_assum1
   ; free_list_Constraint
   ; reserved_words_Constraint
   ; valid_program_Constraint
   ; clock_Constraint
   ; SYS_imp
   ],
  "SYS_spec ((mem_abs o memory) when (is_major_state mpc))
             (s                 when (is_major_state mpc))
             (e                 when (is_major_state mpc))
             (c                 when (is_major_state mpc))
             (d                 when (is_major_state mpc))
             (free              when (is_major_state mpc))
             (button_pin        when (is_major_state mpc))
             ((state_abs o mpc) when (is_major_state mpc))
  ");;

expand
(port[SYS_spec]
 THEN CONJ_TAC
 THENL
 [ IMP_RES_n_THEN 2 MATCH_ACCEPT_TAC thm_initial_state
 ; GEN_TAC
   THEN ASSUME_TAC liveness
   THEN port[UNCURRY_DEF] THEN BETA_TAC
   THEN port[UNCURRY_DEF] THEN BETA_TAC
   THEN port[UNCURRY_DEF] THEN BETA_TAC
   THEN port[UNCURRY_DEF] THEN BETA_TAC
   THEN port[UNCURRY_DEF] THEN BETA_TAC
   THEN port[UNCURRY_DEF] THEN BETA_TAC
					% rewrite (state_abs o mpc) when ... %
   THEN SUBST1_TAC (((in1_conv_rule BETA_CONV)
		     o (porr[o_THM]))
		    (AP_THM (SPECL [ "(state_abs o (mpc:^w9_mvec))"
				   ; "is_major_state (mpc:^w9_mvec)"]
				   (INST_TYPE [":^state",":*"]when))
			    "t:^mtime"))

					% split into 4 major states %
   THEN IMP_RES_THEN (STRIP_ASSUME_TAC
		      o (rr[is_major_state])
		      o (SPEC "t:^mtime")) TimeOf_TRUE
   THEN FIRST_ASSUM				% state_abs is top_of_cycle %
      (\th. (ASSUME_TAC o (porr[state_abs_thm])
			o (AP_TERM "state_abs")) th ? NO_TAC)
   THEN poart[]
   THEN port[states_distinct; SYM_RULE states_distinct]
   THEN rt[]
   THENL
   [ COND_CASES_THEN (ASSUME_TAC
		      o (porr[o_THM])
		      o (in_conv_rule BETA_CONV)
		      o (rr[when]))
     THENL
     [ IMP_RES_n_THEN 2 STRIP_ASSUME_TAC
                      (CONJUNCT1 (SPEC "TimeOf(is_major_state mpc)t"
				       (porr[valid_program_constraint]
					(ASSUME valid_program_Constraint))))
       THEN MATCH_ACCEPT_TAC (theorem `correctness_init` `correctness_idle_1`)
     ; MATCH_ACCEPT_TAC (theorem `correctness_init` `correctness_idle_2`)
     ]
   ; CONV_TAC (RATOR_CONV(RATOR_CONV(ONCE_DEPTH_CONV(CHANGED_CONV(REWR_CONV when)))))
     THEN BETA_TAC
     THEN MATCH_ACCEPT_TAC (theorem `correctness_init` `correctness_error0`)
   ; RES_TAC
     THEN port[NEXT]
     THEN CONV_TAC(RAND_CONV(ONCE_DEPTH_CONV(CHANGED_CONV(REWR_CONV when))))
     THEN BETA_TAC
     THEN port[o_THM]
     THEN IMP_RES_THEN ASSUME_TAC
                       (prr[or_and_distrib; OR_ASSOC; SYM_RULE CONJ_ASSOC]
                        (CONJUNCT2 (SPEC "TimeOf(is_major_state mpc)t"
			 		 (porr[valid_program_lemma]
					  (ASSUME valid_program_Constraint)))))
     THEN IMP_RES_n_THEN 2 port1 opcode_mem_abs_lemma
     THEN port [LET_DEF] THEN BETA_TAC
     THEN POP_ASSUM(solve_all_instructions_tac lst)
   ; CONV_TAC (RATOR_CONV(RATOR_CONV(ONCE_DEPTH_CONV(CHANGED_CONV(REWR_CONV when)))))
     THEN BETA_TAC
     THEN MATCH_ACCEPT_TAC (theorem `correctness_init` `correctness_error1`)
   ]
 ]);;

% ================================================================= %
% The final theorem simply eliminates the previously proved         %
% hypotheses concerning DEC28.                                      %
% ================================================================= %
let SECD_implements_specification =  save_thm
(`SECD_implements_specification`,
 PROVE_HYP DEC28_thm1 (PROVE_HYP DEC28_thm2 (top_thm ()))
 );;

timer false;;
close_theory ();;
print_theory `-`;;
