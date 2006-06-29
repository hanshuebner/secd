% SECD verification                                               %
%                                                                 %
% FILE:                liveness.ml                                %
%                                                                 %
% DESCRIPTION:  This file proves the liveness of the machine,     %
%               under the given constraints.                      %
%                                                                 %
% USES FILES:   proof_LD.th, ..., proof_STOP.th                   %
%                                                                 %
% Brian Graham 90.04.18                                           %
%                                                                 %
% Modifications:                                                  %
% 07.08.91 - updated to HOL2.0                                    %
%=================================================================%
new_theory `liveness`;;

map new_parent
 [ `mu-prog_LD`           ; `mu-prog_LDC`          ; `mu-prog_LDF`         
 ; `mu-prog_AP`           ; `mu-prog_RTN`          ; `mu-prog_DUM`
 ; `mu-prog_RAP`          ; `mu-prog_SEL`          ; `mu-prog_JOIN`        
 ; `mu-prog_CAR`          ; `mu-prog_CDR`          ; `mu-prog_ATOM`
 ; `mu-prog_CONS`         ; `mu-prog_EQ`           ; `mu-prog_ADD`
 ; `mu-prog_SUB`          ; `mu-prog_LEQ`          ; `mu-prog_STOP`
 ; `mu-prog_proof0`
 ];;
map (uncurry load_theorem)
 [ `mu-prog_LD`		, `LD_Next`
 ; `mu-prog_LDC`	, `LDC_Next`
 ; `mu-prog_LDF`	, `LDF_Next`
 ; `mu-prog_AP`		, `AP_Next`
 ; `mu-prog_RTN`	, `RTN_Next`
 ; `mu-prog_DUM`	, `DUM_Next`
 ; `mu-prog_RAP`	, `RAP_Next`
 ; `mu-prog_SEL`	, `SEL_Next`
 ; `mu-prog_JOIN`	, `JOIN_Next`
 ; `mu-prog_CAR`	, `CAR_Next`
 ; `mu-prog_CDR`	, `CDR_Next`
 ; `mu-prog_ATOM`	, `ATOM_Next`
 ; `mu-prog_CONS`	, `CONS_Next`
 ; `mu-prog_EQ`		, `EQ_Next`
 ; `mu-prog_ADD`	, `ADD_Next`
 ; `mu-prog_SUB`	, `SUB_Next`
 ; `mu-prog_LEQ`	, `LEQ_Next`
 ; `mu-prog_STOP`	, `STOP_Next`
 ; `mu-prog_proof0`	, `lemma_state1`
 ; `mu-prog_init_proofs`	, `idle_Next`
 ; `mu-prog_init_proofs`	, `error0_Next`
 ; `mu-prog_init_proofs`	, `error1_Next`
 ];;

map (load_definition `when`)
    [ `Next`
    ; `Inf`
    ];;
map (load_definition `constraints`)
    [ `is_major_state`
    ];;
map (load_theorem `constraints`)
    [ `state_abs_thm`
    ; `valid_program_IMP_valid_codes`
    ; `valid_codes_lemma`
    ];;
%%
%=================================================================%
let mtime = ":num";;

let msig = ":^mtime->bool"
and w9_mvec = ":^mtime->word9"
and w14_mvec = ":^mtime->word14"
and w27_mvec = ":^mtime->word27"
and w32_mvec = ":^mtime->word32";;

let mem14_32 = ":word14->word32";;
let m14_32_mvec = ":^mtime->^mem14_32";;
let M = ":(word14,atom)mfsexp_mem";;
let M_mvec = ":^mtime->^M";;

let state = ":bool # bool";;
let state_msig = ":^mtime->^state";;

%=================================================================%
% Assumptions:                                                    %
% base_assumptions include:                                       %
%  - clock_constraint                                             %
%  - ^SYS_imp                                                     %
%  - reserved_words_constraint                                    %
%  - well_formed_free_list                                        %
%=================================================================%
let base_assumptions =
 (rev o tl o tl o rev)(hyp STOP_Next);;

let valid_program_Constraint =
   "valid_program_constraint memory mpc button_pin s e c d";;

let DEC28_assum1 =
"!w28. (POS (iVal (Bits28 w28)))==>
        (PRE(pos_num_of(iVal(Bits28 w28))) =
           pos_num_of(iVal(Bits28((atom_bits o DEC28) w28))))"
and DEC28_assum2 =
"!w28.(POS (iVal (Bits28 w28)))==>
     ~(NEG (iVal (Bits28 ((atom_bits o DEC28) w28))))";;
%%
% ================================================================= %
% Tactics and theorems used in the main proof.                      %
% ================================================================= %
% First, to discharge several assumptions:                          %
% ================================================================= %
letrec DISCHL l th =
  (l = []) => th | DISCH (hd l) (DISCHL (tl l) th);;


timer true;;
% ================================================================= %
% The fact that Next holds gives the desired result for liveness.   %
% ================================================================= %
let Next_exists_thm = TAC_PROOF
(([], "!t1 t2 f. Next t1 t2 f ==> (?t'. (t1 < t' /\ f t'))"),
  REPEAT GEN_TAC
  THEN port[Next]
  THEN STRIP_TAC
  THEN EXISTS_TAC "t2:num"
  THEN art[]);;

% ================================================================= %
% Reduce proof obligation to initial state and cases that begin     %
% in major states, rather than every possible starting state.       %
% ================================================================= %
let Inf_thm = prove_thm
(`Inf_thm`,
 "!f. (?t'. 0 < t' /\ f t') /\
     (!t. f t ==> (?t'. t < t' /\ f t'))  ==> Inf f",
 GEN_TAC
 THEN REPEAT STRIP_TAC
 THEN port[Inf]
 THEN INDUCT_THEN INDUCTION
                  (CHOOSE_THEN (CONJUNCTS_THEN2
				((DISJ_CASES_THEN ASSUME_TAC)
				 o (porr[LESS_OR_EQ])
				 o (MATCH_MP LESS_OR))
				ASSUME_TAC))
 THENL
 [ EXISTS_TAC "t':num"
   THEN art[]
 ; EXISTS_TAC "t'':num" THEN art[]
 ; FIRST_ASSUM SUBST1_TAC
   THEN FIRST_ASSUM (ANTE_RES_THEN MATCH_ACCEPT_TAC)
 ]);;


% ================================================================= %
% This tactic uses the *_Next theorems for each instruction         %
% transition, and solves the liveness subgoal for each branch.      %
% ================================================================= %
let instruction_tactic microprog_thm =
 (is_cond (concl microprog_thm))
 => ((\th. ASSUME_TAC th THEN UNDISCH_TAC(concl th)) microprog_thm
     THEN COND_CASES_TAC
     THEN MATCH_ACCEPT_TAC Next_exists_thm)
  | (MATCH_ACCEPT_TAC (MATCH_MP Next_exists_thm microprog_thm));;

%%
% ================================================================= %
% The main theorem has all the standard assumptions.  The goal is   %
% split into the initial state, and times beginning in major states.%
% This is further split into 4 cases on the definition of           %
% is_major_state.  There are 2 branches for the idle and error      %
% states, and the valid_program_constraint splits the top_of_cycle  %
% state into 18 transitions, each solved by the instruction_tactic. %
% ================================================================= %
let liveness = save_thm
(`liveness`,
 TAC_PROOF
 ((DEC28_assum2
   . DEC28_assum1
   . valid_program_Constraint
   . base_assumptions
   , "Inf (is_major_state mpc)"),
 MATCH_MP_TAC Inf_thm
 THEN CONJ_TAC
 THENL
 [ EXISTS_TAC "SUC 0"
   THEN rt[LESS_0; lemma_state1]
 ; 				% reduce to cases where
   				  "is_major_state mpc t" holds %
   GEN_TAC
   THEN DISCH_THEN ((REPEAT_TCL DISJ_CASES_THEN ASSUME_TAC)
		    o (porr [is_major_state]))
   THENL
   [ IMP_RES_THEN (\th. ASSUME_TAC th THEN UNDISCH_TAC(concl th))
     (DISCHL (filter (free_in "t:num") (hyp idle_Next)) idle_Next)
     THEN COND_CASES_TAC
     THEN MATCH_ACCEPT_TAC Next_exists_thm
   ; IMP_RES_THEN (\th. ASSUME_TAC th THEN UNDISCH_TAC(concl th))
       (DISCHL (filter (free_in "t:num") (hyp error0_Next)) error0_Next)
     THEN COND_CASES_TAC
     THEN MATCH_ACCEPT_TAC Next_exists_thm

   ; FIRST_ASSUM (ASSUME_TAC o (porr[state_abs_thm]) o (AP_TERM "state_abs"))  
     THEN IMP_RES_THEN (IMP_RES_THEN
		        (REPEAT_TCL DISJ_CASES_THEN
			            (REPEAT_TCL CONJUNCTS_THEN
						ASSUME_TAC))
			  o (porr[valid_codes_lemma]))
                         valid_program_IMP_valid_codes
       THENL (map instruction_tactic
	    [ LD_Next
	    ; LDC_Next
	    ; LDF_Next
	    ; AP_Next
	    ; RTN_Next
	    ; DUM_Next
	    ; RAP_Next
	    ; SEL_Next
	    ; JOIN_Next
	    ; CAR_Next
	    ; CDR_Next
	    ; ATOM_Next
	    ; CONS_Next
	    ; EQ_Next
	    ; ADD_Next
	    ; SUB_Next
	    ; LEQ_Next
	    ; STOP_Next
	    ])
   ; IMP_RES_THEN (\th. ASSUME_TAC th THEN UNDISCH_TAC(concl th))
      (DISCHL (filter (free_in "t:num") (hyp error1_Next)) error1_Next)
     THEN COND_CASES_TAC
     THEN MATCH_ACCEPT_TAC Next_exists_thm
   ]
 ]));;

timer false;;
close_theory ();;
print_theory `-`;;
