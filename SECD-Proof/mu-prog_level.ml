% SECD verification                                                 %
%                                                                   %
% FILE:         mu-prog_level.ml                                    %
%                                                                   %
% DESCRIPTION:  This file is loaded by proof_fcn.ml to provide      %
%               the theorems required for microprogramming level    %
%               proofs of all code sequences above subroutines.     %
%                                                                   %
% USES FILES:   constraints.th                                      %
%                                                                   %
% Brian Graham 90.04.04                                             %
%                                                                   %
% Modifications:                                                    %
% ================================================================= %
new_theory `mu-prog_level`;;

new_parent `constraints`;;

map (load_theorem `constraints`)
[ `state_abs_thm`
; `free_list_constraint_thm`
];;
% ================================================================= %
let mtime = ":num";;

timer true;;
% ================================================================= %
% This theorem provides the maximum of 4 clauses to eliminate the   %
% constraint on the free list pointer required by the conx1x2 and   %
% numberbuf subroutines.                                            %
% ================================================================= %
let free_list_thm = save_thm
(`free_list_thm`,
 ( (PROVE_HYP ((( porr[state_abs_thm])
		o (AP_TERM "state_abs")
		o ASSUME) "mpc (t:^mtime) = #000101011"))
 o UNDISCH
 o (SPEC "t:^mtime")
 o (prr[AND_CLAUSES; IMP_CLAUSES])
 o (PURE_ONCE_ASM_REWRITE_RULE [])
 o (ADD_ASSUM "reserved_words_constraint mpc memory")
 o (ADD_ASSUM "well_formed_free_list memory mpc free s e c d"))
 free_list_constraint_thm);;

% ================================================================= %
% This bit will be used to prove that we don't hit a major state in %
% the microcode addresses we get to.                                %
% ================================================================= %
% ================================================================= %
% Next_step =                                                       %
% |- !ts tf f.                                                      %
%     ~f tf /\ (!t. ts < t /\ t < tf ==> ~f t) ==>                  %
%     (!t. ts < t /\ t < (SUC tf) ==> ~f t)                         %
% ================================================================= %
let Next_step = prove_thm
(`Next_step`,
 "! (ts tf:num) f.
          (~(f tf) /\
           !t. (ts < t) /\ (t < tf) ==> ~(f t)) ==>
          (!t. (ts < t) /\ (t < (SUC tf)) ==> ~(f t))",
 REPEAT GEN_TAC
 THEN STRIP_TAC
 THEN GEN_TAC
 THEN port[LESS_THM]
 THEN STRIP_TAC
 THENL
 [ art[]
 ; RES_TAC
 ]);;

% ================================================================= %
% Next_interval =                                                   %
% |- !ts tm tf f.                                                   %
%     (!t. ts < t /\ t < (SUC tm) ==> ~f t) /\                      %
%     (!t. tm < t /\ t < tf ==> ~f t) ==>                           %
%     (!t. ts < t /\ t < tf ==> ~f t)                               %
% ================================================================= %
let Next_interval = prove_thm
(`Next_interval`,
 "!ts tm tf f.
    (!t. ts < t /\ t < (SUC tm) ==> ~f t) /\
    (!t. tm < t /\ t < tf ==> ~f t) ==>
    (!t. ts < t /\ t < tf ==> ~f t)",
 REPEAT GEN_TAC
 THEN STRIP_TAC
 THEN GEN_TAC
 THEN STRIP_TAC
 THEN ASM_CASES_TAC "t < (SUC tm)"
 THENL [ALL_TAC; IMP_RES_TAC (porr[SYM_RULE NOT_LESS]OR_LESS)]
 THEN RES_TAC);;

% ================================================================= %
% A similar theorem used only in the while loop proofs of proof_LD. %
% ================================================================= %
let Next_interval' = prove_thm
(`Next_interval'`,
 "!ts tm tf f.
    (!t. ts < t /\ t < tm ==> ~f t) /\
    (!t. (PRE tm) < t /\ t < tf ==> ~f t) ==>
    (!t. ts < t /\ t < tf ==> ~f t)",
 REPEAT GEN_TAC
 THEN DISJ_CASES_THEN2 SUBST1_TAC
      (CHOOSE_THEN SUBST1_TAC)(SPEC "tm:num" num_CASES)
 THENL
 [ rt[PRE; NOT_LESS_0]
   THEN STRIP_TAC
   THEN GEN_TAC
   THEN STRIP_TAC 
   THEN FIRST_ASSUM MATCH_MP_TAC
   THEN art[]
   THEN DISJ_CASES_THEN2 SUBST_ALL_TAC
        (CHOOSE_THEN SUBST_ALL_TAC)(SPEC "t:num" num_CASES)
   THENL
   [ IMP_RES_TAC NOT_LESS_0
   ; MATCH_ACCEPT_TAC LESS_0
   ]
 ; port[PRE]
   THEN  MATCH_ACCEPT_TAC Next_interval
 ]);;

% ================================================================= %
% Empty_range =                                                     %
% |- !t t'. ~((PRE t') < t /\ t < t')                               %
% ================================================================= %
let Empty_range = prove_thm
(`Empty_range`,
 "! t t'. ~(PRE t' < t /\ t < t')",
 GEN_TAC
 THEN INDUCT_TAC
 THEN prt [PRE]
 THENL
 [ rt[LESS_ANTISYM]
 ; STRIP_TAC
   THEN IMP_RES_THEN
      (DISJ_CASES_THENL
       ([ \th. SUBST_ALL_TAC th THEN IMP_RES_TAC LESS_REFL
        ; \th. ASSUME_TAC th THEN IMP_RES_TAC LESS_ANTISYM]))
	  ((fst o EQ_IMP_RULE o SPEC_ALL) LESS_THM)
 ]);;

% ================================================================= %
% Start_lem :                                                       %
% |- !t' f t. (PRE t') < t /\ t < t' ==> ~f t                       %
% ================================================================= %
let Start_lem = prove_thm
(`Start_lem`,
 "! t' f t. (PRE t' < t) /\ (t < t') ==> ~(f t)",
 rt[Empty_range]
 );;

% ================================================================= %
% Initial_range_thm :                                               %
% |- !t''. t < t'' /\ t'' < (SUC t) ==> ~is_major_state mpc t''     %
% ================================================================= %
let Initial_range_thm = save_thm
(`Initial_range_thm`,
 porr[PRE](SPECL ["SUC t:^mtime";"is_major_state mpc"] Start_lem));;

% ================================================================= %
% join_branches_thm :                                               %
%  |- ((x = T) ==> a) /\ ((x = F) ==> b) = (x => a | b)             %
% ================================================================= %
let join_branches_thm = prove_thm
(`join_branches_thm`,
 "((x = T) ==> a) /\ ((x = F) ==> b) = (x => a | b)",
  COND_CASES_TAC THEN art[]);;

let F_refld = save_thm (`F_refld`, EQT_INTRO (REFL "F"));;
let PRE_SUC = save_thm (`PRE_SUC`, CONJUNCT2 PRE);;

timer false;;
close_theory ();;
print_theory`-`;;
