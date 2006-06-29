% SECD verification                                                 %
%                                                                   %
% FILE:         mu-prog_proof0.ml                                   %
%                                                                   %
% DESCRIPTION:  This proves the correctness of the initial          %
%               state of the top level spec.   .                    %
%                                                                   %
% USES FILES:   constraints.th, mem_abs.th, when.th                 %
%               phase_lemmas1                                       %
%                                                                   %
% Brian Graham 89.11.22                                             %
%                                                                   %
% Modifications:                                                    %
% 89.12.05 - separated this from "attempt1.ml"                      %
% 90.01.08 - updated to revised phase_lemmas format                 %
%                                                                   %
% ================================================================= %
new_theory `mu-prog_proof0`;;

loadf `wordn`;;
% load_library `unwind`;; %

map new_parent [ `mem_abs`
               ; `when`
               ; `phase_lemmas1`
               ];;

map (load_definition `when`)
    [ `when`
    ; `TimeOf`
    ; `IsTimeOf`
    ];;
load_theorem `when` `IsTimeOf_IDENTITY`;;

map (load_definition `constraints`)
    [ `is_major_state`
    ; `state_abs`
    ];;
loadt `SELECT_UNIQUE`;;

load_theorem `phase_lemmas1` `phase_lemma_0`;;
let word9_EQ_CONV = wordn_EQ_CONV (theorem `cu_types` `Word9_11`);;

% ================================================================= %
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
% ================================================================= %
% The initial state proof.                                          %
% ================================================================= %

% ================================================================= %
% .. |- mpc 0 = #000000000                                          %
% ================================================================= %
let lemma_t_0 = (CONJUNCT1 o UNDISCH o fst o EQ_IMP_RULE o UNDISCH)
               (theorem `SYS_proofs` `SYS_Unwound_lemma`);;

let SYS_imp = (hd o tl o hyp) lemma_t_0;;

let clock_constraint = "clock_constraint SYS_Clocked";;
                                                 
timer true;;
% ================================================================= %
% .. |- (mpc(SUC 0) = #000010110)                                   %
% ================================================================= %
let lemma_t1 =
   CONJUNCT1 (MP (SPEC "0" (GEN "t:^mtime" phase_lemma_0)) lemma_t_0);;

% ================================================================= %
% .. |- ~is_major_state mpc 0                                       %
% ================================================================= %
let lemma_state0 = TAC_PROOF
 (([SYS_imp], "~(is_major_state mpc 0)"),
  part[is_major_state; lemma_t_0]
  THEN in1_conv_tac word9_EQ_CONV
  THEN rt[]);;

% ================================================================= %
% .. |- is_major_state mpc(SUC 0)                                   %
% ================================================================= %
let lemma_state1 = save_thm
(`lemma_state1`,
 TAC_PROOF
  (([SYS_imp; clock_constraint],"is_major_state mpc (SUC 0)"),
   rt[is_major_state; lemma_t1]));;

% ================================================================= %
% .. |- TimeOf(is_major_state mpc)0 = SUC 0                         %
% ================================================================= %
let lemma_startup = TAC_PROOF
(([SYS_imp; clock_constraint],
   "TimeOf (is_major_state mpc) 0 = (SUC 0)"),
  port[TimeOf]
  THEN SELECT_UNIQUE_TAC
  THENL
  [ rt [IsTimeOf; lemma_state1; LESS_THM; NOT_LESS_0]
    THEN GEN_TAC
    THEN DISCH_THEN (\th. rt[th; lemma_state0])
  ; rt [IsTimeOf_IDENTITY]
  ]
 );;

% ================================================================= %
% |- clock_constraint SYS_Clocked ==>                               %
%    ^SYS_imp  ==>                                                  %
%    (((state_abs o mpc) when (is_major_state mpc))0 = idle)        %
% ================================================================= %
let thm_initial_state = prove_thm
(`thm_initial_state`,
 "^clock_constraint ==> ^SYS_imp ==> 
  (((state_abs o mpc) when (is_major_state mpc)) 0 = idle)",
 DISCH_TAC
 THEN DISCH_TAC
 THEN port [when]
 THEN in1_conv_tac BETA_CONV
 THEN prt [lemma_startup; o_DEF]
 THEN in1_conv_tac BETA_CONV
 THEN rt [state_abs; lemma_t1]
 );;

timer false;;
close_theory ();;
print_theory `-`;;
