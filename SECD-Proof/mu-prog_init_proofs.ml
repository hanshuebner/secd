% SECD verification                                                 %
%                                                                   %
% FILE:         mu-prog_init_proofs.ml                              %
%                                                                   %
% DESCRIPTION:  This proves the correctness of the idle to idle,    %
%               etc., transitions.                                  %
%                                                                   %
% USES FILES:   constraints.th, mem_abs.th, when.th                 %
%               phase_lemmas1                                       %
%                                                                   %
% Brian Graham 89.12.05                                             %
%                                                                   %
% Modifications:                                                    %
% 90.04.04 - BtG - switched to well_formed_free_list and            %
%                  reserved_words_constraint from                   %
%                  free_list_constraint                             %
%                                                                   %
% ================================================================= %
new_theory `mu-prog_init_proofs`;;

map new_parent [ `mem_abs`
               ; `when`
               ; `phase_lemmas1`
               ];;

loadt `mu-prog_proof_fcn`;;
load_library `unwind`;;

let idle, error0, error1, top_of_cycle =
      22,     24,     26,           43;;

let ptheory = `phase_lemmas1`;;

letrec truncate i l =
 if i=0 then [] else hd l.truncate(i-1)(tl l);;

letrec seg (m,n) l =
 (if m<0 or n<m then fail
  if m=0 then truncate ((n-m)+1) l
         else seg (m-1,n-1) (tl l)
 ) ? failwith `seg`;;

let start_thm n =
   (LIST_CONJ o (seg (0,5)) o CONJUNCTS o UNDISCH)
         (theorem ptheory (`phase_lemma_`^(string_of_int n))),
   Initial_range_thm;;

timer true;;
% ================================================================= %
% The simple loops proofs.                                          %
% ================================================================= %
let idle_state,idle_Next = save_seq_proof
 ptheory (start_thm idle) (`idle_state`,`idle_Next`);;

let error0_state,error0_Next = save_seq_proof
 ptheory(start_thm error0)(`error0_state`,`error0_Next`);;

let error1_state,error1_Next = save_seq_proof
 ptheory (start_thm error1) (`error1_state`,`error1_Next`);;

% ================================================================= %
% This call doesn't quite get to where we want to go.  Thus, the    %
% returned theorems are fixed up before saving...                   %
% ================================================================= %
let top_of_cycle_state,top_of_cycle_nonmajor =
 recursive (prove_next_step ptheory) (start_thm top_of_cycle);;

% ================================================================= %
% The next value for the mpc is cleaned up here, by rewriting       %
% with the definition of Opcode, then unwinding, and finally        %
% substituting "c t" for "mar_pins t" (which arose because the      %
% initial theorem unwound past where we wanted).                    %
%                                                                   %
% We also add the free list constraint.                             %
% Revised: add the 2 constraints: well_formed_free_list and         %
%                                 reserved_words_constraint         %
% ================================================================= %
let l1 =
  let thl = (CONJUNCTS o UNDISCH) (theorem ptheory `phase_lemma_43`)
  in
  (( (ADD_ASSUM "reserved_words_constraint mpc memory")
   o (ADD_ASSUM "well_formed_free_list memory mpc free s e c d")
   o (SUBS [SUBS [SYM (hd(filter (\th. `c` = line_name(concl th)) thl))]
	         (hd(filter (\th. `mar_pins` = line_name(concl th)) thl))])
   o (CONV_RULE (UNWIND_ONCE_CONV (\tm. line_name tm = `arg`)))
   o (porr[Opcode]))
  top_of_cycle_state);;

let l2 = 
  ( (ADD_ASSUM "reserved_words_constraint mpc memory")
  o (ADD_ASSUM "well_formed_free_list memory mpc free s e c d"))
   top_of_cycle_nonmajor;;

let prove_jump_steps (n, stem) =
  let asm =
    mk_eq ("opcode_bits(memory (t:^mtime)(car_bits(memory t(c t))))",
           mk_word9_from_num n)
  in
  let th1,th2 = prove_next_step ptheory
      (SUBS [ASSUME asm] l1, ADD_ASSUM asm l2)
  in
  (save_thm (`toc_`^stem^`_state`,th1),
   save_thm (`toc_`^stem^`_nonmajor`,th2));;


let toc_LD_state,  toc_LD_nonmajor   = prove_jump_steps ( 1,`LD`  );;
let toc_LDC_state, toc_LDC_nonmajor  = prove_jump_steps ( 2,`LDC` );;
let toc_LDF_state, toc_LDF_nonmajor  = prove_jump_steps ( 3,`LDF` );;
let toc_AP_state,  toc_AP_nonmajor   = prove_jump_steps ( 4,`AP`  );;
let toc_RTN_state, toc_RTN_nonmajor  = prove_jump_steps ( 5,`RTN` );;
let toc_DUM_state, toc_DUM_nonmajor  = prove_jump_steps ( 6,`DUM` );;
let toc_RAP_state, toc_RAP_nonmajor  = prove_jump_steps ( 7,`RAP` );;
let toc_SEL_state, toc_SEL_nonmajor  = prove_jump_steps ( 8,`SEL` );;
let toc_JOIN_state,toc_JOIN_nonmajor = prove_jump_steps ( 9,`JOIN`);;
let toc_CAR_state, toc_CAR_nonmajor  = prove_jump_steps (10,`CAR` );;
let toc_CDR_state, toc_CDR_nonmajor  = prove_jump_steps (11,`CDR` );;
let toc_ATOM_state,toc_ATOM_nonmajor = prove_jump_steps (12,`ATOM`);;
let toc_CONS_state,toc_CONS_nonmajor = prove_jump_steps (13,`CONS`);;
let toc_EQ_state,  toc_EQ_nonmajor   = prove_jump_steps (14,`EQ`  );;
let toc_ADD_state, toc_ADD_nonmajor  = prove_jump_steps (15,`ADD` );;
let toc_SUB_state, toc_SUB_nonmajor  = prove_jump_steps (16,`SUB` );;
let toc_MUL_state, toc_MUL_nonmajor  = prove_jump_steps (17,`MUL` );;
let toc_DIV_state, toc_DIV_nonmajor  = prove_jump_steps (18,`DIV` );;
let toc_REM_state, toc_REM_nonmajor  = prove_jump_steps (19,`REM` );;
let toc_LEQ_state, toc_LEQ_nonmajor  = prove_jump_steps (20,`LEQ` );;
let toc_STOP_state,toc_STOP_nonmajor = prove_jump_steps (21,`STOP`);;

timer false;;
close_theory ();;
print_theory `-`;;


