% SECD verification                                                 %
%                                                                   %
% FILE:         correctness_RTN.ml                                  %
%                                                                   %
% DESCRIPTION:  The correspondence between the specification for    % 
%               RTN instruction, and the computational effect of    %
%               the machine executing an RTN instruction.           %
%                                                                   %
% USES FILES:   correctness_misc.th, wordn & integer libraries      %
%               liveness - only to get at ancestor theories ...     %
%                                                                   %
% Brian Graham 06.12.90                                             %
%                                                                   %
% Modifications:                                                    %
% 08.08.91 - BtG - updated to HOL2                                  %
% ================================================================= %
new_theory `correctness_RTN`;;

map new_parent
 [ `correctness_misc`
 ; `liveness`
 ];;

loadf `wordn`;;
load_library `integer`;;

map (load_theorem `correctness_misc`)
 [ `LET_THM`
 ; `Store14_root_1_lemma`
 ; `Store14_car_cdr_1_lemma`
 ; `Store14_cadr_cddr_1_lemma`
 ; `RTN_opcode_lemma`
 ];;

map (load_definition `when`)
 [ `when`
 ];;
map (load_theorem `when`)
 [ `TimeOf_Next_lemma`
 ];;

map (load_definition `constraints`)
 [ `reserved_words_constraint`
 ];;
map (load_theorem `constraints`)
 [ `state_abs_thm`
 ; `well_formed_free_list_lemma`
 ; `well_formed_free_list_nonintersection_lemma`
 ];;
map (load_definition `top_SECD`)
 [ `RTN_trans`
 ; `cell_of`
 ; `mem_free_of`
 ; `mem_of`
 ; `free_of`
 ];;
map (load_theorem `mu-prog_RTN`)
 [ `RTN_state`
 ; `RTN_Next`
 ];;
map (load_definition `abstract_mem_type`)
 [ `M_CAR`
 ; `M_CDR`
 ];;
map (load_theorem `mem_abs`)
 [ `car_cdr_mem_abs_lemma`
 ; `M_Cons_unfold_1_thm`
 ];;
% ================================================================= %
let mtime = ":num"
and ctime = ":num";;
let w14_mvec = ":^mtime->word14";;

let mem14_32 = ":word14->word32";;
let m14_32_mvec = ":^mtime->^mem14_32";;
let M = ":(word14,atom)mfsexp_mem";;
let M_mvec = ":^mtime->^M";;

let state = ":bool # bool";;
let state_msig = ":^mtime->^state"
and state_csig = ":^ctime->^state";;

% ================================================================= %
% This defines a relation on the inputs and outputs.                %
% ================================================================= %
let SYS_imp = (hd o tl o hyp)(theorem `phase_lemmas1` `phase_lemma_0`);;

% ================================================================= %
loadt `ABBREV_TAC`;;

% ================================================================= %
timer true;;

% ================================================================= %
% Discharge every assumption with "t" in it, and generalize it.     %
% ================================================================= %
let RTN_state' =
 GEN "t:^mtime" 
 (DISCH "mpc (t:^mtime) = #000101011"
  (DISCH "opcode_bits((memory:^m14_32_mvec) t(car_bits(memory t(c t))))
          = #000000101"
         RTN_state));;
let RTN_Next' =
 GEN "t:^mtime" 
 (DISCH "mpc (t:^mtime) = #000101011"
  (DISCH "opcode_bits((memory:^m14_32_mvec) t(car_bits(memory t(c t))))
          = #000000101"
         RTN_Next));;

% ================================================================= %
% Correctness goal for the RTN instruction.                         %
% ================================================================= %
let correctness_RTN = TAC_PROOF
(([
   % ----------------------------- (cdr c) is NIL %
   "cdr_bits(memory(TimeOf(is_major_state mpc)t)
                   ((c:^w14_mvec)(TimeOf(is_major_state mpc)t))) =
    NIL_addr"
 ; % ----------------------------- (cddr d) is a cons cell %
   "is_cons(memory(TimeOf(is_major_state mpc)t)
            (cdr_bits(memory(TimeOf(is_major_state mpc)t)
             (cdr_bits(memory(TimeOf(is_major_state mpc)t)
                     ((d:^w14_mvec)(TimeOf(is_major_state mpc)t)))))))"
 ; % ----------------------------- (cdr d) is a cons cell %
   "is_cons(memory(TimeOf(is_major_state mpc)t)
            (cdr_bits(memory(TimeOf(is_major_state mpc)t)
                     ((d:^w14_mvec)(TimeOf(is_major_state mpc)t)))))"
 ; % ----------------------------- d is a cons cell %
   "is_cons(memory(TimeOf(is_major_state mpc)t)
            ((d:^w14_mvec)(TimeOf(is_major_state mpc)t)))"
 ; % ----------------------------- s is a cons cell %
   "is_cons(memory(TimeOf(is_major_state mpc)t)
            ((s:^w14_mvec)(TimeOf(is_major_state mpc)t)))"
 ; % ----------------------------- the opcode is RTN %
   "atom_bits(memory(TimeOf(is_major_state mpc)t)
            (car_bits(memory(TimeOf(is_major_state mpc)t)
                      ((c:^w14_mvec)(TimeOf(is_major_state mpc)t))))) =
    #0000000000000000000000000101" 
 ; % ----------------------------- opcode is a number record %
   "is_number(memory(TimeOf(is_major_state mpc)t)
              (car_bits(memory(TimeOf(is_major_state mpc)t)
                        ((c:^w14_mvec)(TimeOf(is_major_state mpc)t)))))"
 ; % ----------------------------- c is itself a cons cell %
   "is_cons(memory(TimeOf(is_major_state mpc)t)
            ((c:^w14_mvec)(TimeOf(is_major_state mpc)t)))"
 ; "mpc(TimeOf(is_major_state mpc)t) = #000101011" 
 ; "Inf(is_major_state mpc)"
 ; "well_formed_free_list memory mpc free s e c d"
 ; "reserved_words_constraint mpc memory" 
 ; SYS_imp
 ; "clock_constraint SYS_Clocked" 
 ],
 "((s                  when (is_major_state mpc))(SUC t),    
    (e                  when (is_major_state mpc))(SUC t),
    (c                  when (is_major_state mpc))(SUC t),
    (d                  when (is_major_state mpc))(SUC t),
    (free               when (is_major_state mpc))(SUC t), 
    ((mem_abs o memory) when (is_major_state mpc))(SUC t), 
    ((state_abs o mpc)  when (is_major_state mpc))(SUC t)) =
    RTN_trans ((s                  when (is_major_state mpc))t,
               (e                  when (is_major_state mpc))t,
               (c                  when (is_major_state mpc))t,
               (d                  when (is_major_state mpc))t,
               (free               when (is_major_state mpc))t,
               ((mem_abs o memory) when (is_major_state mpc))t)
 "),
 FIRST_ASSUM				% state_abs is top_of_cycle %
      (\th. (ASSUME_TAC o (porr[state_abs_thm])
			o (AP_TERM "state_abs")) th ? NO_TAC)
 THEN IMP_RES_TAC RTN_opcode_lemma 		% opcode_bits assumption %
 THEN port[when]
 THEN in_conv_tac BETA_CONV
					% Next assumption %
 THEN IMP_RES_THEN (ASSUME_TAC o UNDISCH) RTN_Next'
 					% rewrite Timeof ... (SUC t) %
 THEN IMP_RES_n_THEN 2 port1 TimeOf_Next_lemma
 THEN port[o_THM]
					% abbreviate times for readability ... %
 THEN ABBREV_TAC "(TimeOf(is_major_state mpc)t)" "t':num"
					% generate req'd assumptions ... %
 THEN IMP_RES_n_THEN 3 ASSUME_TAC
                       well_formed_free_list_lemma
	    % only 3 of the 6 free cell inequalities are likely needed %
 THEN IMP_RES_n_THEN 2			% mem0 NIL_addr = ... %
      (\th. (free_in "NIL_addr" (concl th)) => ASSUME_TAC th | ALL_TAC)
      reserved_words_constraint
 THEN IMP_RES_n_THEN 2			% nonintersecting mem0 free [s;e;c] %
      (\th. (free_in "d:^w14_mvec" (concl th))
             => ASSUME_TAC th
              | ALL_TAC)
      well_formed_free_list_nonintersection_lemma

 THEN port[RTN_trans]                    % unfold spec %
% ================================================================= %
			                % expand the M_* ops %
 THEN port[M_CAR]                       % rewrite M_CAR d, M_Car s %
 THEN IMP_RES_THEN port1 car_cdr_mem_abs_lemma
					% rewrite the 1st M_Cons %
 THEN IMP_RES_n_THEN 3 port1 (hd(IMP_CANON M_Cons_unfold_1_thm))
					% unwind the s_mem_free let binding %
 THEN port[LET_THM]
 THEN in1_conv_tac BETA_CONV
 THEN prt[cell_of; free_of; mem_of; mem_free_of]

 THEN port[M_CDR]			% unwind M_CDR (d,mem1, ) %
 THEN IMP_RES_n_THEN 3
      ((IMP_RES_THEN (port1 o (MATCH_MP car_cdr_mem_abs_lemma) o SPEC_ALL))
       o snd
       o EQ_IMP_RULE
       o (AP_TERM "is_cons")
       o SPEC_ALL)
      (hd(IMP_CANON Store14_root_1_lemma))
 THEN port[M_CDR]			% unwind M_CDR (cdr(mem1 d),mem1, ) %
 THEN IMP_RES_n_THEN 4			% and M_Car (cdr(mem1 d),mem1, ) %
      ((IMP_RES_THEN (port1 o (MATCH_MP car_cdr_mem_abs_lemma) o SPEC_ALL))
       o snd
       o EQ_IMP_RULE
       o (AP_TERM "is_cons")
       o SPEC_ALL)
      (hd(IMP_CANON Store14_car_cdr_1_lemma))
 THEN IMP_RES_n_THEN 5			% unwind M_Ca/dr (cddr(mem1 d),mem1, ) %
      ((IMP_RES_THEN (port1 o (MATCH_MP car_cdr_mem_abs_lemma) o SPEC_ALL))
       o snd
       o EQ_IMP_RULE
       o (AP_TERM "is_cons")
       o SPEC_ALL)
      (hd(IMP_CANON Store14_cadr_cddr_1_lemma))
					% simplify _imp view %
 THEN IMP_RES_THEN (SUBST1_TAC o UNDISCH) RTN_state'
 THEN port[state_abs_thm]
 THEN REFL_TAC
 );;

% ================================================================= %
save_thm(`correctness_RTN`,correctness_RTN);;

timer false;;
close_theory ();;
print_theory `-`;;
