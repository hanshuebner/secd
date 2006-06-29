% SECD verification                                                 %
%                                                                   %
% FILE:         correctness_EQ.ml                                   %
%                                                                   %
% DESCRIPTION:  The correspondence between the specification for    % 
%               EQ instruction, and the computational effect of     %
%               the machine executing an EQ instruction.            %
%                                                                   %
% USES FILES:   correctness_misc.th, wordn & integer libraries      %
%               liveness - only to get at ancestor theories ...     %
%                                                                   %
% Brian Graham 06.12.90                                             %
%                                                                   %
% Modifications:                                                    %
% 09.08.91 - BtG - updated to HOL2                                  %
% ================================================================= %
new_theory `correctness_EQ`;;

map new_parent
 [ `correctness_misc`
 ; `liveness`
 ];;

loadf `wordn`;;
load_library `integer`;;

map (load_theorem `correctness_misc`)
 [ `LET_THM`
 ; `Store14_root_1_lemma`
 ; `EQ_opcode_lemma`
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
 [ `EQ_trans`
 ; `cell_of`
 ; `mem_free_of`
 ; `mem_of`
 ; `free_of`
 ];;
map (load_theorem `mu-prog_EQ`)
 [ `EQ_state`
 ; `EQ_Next`
 ];;
map (load_definition `abstract_mem_type`)
 [ `M_CAR`
 ; `M_CDR`
 ];;
map (load_theorem `mem_abs`)
 [ `car_cdr_mem_abs_lemma`
 ; `M_Eq_unfold_lemma`
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
loadt `COND_CASES_THEN`;;
loadt `RATOR_RAND_CONV`;;		% for RHS_CONV %
% ================================================================= %
timer true;;

% ================================================================= %
% Discharge every assumption with "t" in it, and generalize it.     %
% ================================================================= %
let EQ_state' =
 GEN "t:^mtime" 
 (DISCH "mpc (t:^mtime) = #000101011"
  (DISCH "opcode_bits((memory:^m14_32_mvec) t(car_bits(memory t(c t))))
          = #000001110"
         EQ_state));;
let EQ_Next' =
 GEN "t:^mtime" 
 (DISCH "mpc (t:^mtime) = #000101011"
  (DISCH "opcode_bits((memory:^m14_32_mvec) t(car_bits(memory t(c t))))
          = #000001110"
         EQ_Next));;

% ================================================================= %
% Correctness goal for the EQ instruction.                          %
% ================================================================= %
let correctness_EQ = TAC_PROOF
(([
   % ----------------------------- (car s) or (cadr s) is a cons cell %
   "(is_atom(memory(TimeOf(is_major_state mpc)t)
                   (car_bits(memory(TimeOf(is_major_state mpc)t)
                            ((s:^w14_mvec)(TimeOf(is_major_state mpc)t)))))) \/
    (is_atom(memory(TimeOf(is_major_state mpc)t)
             (car_bits(memory(TimeOf(is_major_state mpc)t)
               (cdr_bits(memory(TimeOf(is_major_state mpc)t)
                     ((s:^w14_mvec)(TimeOf(is_major_state mpc)t))))))))"
 ; % ----------------------------- (cdr s) is a cons cell %
   "is_cons(memory(TimeOf(is_major_state mpc)t)
            (cdr_bits(memory(TimeOf(is_major_state mpc)t)
                     ((s:^w14_mvec)(TimeOf(is_major_state mpc)t)))))"
 ; % ----------------------------- s is a cons cell %
   "is_cons(memory(TimeOf(is_major_state mpc)t)
            ((s:^w14_mvec)(TimeOf(is_major_state mpc)t)))"
 ; % ----------------------------- the opcode is EQ %
   "atom_bits(memory(TimeOf(is_major_state mpc)t)
            (car_bits(memory(TimeOf(is_major_state mpc)t)
                      ((c:^w14_mvec)(TimeOf(is_major_state mpc)t))))) =
    #0000000000000000000000001110" 
 ; % ----------------------------- opcode is a number record %
   "is_number(memory(TimeOf(is_major_state mpc)t)
              (car_bits(memory(TimeOf(is_major_state mpc)t)
                        ((c:^w14_mvec)(TimeOf(is_major_state mpc)t)))))"
 ; % ----------------------------- c is itself a cons cell %
   "is_cons(memory(TimeOf(is_major_state mpc)t)
            ((c:^w14_mvec)(TimeOf(is_major_state mpc)t)))"
 ; "mpc(TimeOf(is_major_state mpc)t) = #000101011" 
 ; "Inf(is_major_state mpc)"
 ; "(!x:word14. garbage_bits(memory (TimeOf(is_major_state mpc)t) x) = #00)"
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
    EQ_trans ((s                  when (is_major_state mpc))t,
               (e                  when (is_major_state mpc))t,
               (c                  when (is_major_state mpc))t,
               (d                  when (is_major_state mpc))t,
               (free               when (is_major_state mpc))t,
               ((mem_abs o memory) when (is_major_state mpc))t)
 "),
 FIRST_ASSUM				% state_abs is top_of_cycle %
      (\th. (ASSUME_TAC o (porr[state_abs_thm])
			o (AP_TERM "state_abs")) th ? NO_TAC)
 THEN IMP_RES_TAC EQ_opcode_lemma 		% opcode_bits assumption %
 THEN port[when]
 THEN in_conv_tac BETA_CONV
 THEN port[o_THM]
					% generate req'd assumptions ... %
 THEN IMP_RES_n_THEN 3 ASSUME_TAC
                       well_formed_free_list_lemma
	    % only 3 of the 6 free cell inequalities are likely needed %
 THEN IMP_RES_n_THEN 2			% mem0 NIL_addr = ... %
      (\th. (free_in "NIL_addr" (concl th)) => ASSUME_TAC th | ALL_TAC)
      reserved_words_constraint
 THEN IMP_RES_n_THEN 2			% nonintersecting mem0 free [s;e;c] %
      (\th. ((free_in "s:^w14_mvec" (concl th))
          or (free_in "c:^w14_mvec" (concl th)))
             => ASSUME_TAC th
              | ALL_TAC)
      well_formed_free_list_nonintersection_lemma

 THEN port[EQ_trans]                    % unfold spec %
% ================================================================= %
			                % expand the M_* ops %

 THEN port[M_CAR; M_CDR]                % rewrite M_CAR/M_CDR s  %
 THEN IMP_RES_THEN port1 car_cdr_mem_abs_lemma
 THEN port[M_CDR]	                % rewrite M_CDR (cdr s), etc.  %
 THEN IMP_RES_THEN port1 car_cdr_mem_abs_lemma
					% rewrite the 1st M_Cons %
 THEN FIRST_ASSUM
       (\th. is_disj(concl th)
	=> (IMP_RES_THEN port1 (MATCH_MP ((DISCH_ALL
					   o (CONV_RULE(RHS_CONV SYM_CONV))
					   o UNDISCH_ALL
					   o (porr[DISJ_SYM]))
					  M_Eq_unfold_lemma) th))
	 | NO_TAC)
 THEN IMP_RES_n_THEN 3 port1 (hd(IMP_CANON M_Cons_unfold_1_thm))
					% unwind the cell1_mem_free let binding %
 THEN port[LET_THM]
 THEN BETA_TAC
 THEN prt[cell_of; free_of; mem_of; mem_free_of]
 					% unwind M_Cdr (c,mem1, ) %
 THEN IMP_RES_n_THEN 3
      ((IMP_RES_THEN (port1 o (MATCH_MP car_cdr_mem_abs_lemma) o SPEC_ALL))
       o snd
       o EQ_IMP_RULE
       o (AP_TERM "is_cons")
       o SPEC_ALL)
      (hd(IMP_CANON Store14_root_1_lemma))
					% introduce the two conditional theorems %
 THEN IMP_RES_THEN ((\th. ASSUME_TAC th
		          THEN UNDISCH_TAC (concl th))o UNDISCH) EQ_state'
 THEN IMP_RES_THEN ((\th. ASSUME_TAC th
		          THEN UNDISCH_TAC (concl th))o UNDISCH) EQ_Next'
 THEN COND_CASES_THEN			% split on the branch %
      (\th. SUBST_ALL_TAC th
            THEN ASSUME_TAC (SYM_RULE (rr[]th))
            THEN prt[COND_CLAUSES]
	    THEN STRIP_TAC THEN STRIP_TAC
	    THEN IMP_RES_n_THEN 2 port1 TimeOf_Next_lemma
	    THEN ABBREV_TAC "(TimeOf(is_major_state mpc)t)" "t':num"
	    THEN ABBREV_TAC "(memory:^m14_32_mvec) t'" "mem0:^mem14_32"
	    THEN prt[PAIR_EQ]
	    THEN part[]			% simplify _imp view %
	    THEN REPEAT CONJ_TAC
	    THEN (REFL_TAC
		  ORELSE (port[state_abs_thm] THEN REFL_TAC)
		  ORELSE ALL_TAC))
 );;

% ================================================================= %
save_thm(`correctness_EQ`,correctness_EQ);;

timer false;;
close_theory ();;
print_theory `-`;;


