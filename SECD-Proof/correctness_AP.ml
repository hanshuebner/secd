% SECD verification                                                 %
%                                                                   %
% FILE:         correctness_AP.ml                                   %
%                                                                   %
% DESCRIPTION:  The correspondence between the specification for    % 
%               AP instruction, and the computational effect of     %
%               the machine executing an AP instruction.            %
%                                                                   %
% USES FILES:   correctness_misc.th, wordn & integer libraries      %
%               liveness - only to get at ancestor theories ...     %
%                                                                   %
% Brian Graham 29.11.90                                             %
%                                                                   %
% Modifications:                                                    %
% 08.08.91 - BtG - updated to HOL2                                  %
% ================================================================= %
new_theory `correctness_AP`;;

map new_parent
 [ `correctness_misc`
 ; `liveness`
 ];;

loadf `wordn`;;
load_library `integer`;;

map (load_theorem `correctness_misc`)
 [ `LET_THM`
 ; `Store14_root_2_lemma`
 ; `Store14_root_3_lemma`
 ; `Store14_root_4_lemma`
 ; `Store14_car_cdr_2_lemma`
 ; `Store14_car_cdr_3_lemma`
 ; `Store14_car_cdr_4_lemma`
 ; `AP_opcode_lemma`
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
 [ `AP_trans`
 ; `cell_of`
 ; `mem_free_of`
 ; `mem_of`
 ; `free_of`
 ];;
map (load_theorem `mu-prog_AP`)
 [ `AP_state`
 ; `AP_Next`
 ];;
map (load_definition `abstract_mem_type`)
 [ `M_CAR`
 ; `M_CDR`
 ; `M_Cons_tr`
 ];;
map (load_theorem `mem_abs`)
 [ `car_cdr_mem_abs_lemma`
 ; `M_Cons_unfold_1_thm`
 ; `M_Cons_unfold_2_thm`
 ; `M_Cons_unfold_3_thm`
 ; `M_Cons_unfold_4_thm`
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
let AP_state' =
 GEN "t:^mtime" 
 (DISCH "mpc (t:^mtime) = #000101011"
  (DISCH "opcode_bits((memory:^m14_32_mvec) t(car_bits(memory t(c t))))
          = #000000100"
         AP_state));;
let AP_Next' =
 GEN "t:^mtime" 
 (DISCH "mpc (t:^mtime) = #000101011"
  (DISCH "opcode_bits((memory:^m14_32_mvec) t(car_bits(memory t(c t))))
          = #000000100"
         AP_Next));;

% ================================================================= %
% Correctness goal for the AP instruction.                          %
% ================================================================= %
let correctness_AP = TAC_PROOF
(([ % ----------------------------- (cdr s) is a cons cell %
   "is_cons(memory(TimeOf(is_major_state mpc)t)
            (cdr_bits(memory(TimeOf(is_major_state mpc)t)
                     ((s:^w14_mvec)(TimeOf(is_major_state mpc)t)))))"
 ; % ----------------------------- (car s) is a cons cell %
   "is_cons(memory(TimeOf(is_major_state mpc)t)
            (car_bits(memory(TimeOf(is_major_state mpc)t)
                     ((s:^w14_mvec)(TimeOf(is_major_state mpc)t)))))"
 ; % ----------------------------- s is a cons cell %
   "is_cons(memory(TimeOf(is_major_state mpc)t)
            ((s:^w14_mvec)(TimeOf(is_major_state mpc)t)))"
 ; % ----------------------------- the opcode is AP %
   "atom_bits(memory(TimeOf(is_major_state mpc)t)
            (car_bits(memory(TimeOf(is_major_state mpc)t)
                      ((c:^w14_mvec)(TimeOf(is_major_state mpc)t))))) =
    #0000000000000000000000000100" 
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
    AP_trans ((s                  when (is_major_state mpc))t,
              (e                  when (is_major_state mpc))t,
              (c                  when (is_major_state mpc))t,
              (d                  when (is_major_state mpc))t,
              (free               when (is_major_state mpc))t,
              ((mem_abs o memory) when (is_major_state mpc))t)
 "),
 FIRST_ASSUM				% state_abs is top_of_cycle %
      (\th. (ASSUME_TAC o (porr[state_abs_thm])
			o (AP_TERM "state_abs")) th ? NO_TAC)
 THEN IMP_RES_TAC AP_opcode_lemma 		% opcode_bits assumption %
 THEN port[when]
 THEN in_conv_tac BETA_CONV
					% Next assumption %
 THEN IMP_RES_THEN (ASSUME_TAC o UNDISCH) AP_Next'
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
 THEN IMP_RES_n_THEN 2			% nonintersecting mem0 free s %
      (\th. (free_in "s:^w14_mvec" (concl th)) => ASSUME_TAC th | ALL_TAC)
      well_formed_free_list_nonintersection_lemma

 THEN port[AP_trans]                    % unfold spec %
% ================================================================= %
 THEN port[M_CDR]                       % expand the M_* ops %

			                % rewrite M_Cdr c  %
 THEN IMP_RES_THEN port1 car_cdr_mem_abs_lemma
					% rewrite the 1st 2 M_Cons'es %
 THEN port[M_Cons_tr]
 THEN IMP_RES_n_THEN 3 port1 (hd(IMP_CANON M_Cons_unfold_1_thm))
 THEN IMP_RES_n_THEN 3 port1 (hd(IMP_CANON M_Cons_unfold_2_thm))
					% unwind the cell_mem_free let binding %
 THEN port[LET_THM]
 THEN in1_conv_tac BETA_CONV
 THEN prt[cell_of; mem_free_of]

 THEN port[M_CDR]			% unwind M_CDR (s,mem2, ) %
 THEN IMP_RES_n_THEN 4
      ((IMP_RES_THEN (port1 o (MATCH_MP car_cdr_mem_abs_lemma) o SPEC_ALL))
       o snd
       o EQ_IMP_RULE
       o (AP_TERM "is_cons")
       o SPEC_ALL)
      (hd(IMP_CANON Store14_root_2_lemma))
 THEN port[M_CDR]			% unwind M_CDR (cdr(mem2 s),mem2, ) %
 THEN IMP_RES_n_THEN 5
      ((IMP_RES_THEN (port1 o (MATCH_MP car_cdr_mem_abs_lemma) o SPEC_ALL))
       o snd
       o EQ_IMP_RULE
       o (AP_TERM "is_cons")
       o SPEC_ALL)
      (hd(IMP_CANON Store14_car_cdr_2_lemma))
					% rewrite the 3rd M_Cons %
 THEN port[M_Cons_tr]
 THEN IMP_RES_n_THEN 3 port1 (hd(IMP_CANON M_Cons_unfold_3_thm))
 THEN port[LET_THM]			% unwind d_mem_free let binding %
 THEN in1_conv_tac BETA_CONV
 THEN prt[cell_of; mem_free_of]

 THEN port[M_CAR;M_CDR]			% unwind M_CAR,M_CDR (s,mem3, ) %
 THEN IMP_RES_n_THEN 6
      ((IMP_RES_THEN (port1 o (MATCH_MP car_cdr_mem_abs_lemma) o SPEC_ALL))
       o snd
       o EQ_IMP_RULE
       o (AP_TERM "is_cons")
       o SPEC_ALL)
      (hd(IMP_CANON Store14_root_3_lemma))
 THEN IMP_RES_n_THEN 7			% unwind M_CAR (cdr(mem3 s),mem3, ) %
      ((IMP_RES_THEN (port1 o (MATCH_MP car_cdr_mem_abs_lemma) o SPEC_ALL))
       o snd
       o EQ_IMP_RULE
       o (AP_TERM "is_cons")
       o SPEC_ALL)
      (hd(IMP_CANON Store14_car_cdr_3_lemma))
 THEN port[M_CDR]			% unwind M_CDR (car(mem3 s),mem3, ) %
 THEN IMP_RES_n_THEN 7
      ((IMP_RES_THEN (port1 o (MATCH_MP car_cdr_mem_abs_lemma) o SPEC_ALL))
       o snd
       o EQ_IMP_RULE
       o (AP_TERM "is_cons")
       o SPEC_ALL)
      (hd(tl(IMP_CANON Store14_car_cdr_3_lemma)))
					% rewrite the 4th M_Cons %
 THEN IMP_RES_n_THEN 3 port1 (hd(IMP_CANON M_Cons_unfold_4_thm))
 THEN port[LET_THM]			% unwind e_mem_free let binding %
 THEN in1_conv_tac BETA_CONV
 THEN prt[cell_of; free_of; mem_of; mem_free_of]

 THEN prt[PAIR_EQ]			% split into 7 subgoals %
 THEN REPEAT CONJ_TAC
					% simplify _imp view %
 THEN IMP_RES_THEN (SUBST1_TAC o UNDISCH) AP_state'
 THENL
 [ REFL_TAC				% s % 
 ; REFL_TAC				% e %
 ; port[M_CAR]				% c %
 THEN IMP_RES_n_THEN 9			% unwind M_CAR (s,mem4, ) %
      ((IMP_RES_THEN (port1 o (MATCH_MP car_cdr_mem_abs_lemma) o SPEC_ALL))
       o snd
       o EQ_IMP_RULE
       o (AP_TERM "is_cons")
       o SPEC_ALL)
      (hd(IMP_CANON Store14_root_4_lemma))
 THEN IMP_RES_n_THEN 10			% unwind M_CAR (car(mem4 s),mem4, ) %
      ((IMP_RES_THEN (port1 o (MATCH_MP car_cdr_mem_abs_lemma) o SPEC_ALL))
       o snd
       o EQ_IMP_RULE
       o (AP_TERM "is_cons")
       o SPEC_ALL)
      (hd(tl(IMP_CANON Store14_car_cdr_4_lemma)))
 THEN (REFL_TAC ORELSE ALL_TAC)
 ; REFL_TAC				% d %
 ; REFL_TAC 				% free %
 ; REFL_TAC 				% memory %
 ; port[state_abs_thm]			% state %
   THEN REFL_TAC
 ]
 );;

% ================================================================= %
%< documentation: aids for interactive proof discovery
let cell1 = "(bus32_cons_append 
            #00 
            RT_CONS
            (cdr_bits(mem0((c:^w14_mvec) t')))
            (d t'))"
and cell2 = "(bus32_cons_append #00 RT_CONS((e:^w14_mvec) t')(free t'))";;

 THEN ABBREV_TAC "t'+48" "t'':num"
 THEN ABBREV_TAC "(memory:^m14_32_mvec) t'" "mem0:^mem14_32"
 THEN ABBREV_TAC
 "Store14  (free (t':num))
           (bus32_cons_append 
            #00 
            RT_CONS
            (cdr_bits(mem0(c t')))
            (d t'))
           mem0"
 "mem1:^mem14_32"
 THEN ABBREV_TAC
      "Store14 (cdr_bits(mem0((free:^w14_mvec) t')))
               (bus32_cons_append #00 RT_CONS(e t')(free t'))
               mem1"
      "mem2:^mem14_32"
>%
% ================================================================= %
save_thm(`correctness_AP`,correctness_AP);;

timer false;;
close_theory ();;
print_theory `-`;;
