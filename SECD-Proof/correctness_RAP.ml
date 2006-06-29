% SECD verification                                                 %
%                                                                   %
% FILE:         correctness_RAP.ml                                  %
%                                                                   %
% DESCRIPTION:  The correspondence between the specification for    % 
%               RAP instruction, and the computational effect of    %
%               the machine executing an RAP instruction.           %
%                                                                   %
% USES FILES:   correctness_misc.th, wordn & integer libraries      %
%               liveness - only to get at ancestor theories ...     %
%                                                                   %
% Brian Graham 29.11.90                                             %
%                                                                   %
% Modifications:                                                    %
% 08.08.91 - BtG - updated to HOL2                                  %
% ================================================================= %
new_theory `correctness_RAP`;;

map new_parent
 [ `correctness_misc`
 ; `liveness`
 ];;

loadf `wordn`;;
load_library `integer`;;

map (load_theorem `correctness_misc`)
 [ `LET_THM`
 ; `Store14_root_1_lemma`
 ; `Store14_root_2_lemma`
 ; `Store14_root_3_lemma`
 ; `Store14_car_cdr_2_lemma`
 ; `Store14_car_cdr_3_lemma`
 ; `Store14_caar_cdar_3_lemma`
 ; `RAP_opcode_lemma`
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
 ; `Store14_1_lemma`
 ];;
map (load_definition `top_SECD`)
 [ `RAP_trans`
 ; `cell_of`
 ; `mem_free_of`
 ; `mem_of`
 ; `free_of`
 ];;
map (load_theorem `mu-prog_RAP`)
 [ `RAP_state`
 ; `RAP_Next`
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
 ; `Rplaca_unfold_lemma`
 ];;
load_theorem `val_theorems` `AP_TERM_INV`;;
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
let RAP_state' =
 GEN "t:^mtime" 
 (DISCH "mpc (t:^mtime) = #000101011"
  (DISCH "opcode_bits((memory:^m14_32_mvec) t(car_bits(memory t(c t))))
          = #000000111"
         RAP_state));;
let RAP_Next' =
 GEN "t:^mtime" 
 (DISCH "mpc (t:^mtime) = #000101011"
  (DISCH "opcode_bits((memory:^m14_32_mvec) t(car_bits(memory t(c t))))
          = #000000111"
         RAP_Next));;

% ================================================================= %
% Specialize a theorem used late in the proof.                      %
% ================================================================= %
let Store14_1_lemma' =
 SPECL ["mem3:^mem14_32"
       ; "cdr_bits(mem3(car_bits(mem3((s:^w14_mvec) t'))))"
       ; "(s:^w14_mvec) t'"]
       (GENL ["memory:^mem14_32";"free:word14"]
             Store14_1_lemma);;

% ================================================================= %
let rplaca_cons_lemma = prove
("!a mem. (car_bits (mem a) = NIL_addr) ==>
       (!v. is_cons(mem v) ==>
       (!p. is_cons(Store14 a (bus32_cons_append #00 RT_CONS p (cdr_bits (mem a)))
                            mem v)))",
 REPEAT STRIP_TAC
 THEN port[definition `rt_SYS` `Store14`]
 THEN BETA_TAC
 THEN COND_CASES_TAC
 THENL
 [ port[definition `dp_types` `is_cons`]
   THEN port[theorem `dp_types` `bus32_cons_fields_lemma_1`]
   THEN REFL_TAC
 ; art[]
 ]);;

% ================================================================= %
let NIL_nonintersecting = prove
("!mem f. (mem NIL_addr = bus32_symb_append #0000000000000000000000000000) ==>
   nonintersecting mem f NIL_addr",
 REPEAT GEN_TAC
 THEN STRIP_TAC
 THEN port[definition `constraints` `nonintersecting`]
 THEN LIST_INDUCT_TAC
 THEN port[definition `constraints` `path`]
 THENL
 [ REPEAT GEN_TAC THEN STRIP_TAC THEN STRIP_TAC THEN art[]
   THEN SYM_TAC
   THEN STRIP_TAC
   THEN RES_TAC
 ; REPEAT GEN_TAC
   THEN IMP_RES_THEN (ASSUME_TAC o (rr[]) o (SPEC "NIL_addr"))
                     (theorem `constraints` `NIL_not_cons`)
   THEN art[]
   THEN STRIP_TAC
   THEN STRIP_TAC
   THEN SYM_TAC
   THEN STRIP_TAC
   THEN RES_TAC 
 ]);;

% ================================================================= %
let symb_not_cons = prove
("~(is_cons (bus32_symb_append #0000000000000000000000000000))",
 port[definition `dp_types` `is_cons`]
 THEN port[theorem `dp_types` `bus32_symb_fields_lemma`]
 THEN rt[SYM_RULE (theorem `dp_types` `rec_types_DISTINCT`)]
);;

% ================================================================= %
let cons_symb_distinct = prove
("!(mem:^mem14_32) (x:word14) y. ~(is_cons (mem x)) ==>
           (is_cons (mem y)) ==>
	   ~(x = y)",
 REPEAT GEN_TAC
 THEN STRIP_TAC
 THEN STRIP_TAC
 THEN DISCH_THEN SUBST_ALL_TAC
 THEN RES_TAC
 );;

timer false;;
% ================================================================= %
let mem0 = "(memory:^m14_32_mvec) t'";;

let cell1 = "(bus32_cons_append 
            #00 
            RT_CONS
            (cdr_bits(^mem0((c:^w14_mvec) t')))
            (d t'))";;

let mem1 = "Store14  (free (t':num)) ^cell1 ^mem0";;

let cell2 = "bus32_cons_append 
              #00 
              RT_CONS
              (cdr_bits(^mem1((e:^w14_mvec) t')))
              (free t')";;

let mem2 =  "Store14 (cdr_bits(^mem0((free:^w14_mvec) t')))
             ^cell2 ^mem1";;

let cell3 = "bus32_cons_append 
             #00 
             RT_CONS
             (cdr_bits(^mem2(cdr_bits(^mem2((s:^w14_mvec) t')))))
             (cdr_bits(^mem0((free:^w14_mvec) t')))";;

let mem3 =  "Store14
            (cdr_bits(^mem1(cdr_bits(^mem0((free:^w14_mvec) t')))))
            ^cell3 ^mem2";;

let cell4 = "bus32_cons_append 
     #00 
     RT_CONS
     (car_bits(^mem3(cdr_bits(^mem3((s:^w14_mvec) t')))))
     (cdr_bits(^mem3(cdr_bits(^mem3(car_bits(^mem3(s t')))))))";;

let mem4 = "Store14
    (cdr_bits(^mem3(car_bits(^mem3((s:^w14_mvec) t')))))
    ^cell4 ^mem3";;

timer true;;
% ================================================================= %
% Correctness goal for the RAP instruction.                         %
% ================================================================= %
let correctness_RAP = TAC_PROOF
(([
   % ----------------------------- e is identical to closure on stack %
   "(e:^w14_mvec)(TimeOf(is_major_state mpc)t) =
    cdr_bits (memory(TimeOf(is_major_state mpc)t)
    (car_bits (memory(TimeOf(is_major_state mpc)t)
     ((s:^w14_mvec)(TimeOf(is_major_state mpc)t)))))"
 ; % ----------------------------- (cdr s) is a cons cell %
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
 ; % ----------------------------- (car e) is NIL %
   "car_bits(memory(TimeOf(is_major_state mpc)t)
                   ((e:^w14_mvec)(TimeOf(is_major_state mpc)t))) =
    NIL_addr"
 ; % ----------------------------- e is a cons cell %
   "is_cons(memory(TimeOf(is_major_state mpc)t)
            ((e:^w14_mvec)(TimeOf(is_major_state mpc)t)))"
 ; % ----------------------------- the opcode is RAP %
   "atom_bits(memory(TimeOf(is_major_state mpc)t)
            (car_bits(memory(TimeOf(is_major_state mpc)t)
                      ((c:^w14_mvec)(TimeOf(is_major_state mpc)t))))) =
    #0000000000000000000000000111" 
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
    RAP_trans ((s                  when (is_major_state mpc))t,
               (e                  when (is_major_state mpc))t,
               (c                  when (is_major_state mpc))t,
               (d                  when (is_major_state mpc))t,
               (free               when (is_major_state mpc))t,
               ((mem_abs o memory) when (is_major_state mpc))t)
 "),
 FIRST_ASSUM (\th. ((is_eq(concl th)) & (type_of(fst(dest_eq(concl th)))=":word14"))
 => 
 (IMP_RES_TAC
  o (rr[o_THM])
  o (AP_TERM "is_cons o ((memory:^m14_32_mvec)(TimeOf(is_major_state mpc)t))")) th
  THEN FIRST_ASSUM
  (\th1. (free_in "NIL_addr" (concl th1) & (free_in "e:^w14_mvec" (concl th1)))
         => ASSUME_TAC (SUBS [th]th1) | NO_TAC)
 | NO_TAC)
 THEN FIRST_ASSUM				% state_abs is top_of_cycle %
      (\th. (ASSUME_TAC o (porr[state_abs_thm])
			o (AP_TERM "state_abs")) th ? NO_TAC)
 THEN IMP_RES_TAC RAP_opcode_lemma 		% opcode_bits assumption %
 THEN port[when]
 THEN in_conv_tac BETA_CONV
					% Next assumption %
 THEN IMP_RES_THEN (ASSUME_TAC o UNDISCH) RAP_Next'
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
      (\th. ((free_in "s:^w14_mvec" (concl th))
          or (free_in "e:^w14_mvec" (concl th))
          or (free_in "c:^w14_mvec" (concl th)))
             => ASSUME_TAC th
              | ALL_TAC)
      well_formed_free_list_nonintersection_lemma

 THEN port[RAP_trans]                    % unfold spec %
% ================================================================= %
			                % expand the M_* ops %

 THEN port[M_CDR]                       % rewrite M_CDR c  %
 THEN IMP_RES_THEN port1 car_cdr_mem_abs_lemma
					% rewrite the 1st M_Cons %
 THEN port[M_Cons_tr]
 THEN IMP_RES_n_THEN 3 port1 (hd(IMP_CANON M_Cons_unfold_1_thm))
					% unwind the cell1_mem_free let binding %
 THEN port[LET_THM]
 THEN in1_conv_tac BETA_CONV
 THEN prt[cell_of; mem_free_of]

 THEN port[M_CDR]			% unwind M_CDR (e,mem1, ) %
 THEN IMP_RES_n_THEN 3
      ((IMP_RES_THEN (port1 o (MATCH_MP car_cdr_mem_abs_lemma) o SPEC_ALL))
       o snd
       o EQ_IMP_RULE
       o (AP_TERM "is_cons")
       o SPEC_ALL)
      (hd(IMP_CANON Store14_root_1_lemma))
					% rewrite the 2nd M_Cons %
 THEN port[M_Cons_tr]
 THEN IMP_RES_n_THEN 3 port1 (hd(IMP_CANON M_Cons_unfold_2_thm))
					% unwind the cell2_mem_free let binding %
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
 THEN prt[mem_free_of]

 THEN port[M_CAR;M_CDR]			% unwind M_CAR,M_CDR (s,mem3, ) %
 THEN IMP_RES_n_THEN 6
      ((IMP_RES_THEN (port1 o (MATCH_MP car_cdr_mem_abs_lemma) o SPEC_ALL))
       o snd
       o EQ_IMP_RULE
       o (AP_TERM "is_cons")
       o SPEC_ALL)
      (hd(IMP_CANON Store14_root_3_lemma))
 THEN IMP_RES_n_THEN 7			% unwind M_Cdr (car(mem3 s),mem3, ) %
      ((IMP_RES_THEN (port1 o (MATCH_MP car_cdr_mem_abs_lemma) o SPEC_ALL))
       o snd
       o EQ_IMP_RULE
       o (AP_TERM "is_cons")
       o SPEC_ALL)
      (hd(tl(IMP_CANON Store14_car_cdr_3_lemma)))
 THEN port[M_CAR]			% unwind M_CAR (cdr(mem3 s),mem3, ) %
 THEN IMP_RES_n_THEN 7
      ((IMP_RES_THEN (port1 o (MATCH_MP car_cdr_mem_abs_lemma) o SPEC_ALL))
       o snd
       o EQ_IMP_RULE
       o (AP_TERM "is_cons")
       o SPEC_ALL)
      (hd(IMP_CANON Store14_car_cdr_3_lemma))
					% rewrite the M_Rplaca %
 THEN IMP_RES_n_THEN 8
      ((IMP_RES_THEN (port1 o (MATCH_MP Rplaca_unfold_lemma) o SPEC_ALL))
       o snd
       o EQ_IMP_RULE
       o (AP_TERM "is_cons")
       o SPEC_ALL)
      (hd(IMP_CANON Store14_caar_cdar_3_lemma))

 THEN port[LET_THM]			% unwind e_mem_free let binding %
 THEN in1_conv_tac BETA_CONV
 THEN prt[cell_of; free_of; mem_of; mem_free_of]

 THEN prt[PAIR_EQ]			% split into 7 subgoals %
 THEN REPEAT CONJ_TAC
					% simplify _imp view %
 THEN IMP_RES_THEN (SUBST1_TAC o UNDISCH) RAP_state'

 THEN
 (REFL_TAC
  ORELSE (port[state_abs_thm] THEN REFL_TAC)
  ORELSE
  (port[M_CAR]
   THEN IMP_RES_THEN (ASSUME_TAC o (SPEC "free:^w14_mvec"))
                     (SPECL ["(memory:^m14_32_mvec) t'";"(free:^w14_mvec) t'"]
			    NIL_nonintersecting)
   THEN					% is_cons(mem3 (s t')) %
   (\th. (ASSUME_TAC o (SPECL [cell1; cell3; cell2])
	             o GEN_ALL o UNDISCH o snd o EQ_IMP_RULE
		     o (AP_TERM "is_cons") o UNDISCH
		     o (SPEC "(s:^w14_mvec) t'")) th
					% ~(is_cons(mem3(NIL_addr))) %
              THEN (ASSUME_TAC o (SPECL [cell1; cell3; cell2])
			       o GEN_ALL o (arr[symb_not_cons])
			       o (AP_TERM "is_cons") o UNDISCH
			       o (SPEC "NIL_addr")) th
	)
   (((GEN "v:word14") o UNDISCH o UNDISCH o UNDISCH o UNDISCH o UNDISCH
     o (SPECL ["(memory:^m14_32_mvec) t'"; "(free:^w14_mvec) t'"])
     o (GENL ["mem:^mem14_32" ;"free:word14"]) o hd o IMP_CANON)
   Store14_root_3_lemma)
     					% car_bits(mem3(cdar(s t)))=NIL_addr %
   THEN (\th. ASSUME_TAC (SPECL [cell1; cell3; cell2] (GEN_ALL th))
     					% is_cons (mem3 )==>is_cons(mem3? ?) %
	      THEN (ASSUME_TAC
		    o (SPECL [cell1; cell3; cell2])
		    o GEN_ALL 
		    o (MATCH_MP rplaca_cons_lemma)
		    o SPEC_ALL) th)
   (((rr[ASSUME "car_bits(memory t'(cdr_bits
                        (memory t'(car_bits(memory t'((s:^w14_mvec) t')))))) =
                       NIL_addr"])
    
     o (AP_TERM "car_bits")
     o UNDISCH o UNDISCH o UNDISCH
     o (SPEC "(s:^w14_mvec) t'") o (GEN "v:word14")
     o UNDISCH o UNDISCH o UNDISCH o UNDISCH o UNDISCH
     o (SPECL ["(memory:^m14_32_mvec) t'"; "(free:^w14_mvec) t'"])
     o (GENL ["mem:^mem14_32" ;"free:word14"]) o hd o IMP_CANON)
     Store14_caar_cdar_3_lemma)

     					% is_cons(mem3(car(s t'))) %
   THEN (ASSUME_TAC o (SPECL [cell1; cell3; cell2]) o GEN_ALL o UNDISCH
	o snd o EQ_IMP_RULE o (AP_TERM "is_cons")
	o UNDISCH o UNDISCH 
	o (SPEC "(s:^w14_mvec) t'") o (GEN "v:word14")
	o UNDISCH o UNDISCH o UNDISCH o UNDISCH o UNDISCH
	o (SPECL ["(memory:^m14_32_mvec) t'"; "(free:^w14_mvec) t'"])
        o (GENL ["mem:^mem14_32" ;"free:word14"])
        o hd o tl o IMP_CANON)
	Store14_car_cdr_3_lemma

   THEN ABBREV_TAC "(memory:^m14_32_mvec) t'" "mem0:^mem14_32"
   THEN ABBREV_TAC
   "Store14  (free (t':num))
             (bus32_cons_append  #00  RT_CONS
               (cdr_bits(mem0(c t'))) (d t'))
             mem0"
   "mem1:^mem14_32"
   THEN ABBREV_TAC
        "Store14 (cdr_bits(mem0((free:^w14_mvec) t')))
               (bus32_cons_append  #00  RT_CONS
                 (cdr_bits(mem1(e t'))) (free t'))
               mem1"
        "mem2:^mem14_32"
   THEN ABBREV_TAC
       "Store14
              (cdr_bits(mem1(cdr_bits(mem0((free:^w14_mvec) t')))))
              (bus32_cons_append #00  RT_CONS
                (cdr_bits(mem2(cdr_bits(mem2(s t')))))
                (cdr_bits(mem0(free t'))))
              mem2"
        "mem3:^mem14_32"

   THEN POP_ASSUM (\th10.
   POP_ASSUM \th9.
   POP_ASSUM \th8.
   POP_ASSUM \th7.			% NOTE: th6 not here!! %
   POP_ASSUM \th5.
   POP_ASSUM \th4.
   POP_ASSUM \th3.
   POP_ASSUM \th2.
   POP_ASSUM \th1.
   port1 (GEN_ALL (MATCH_MP car_cdr_mem_abs_lemma	% rewrite 1st M_Car ... %
	  		         (SPEC_ALL(MATCH_MP th4 th1))))
   THEN (let th6 = 			% ~(s t' = cdar(mem3(s t'))) %
        (MATCH_MP AP_TERM_INV
         (MATCH_MP AP_TERM_INV
  	  (MATCH_MP AP_TERM_INV
	   (MATCH_MP AP_TERM_INV
		     (porr[ SYM_RULE
			  (EQF_INTRO
			   (SUBS [SYM_RULE (AP_TERM "mem3:^mem14_32" th3)] th2))
			  ; SYM_RULE (EQT_INTRO th5)]
  			  (CONJUNCT1 BOOL_EQ_DISTINCT))))))
        in
        port1 (GEN_ALL (MATCH_MP car_cdr_mem_abs_lemma	% rewrite 2nd M_Car ... %
	  		         (SPEC_ALL
                                  (MATCH_MP th4
                                            (porr [(MATCH_MP Store14_1_lemma'
                                                             (SYM_RULE th6))]
                                                  th5)))))))
   THEN REFL_TAC
   )
  )
 );;
% ================================================================= %
save_thm(`correctness_RAP`,correctness_RAP);;

timer false;;
close_theory ();;
print_theory `-`;;

