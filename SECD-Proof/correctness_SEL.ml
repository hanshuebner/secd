% SECD verification                                                 %
%                                                                   %
% FILE:         correctness_SEL.ml                                  %
%                                                                   %
% DESCRIPTION:  The correspondence between the specification for    % 
%               LDC instruction, and the computational effect of    %
%               the machine executing an LDC instruction.           %
%                                                                   %
% USES FILES:   correctness_misc.th, wordn & integer libraries      %
%               liveness - only to get at ancestor theories ...     %
%                                                                   %
% Brian Graham 02.01.91                                             %
%                                                                   %
% Modifications:                                                    %
% 09.08.91 - BtG - updated to HOL2                                  %
% ================================================================= %
new_theory `correctness_SEL`;;

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
 ; `SEL_opcode_lemma`
 ];;

map (load_definition `when`)
 [ `when`
 ];;
map (load_theorem `when`)
 [ `TimeOf_Next_lemma`
 ];;
map (load_definition `val_defs`)
[ `bv`
; `val`
; `Val`
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
 [ `SEL_trans`
 ; `cell_of`
 ; `mem_free_of`
 ; `mem_of`
 ; `free_of`
 ];;
map (load_theorem `mu-prog_SEL`)
 [ `SEL_state`
 ; `SEL_Next`
 ];;
map (load_definition `abstract_mem_type`)
 [ `M_CAR`
 ; `M_CDR`
 ; `M_Cons_tr`
 ; `M_is_T`
 ; `T_atom`
 ];;
load_theorem `abstract_mem_type` `Symb_11`;;
map (load_theorem `mem_abs`)
 [ `car_cdr_mem_abs_lemma`
 ; `M_Cons_unfold_1_thm`
 ; `atom_symbol_mem_abs_lemma`
 ];;

map (load_definition `dp_types`)
[ `is_cons`
; `is_symbol`
];;
map (load_theorem `dp_types`)
 [ `rec_types_DISTINCT`
 ; `bus32_symb_fields_lemma`
 ; `bus32_cons_fields_lemma_1`
 ; `atom_rec_equivalence`
 ; `Bits28_Word28`
 ];;
load_definition `rt_SYS` `Store14`;;

map (load_theorem `val_theorems`)
[ `Val_Bits28_11`
; `val_0_F_bus`
; `bv_thm`
; `val_0_lemma`
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
loadt `COND_CASES_THEN`;;

% ================================================================= %
timer true;;

% ================================================================= %
% Discharge every assumption with "t" in it, and generalize it.     %
% ================================================================= %
let SEL_state' =
 GEN "t:^mtime" 
 (DISCH "mpc (t:^mtime) = #000101011"
  (DISCH "opcode_bits((memory:^m14_32_mvec) t(car_bits(memory t(c t))))
          = #000001000"
         SEL_state));;
let SEL_Next' =
 GEN "t:^mtime" 
 (DISCH "mpc (t:^mtime) = #000101011"
  (DISCH "opcode_bits((memory:^m14_32_mvec) t(car_bits(memory t(c t))))
          = #000001000"
         SEL_Next));;

% ================================================================= %
% ================================================================= %
let garb_bits_untouched_lemma = prove
("!mem.
  (!x. garbage_bits(mem x) = #00) ==>
  (!x y a b. garbage_bits(Store14 y (bus32_cons_append #00 RT_CONS a b)mem x) =
             #00)",
 GEN_TAC
 THEN STRIP_TAC
 THEN REPEAT GEN_TAC
 THEN port[Store14]
 THEN BETA_TAC
 THEN COND_CASES_TAC
 THENL
 [ port[bus32_cons_fields_lemma_1]
   THEN REFL_TAC
 ; art[]
 ]);;

% ================================================================= %
% ================================================================= %
let conditional_atom_bits_11 = prove
("(!x:word14. garbage_bits(mem x) = #00) ==>
   !y z:word14. (is_symbol (mem y)) ==>
                (is_symbol (mem z)) ==>
                ((atom_bits (mem y) = atom_bits (mem z)) = (mem y = mem z))",
 STRIP_TAC THEN REPEAT GEN_TAC
 THEN port[is_symbol]
 THEN REPEAT STRIP_TAC
 THEN port[SYM_RULE(SPECL ["(mem:^mem14_32) y"; "(mem:^mem14_32) z"]
                          atom_rec_equivalence)]
 THEN art[]
 );;

% ================================================================= %
% ================================================================= %
let T_atom_lemma = prove
("Val(Bits28 #0000000000000000000000000001) = 1",
 in1_conv_tac wordn_CONV
 THEN port[Bits28_Word28]
 THEN port[Val]
 THEN prt[val_0_F_bus]
 THEN prt[val; bv_thm; ADD_CLAUSES]
 THEN REFL_TAC
 );;

% ================================================================= %
let STRIP_UNDISCH th =
(DISCH_ALL o (arr[])
	   o (C(itlist ADD_ASSUM) th)
	   o conjuncts 
	   o fst
	   o dest_imp
	   o concl) th;;
% ================================================================= %
let t' = "(TimeOf(is_major_state mpc)t)";;
let mem0 = "(memory:^m14_32_mvec) ^t'";;

% ================================================================= %
% Correctness goal for the SEL instruction.                         %
% ================================================================= %
let correctness_SEL = TAC_PROOF
(([
   % ----------------------------- (cddr c) is a cons cell %
   "is_cons(memory(TimeOf(is_major_state mpc)t)
            (cdr_bits(memory(TimeOf(is_major_state mpc)t)
             (cdr_bits(memory(TimeOf(is_major_state mpc)t)
                     ((c:^w14_mvec)(TimeOf(is_major_state mpc)t)))))))"
 ; % ----------------------------- (cdr c) is a cons cell %
   "is_cons(memory(TimeOf(is_major_state mpc)t)
            (cdr_bits(memory(TimeOf(is_major_state mpc)t)
                     ((c:^w14_mvec)(TimeOf(is_major_state mpc)t)))))"
 ; % ----------------------------- (car s) is a symbol cell %
   "is_symbol(memory(TimeOf(is_major_state mpc)t)
            (car_bits(memory(TimeOf(is_major_state mpc)t)
                     ((s:^w14_mvec)(TimeOf(is_major_state mpc)t)))))"
 ; % ----------------------------- s is a cons cell %
   "is_cons(memory(TimeOf(is_major_state mpc)t)
            ((s:^w14_mvec)(TimeOf(is_major_state mpc)t)))"
 ; % ----------------------------- the opcode is SEL %
   "atom_bits(memory(TimeOf(is_major_state mpc)t)
            (car_bits(memory(TimeOf(is_major_state mpc)t)
                      ((c:^w14_mvec)(TimeOf(is_major_state mpc)t))))) =
    #0000000000000000000000001000" 
 ; % ----------------------------- opcode is a number record %
   "is_number(memory(TimeOf(is_major_state mpc)t)
              (car_bits(memory(TimeOf(is_major_state mpc)t)
                        ((c:^w14_mvec)(TimeOf(is_major_state mpc)t)))))"
 ; % ----------------------------- c is itself a cons cell %
   "is_cons(memory(TimeOf(is_major_state mpc)t)
            ((c:^w14_mvec)(TimeOf(is_major_state mpc)t)))"
 ; "mpc(TimeOf(is_major_state mpc)t) = #000101011" 
 ; "(!x:word14. garbage_bits(memory (TimeOf(is_major_state mpc)t) x) = #00)"
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
    SEL_trans ((s                  when (is_major_state mpc))t,
               (e                  when (is_major_state mpc))t,
               (c                  when (is_major_state mpc))t,
               (d                  when (is_major_state mpc))t,
               (free               when (is_major_state mpc))t,
               ((mem_abs o memory) when (is_major_state mpc))t)
 "),
 FIRST_ASSUM				% state_abs is top_of_cycle %
      (\th. (ASSUME_TAC o (porr[state_abs_thm])
			o (AP_TERM "state_abs")) th ? NO_TAC)
 THEN IMP_RES_TAC SEL_opcode_lemma 		% opcode_bits assumption %
 THEN port[when]
 THEN in_conv_tac BETA_CONV
 THEN port[o_THM]
					% generate req'd assumptions ... %
 THEN IMP_RES_n_THEN 3
 (\th. ASSUME_TAC th			% th = is_cons(mem0 (free t)) %
       THEN IMP_RES_n_THEN 2		% th1 = mem0 NIL/T_addr = ... %
      (\th1. (free_in "NIL_addr" (concl th1))
            => ASSUME_TAC th1		% mem0 NIL_addr = ... %
	     | (free_in "T_addr" (concl th1))
            => ASSUME_TAC th1		% mem0 T_addr = ... %
               THEN ASSUME_TAC		% ~(free t = T_addr) %
                    (MATCH_MP AP_TERM_INV
                     (MATCH_MP AP_TERM_INV
                      (SUBS[ SYM
                             (prr [ SYM_RULE is_cons ]
                              (prr[ is_cons
                                  ; bus32_symb_fields_lemma
		                  ; SYM_RULE rec_types_DISTINCT ]
                               (AP_TERM "is_cons" th1)))
                           ; SYM_RULE (EQT_INTRO th)
                           ]
                           (CONJUNCT1 BOOL_EQ_DISTINCT))))
             | ALL_TAC)
      reserved_words_constraint)
      ((DISCH_ALL			% ... ==> is_cons(mem0 free) %
	o GEN_ALL
	o (DISCH "(state_abs(mpc (t:num)) = top_of_cycle)")
	o CONJUNCT1
	o UNDISCH
	o SPEC_ALL
	o UNDISCH
	o UNDISCH) (STRIP_UNDISCH well_formed_free_list_lemma))

 THEN IMP_RES_n_THEN 2			% nonintersecting mem0 free [s;c] %
      (\th. ((free_in "s:^w14_mvec" (concl th))
          or (free_in "c:^w14_mvec" (concl th)))
             => ASSUME_TAC th
              | ALL_TAC)
      well_formed_free_list_nonintersection_lemma

 THEN port[SEL_trans]                    % unfold spec %
% ================================================================= %
			                % expand the M_* ops %

 THEN port[M_CDR]                       % rewrite M_CDR c  %
 THEN IMP_RES_THEN port1 car_cdr_mem_abs_lemma
 THEN port[M_CDR]                       % rewrite M_CDR (cdr c)  %
 THEN IMP_RES_THEN port1 car_cdr_mem_abs_lemma
 THEN port[M_CDR]                       % rewrite M_CDR (cddr c)  %
 THEN IMP_RES_THEN port1 car_cdr_mem_abs_lemma

					% rewrite the 1st M_Cons %
 THEN port[M_Cons_tr]
 THEN IMP_RES_n_THEN 3 port1 (hd(IMP_CANON M_Cons_unfold_1_thm))
					% unwind the cell1_mem_free let binding %
 THEN port[LET_THM]
 THEN in1_conv_tac BETA_CONV
 THEN prt[mem_free_of]

 THEN port[M_CAR]			% unwind M_CAR (s,mem1, ) %
 THEN IMP_RES_n_THEN 3
      ((IMP_RES_THEN (port1 o (MATCH_MP car_cdr_mem_abs_lemma) o SPEC_ALL))
       o snd
       o EQ_IMP_RULE
       o (AP_TERM "is_cons")
       o SPEC_ALL)
      (hd(IMP_CANON Store14_root_1_lemma))

 THEN port[M_is_T]
 THEN IMP_RES_n_THEN 4			% unwind M_atom_of(car(mem1 s),mem1, ) %
      ((IMP_RES_THEN (port1 o (MATCH_MP atom_symbol_mem_abs_lemma) o SPEC_ALL))
       o snd
       o EQ_IMP_RULE
       o (AP_TERM "is_symbol")
       o SPEC_ALL)
      (hd(tl(IMP_CANON Store14_car_cdr_1_lemma)))
 THEN port[LET_THM]			% unwind the cond let binding %
 THEN in1_conv_tac BETA_CONV
 THEN prt[cell_of; mem_of; free_of]

 THEN port[M_CDR]			% unwind M_CDR (c,mem1, ) %
 THEN IMP_RES_n_THEN 3
      ((IMP_RES_THEN (port1 o (MATCH_MP car_cdr_mem_abs_lemma) o SPEC_ALL))
       o snd
       o EQ_IMP_RULE
       o (AP_TERM "is_cons")
       o SPEC_ALL)
      (hd(IMP_CANON Store14_root_1_lemma))

 THEN port[M_CDR]			% unwind M_CDR (cdr(mem1 c),mem1, ) %
 THEN IMP_RES_n_THEN 4
      ((IMP_RES_THEN (port1 o (MATCH_MP car_cdr_mem_abs_lemma) o SPEC_ALL))
       o snd
       o EQ_IMP_RULE
       o (AP_TERM "is_cons")
       o SPEC_ALL)
      (hd(IMP_CANON Store14_car_cdr_1_lemma))
 THEN IMP_RES_n_THEN 4			% unwind M_Car (cdr(mem1 c),mem1, ) %
      ((IMP_RES_THEN (port1 o (MATCH_MP car_cdr_mem_abs_lemma) o SPEC_ALL))
       o snd
       o EQ_IMP_RULE
       o (AP_TERM "is_cons")
       o SPEC_ALL)
      (hd(tl(IMP_CANON Store14_car_cdr_1_lemma)))
 THEN IMP_RES_n_THEN 5			% unwind M_Car (cddr(mem1 c),mem1, ) %
      ((IMP_RES_THEN (port1 o (MATCH_MP car_cdr_mem_abs_lemma) o SPEC_ALL))
       o snd
       o EQ_IMP_RULE
       o (AP_TERM "is_cons")
       o SPEC_ALL)
      (hd(IMP_CANON Store14_cadr_cddr_1_lemma))

 THEN FIRST_ASSUM			% is_symbol (mem0 T_addr) %
 (\th. free_in "bus32_symb_append #0000000000000000000000000001" (concl th)
      => ASSUME_TAC (porr[SYM_RULE is_symbol]
                     (rr[bus32_symb_fields_lemma
                       ;is_symbol]
                        (AP_TERM "is_symbol" th)))
       | NO_TAC)

 THEN IMP_RES_THEN			% mem1 T_addr = mem0 T_addr %
      ((\th. ASSUME_TAC th		% is_symbol(mem1 T_addr) %
             THEN IMP_RES_THEN (ASSUME_TAC o SPEC_ALL)
                               ((snd o EQ_IMP_RULE o (AP_TERM "is_symbol"))th))
       o SYM
       o (SPECL [mem0
		; "bus32_cons_append #00 RT_CONS
                (cdr_bits(^mem0(cdr_bits(^mem0(cdr_bits(^mem0(c ^t')))))))
                ((d:^w14_mvec) ^t')"]))
     ((DISCH_ALL o GEN_ALL o UNDISCH o SPEC_ALL) Store14_1_lemma)

					% !x. garbage_bits(mem1 d) = #00 %
 THEN IMP_RES_THEN
 (ASSUME_TAC
   o (SPECL ["(free:^w14_mvec) ^t'";
             "(cdr_bits(^mem0(cdr_bits(^mem0(cdr_bits(^mem0(c (^t':num))))))))";
             "(d:^w14_mvec) ^t'"]))
   garb_bits_untouched_lemma
					% is_symbol (mem1 (car s)) %
 THEN IMP_RES_n_THEN 4
      ((IMP_RES_THEN (ASSUME_TAC o (SPEC "bus32_cons_append 
          #00 
          RT_CONS
          (cdr_bits(^mem0(cdr_bits(^mem0(cdr_bits(^mem0(c (^t'))))))))
          (d ^t')")))
       o snd
       o EQ_IMP_RULE
       o (AP_TERM "is_symbol")
       o SPEC_ALL)
      (hd(tl(IMP_CANON Store14_car_cdr_1_lemma)))
   
					% introduce the two conditional theorems %
 THEN IMP_RES_THEN ((\th. ASSUME_TAC th
		          THEN UNDISCH_TAC (concl th))o UNDISCH) SEL_state'
 THEN IMP_RES_THEN ((\th. ASSUME_TAC th
		          THEN UNDISCH_TAC (concl th))o UNDISCH) SEL_Next'
 THEN COND_CASES_THEN			% split on the branch %
      (\th. SUBST_ALL_TAC th
            THEN ASSUME_TAC (SYM_RULE (rr[]th)))
 THEN prt[COND_CLAUSES]
 THEN STRIP_TAC THEN STRIP_TAC
 THEN IMP_RES_n_THEN 2 port1 TimeOf_Next_lemma

 THEN ABBREV_TAC "(TimeOf(is_major_state mpc)t)" "t':num"
 THEN ABBREV_TAC "(memory:^m14_32_mvec) t'" "mem0:^mem14_32"
 THEN ABBREV_TAC
 "Store14  (free (t':num))
           (bus32_cons_append 
            #00 
            RT_CONS
            (cdr_bits(mem0(cdr_bits(mem0(cdr_bits(mem0(c t')))))))
            (d t'))
           mem0"
 "mem1:^mem14_32"
	    
 THEN prt[PAIR_EQ]
 THEN part[state_abs_thm]		% simplify _imp view %
 THEN REPEAT CONJ_TAC
 THEN (REFL_TAC ORELSE ALL_TAC)
 THENL
 [ prt[bus32_symb_fields_lemma]
   THEN re_conv_tac wordn_CONV
   THEN port[Bits28_Word28]
   THEN port[Val]
   THEN prt[val_0_lemma]
   THEN prt[val; bv]
   THEN rt[ADD_CLAUSES; COND_CLAUSES; T_atom]
 ; IMP_RES_n_THEN 3 (\th. (is_eq(concl th)) => (SUBST_ALL_TAC o SYM_RULE) th
                                             | ALL_TAC)
        (DISCH_ALL (SPECL ["car_bits(mem1((s:^w14_mvec) t'))"; "T_addr"]
                          (UNDISCH (SPEC "mem1:^mem14_32"
                                         (GEN_ALL conditional_atom_bits_11)))))
   THEN FIRST_ASSUM (\th. is_neg(concl th)
                          => (\th1. ASSUME_TAC th1 THEN UNDISCH_TAC (concl th1))
                              (porr[SYM_RULE Val_Bits28_11]th)
                           | NO_TAC)
   THEN part[bus32_symb_fields_lemma]
   THEN port[T_atom_lemma]
   THEN port[SYM_RULE Symb_11]
   THEN port[SYM_RULE T_atom]
   THEN DISCH_THEN (SUBST1_TAC o EQF_INTRO)
   THEN rt[]
 ]);;

% ================================================================= %
%< documentation: aids for interactive proof discovery
let cell1 = "(bus32_cons_append 
            #00 
            RT_CONS
            (cdr_bits(mem0((c:^w14_mvec) t')))
            (d t'))"
and cell2 = "(bus32_cons_append #00 RT_CONS((e:^w14_mvec) t')(free t'))";;

 THEN ABBREV_TAC "(memory:^m14_32_mvec) t'" "mem0:^mem14_32"
 THEN ABBREV_TAC
 "Store14  (free (t':num))
           (bus32_cons_append 
            #00 
            RT_CONS
            (cdr_bits(mem0(cdr_bits(mem0(cdr_bits(mem0(c t')))))))
            (d t'))
           mem0"
 "mem1:^mem14_32"
>%
% ================================================================= %
save_thm(`correctness_SEL`,correctness_SEL);;

timer false;;
close_theory ();;
print_theory `-`;;
