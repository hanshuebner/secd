% SECD verification                                                 %
%                                                                   %
% FILE:         correctness_init.ml                                 %
%                                                                   %
% DESCRIPTION:  The correspondence between the specification for    % 
%               top level fsm transitions aside from machine        %
%               instruction exectutions.                            %
%                                                                   %
% USES FILES:   correctness_misc.th, wordn & integer libraries      %
%               liveness - only to get at ancestor theories ...     %
%                                                                   %
% Brian Graham 02.01.91                                             %
%                                                                   %
% Modifications:                                                    %
% ================================================================= %
new_theory `correctness_init`;;

map new_parent
 [ `correctness_misc`
 ; `liveness`
 ];;

loadf `wordn`;;
load_library `integer`;;

map (load_definition `when`)
 [ `when`
 ];;
map (load_theorem `when`)
 [ `TimeOf_Next_lemma`
 ];;
map (load_theorem `constraints`)
 [ `state_abs_thm`
 ];;
map (load_theorem `mu-prog_init_proofs`)
 [ `idle_state`
 ; `idle_Next`
 ; `error0_state`
 ; `error0_Next`
 ; `error1_state`
 ; `error1_Next`
 ];;
map (load_definition `abstract_mem_type`)
 [ `M_CAR`
 ];;
map (load_theorem `mem_abs`)
 [ `car_cdr_mem_abs_lemma`
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

% ================================================================= %
timer true;;

% ================================================================= %
% Discharge every assumption with "t" in it, and generalize it.     %
% ================================================================= %
let idle_state' =
 GEN "t:^mtime" 
 (DISCH "mpc (t:^mtime) = #000010110"
         idle_state);;
let idle_Next' =
 GEN "t:^mtime" 
 (DISCH "mpc (t:^mtime) = #000010110"
         idle_Next);;

let error0_state' =
 GEN "t:^mtime" 
 (DISCH "mpc (t:^mtime) = #000011000"
         error0_state);;
let error0_Next' =
 GEN "t:^mtime" 
 (DISCH "mpc (t:^mtime) = #000011000"
         error0_Next);;

let error1_state' =
 GEN "t:^mtime" 
 (DISCH "mpc (t:^mtime) = #000011010"
         error1_state);;
let error1_Next' =
 GEN "t:^mtime" 
 (DISCH "mpc (t:^mtime) = #000011010"
         error1_Next);;

% ================================================================= %
% AP_TERM_INV = |- !f a b. ~(f a = f b) ==> ~(a = b)                %
% ================================================================= %
let AP_TERM_INV =
 GEN_ALL(porr[GEN_ALL(CONTRAPOS_CONV "c==>d")]
		     (DISCH_ALL (AP_TERM "f:*->**"(ASSUME "a:* = b"))));;

% ================================================================= %
let t' = "(TimeOf(is_major_state mpc)t)";;
% ================================================================= %

% ================================================================= %
let correctness_idle_1 = TAC_PROOF
(([
   % ----------------------------- button has been asserted %
   "(button_pin:num->bool)(TimeOf(is_major_state mpc)t)"
 ; % ----------------------------- car NUM_addr is a cons cell %
   "is_cons(memory(TimeOf(is_major_state mpc)t)
            (car_bits(memory(TimeOf(is_major_state mpc)t)NUM_addr)))"
 ; % ----------------------------- NUM_addr is a cons cell %
   "is_cons(memory(TimeOf(is_major_state mpc)t) NUM_addr)"

 ; "mpc(TimeOf(is_major_state mpc)t) = #000010110" 
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
   (M_Cdr(M_CAR(NUM_addr,
                ((mem_abs o memory) when (is_major_state mpc))t,
                (free               when (is_major_state mpc))t)),
     NIL_addr,
     M_Car(M_CAR(NUM_addr,
                 ((mem_abs o memory) when (is_major_state mpc))t,
                 (free               when (is_major_state mpc))t)),
     NIL_addr,
     M_Cdr(NUM_addr,
           ((mem_abs o memory) when (is_major_state mpc))t,
           (free               when (is_major_state mpc))t),
     ((mem_abs o memory) when (is_major_state mpc))t, 
     top_of_cycle)"),
 FIRST_ASSUM				% state_abs is top_of_cycle %
      (\th. (ASSUME_TAC o (porr[state_abs_thm])
			o (AP_TERM "state_abs")) th ? NO_TAC)
 THEN port[when]
 THEN BETA_TAC
 THEN port[o_THM]
 THEN port[M_CAR]
 THEN IMP_RES_THEN port1 car_cdr_mem_abs_lemma
 THEN IMP_RES_THEN port1 car_cdr_mem_abs_lemma

					% introduce the two conditional theorems %
 THEN IMP_RES_THEN ((\th. ASSUME_TAC th
		          THEN UNDISCH_TAC (concl th))) idle_state'
 THEN IMP_RES_THEN ((\th. ASSUME_TAC th
		          THEN UNDISCH_TAC (concl th))) idle_Next'
 THEN art[]				% split on the branch %
 THEN STRIP_TAC THEN STRIP_TAC
 THEN IMP_RES_n_THEN 2 port1 TimeOf_Next_lemma

 THEN ABBREV_TAC "(TimeOf(is_major_state mpc)t)" "t':num"
 THEN part[state_abs_thm]		% simplify _imp view %
 THEN REFL_TAC
 );;

% ================================================================= %
% ================================================================= %
let correctness_idle_2 = TAC_PROOF
(([
   % ----------------------------- button is not asserted %
   "~(button_pin:num->bool)(TimeOf(is_major_state mpc)t)"
 ; "mpc(TimeOf(is_major_state mpc)t) = #000010110" 
 ; "Inf(is_major_state mpc)"
 ; SYS_imp
 ; "clock_constraint SYS_Clocked" 
 ],
  "(((s:^w14_mvec)      when (is_major_state mpc))(SUC t),    
    ((e:^w14_mvec)      when (is_major_state mpc))(SUC t),
    ((c:^w14_mvec)      when (is_major_state mpc))(SUC t),
    ((d:^w14_mvec)      when (is_major_state mpc))(SUC t),
    ((free:^w14_mvec)   when (is_major_state mpc))(SUC t), 
    ((mem_abs o memory) when (is_major_state mpc))(SUC t), 
    ((state_abs o mpc)  when (is_major_state mpc))(SUC t)) =
   ((s                  when (is_major_state mpc)) t,    
    (e                  when (is_major_state mpc)) t,
    (c                  when (is_major_state mpc)) t,
    (d                  when (is_major_state mpc)) t,
    (free               when (is_major_state mpc)) t, 
    ((mem_abs o memory) when (is_major_state mpc)) t, 
    idle)"
  ),
 FIRST_ASSUM				% state_abs is top_of_cycle %
      (\th. (ASSUME_TAC o (porr[state_abs_thm])
			o (AP_TERM "state_abs")) th ? NO_TAC)
 THEN port[when]
 THEN BETA_TAC
 THEN port[o_THM]
					% introduce the two conditional theorems %
 THEN IMP_RES_THEN ((\th. ASSUME_TAC th
		          THEN UNDISCH_TAC (concl th))) idle_state'
 THEN IMP_RES_THEN ((\th. ASSUME_TAC th
		          THEN UNDISCH_TAC (concl th))) idle_Next'
 THEN art[]				% split on the branch %
 THEN STRIP_TAC THEN STRIP_TAC
 THEN IMP_RES_n_THEN 2 port1 TimeOf_Next_lemma

 THEN ABBREV_TAC "(TimeOf(is_major_state mpc)t)" "t':num"
 THEN part[state_abs_thm]		% simplify _imp view %
 THEN REFL_TAC
 );;

% ================================================================= %
let correctness_error0 = TAC_PROOF
(([
   % ----------------------------- error0 state %
   "mpc(TimeOf(is_major_state mpc)t) = #000011000" 
 ; "Inf(is_major_state mpc)"
 ; SYS_imp
 ; "clock_constraint SYS_Clocked" 
 ],
  "button_pin(TimeOf(is_major_state mpc)t) 
   => 
   ((((s:^w14_mvec)      when (is_major_state mpc))(SUC t),    
     ((e:^w14_mvec)      when (is_major_state mpc))(SUC t),
     ((c:^w14_mvec)      when (is_major_state mpc))(SUC t),
     ((d:^w14_mvec)      when (is_major_state mpc))(SUC t),
     ((free:^w14_mvec)   when (is_major_state mpc))(SUC t), 
     ((mem_abs o memory) when (is_major_state mpc))(SUC t), 
     ((state_abs o mpc)  when (is_major_state mpc))(SUC t)) =
    ((s                  when (is_major_state mpc)) t,    
     (e                  when (is_major_state mpc)) t,
     (c                  when (is_major_state mpc)) t,
     (d                  when (is_major_state mpc)) t,
     (free               when (is_major_state mpc)) t, 
     ((mem_abs o memory) when (is_major_state mpc)) t, 
     error1))
   | 
   (((s                  when (is_major_state mpc))(SUC t),    
     (e                  when (is_major_state mpc))(SUC t),
     (c                  when (is_major_state mpc))(SUC t),
     (d                  when (is_major_state mpc))(SUC t),
     (free               when (is_major_state mpc))(SUC t), 
     ((mem_abs o memory) when (is_major_state mpc))(SUC t), 
     ((state_abs o mpc)  when (is_major_state mpc))(SUC t)) =
    ((s                  when (is_major_state mpc)) t,    
     (e                  when (is_major_state mpc)) t,
     (c                  when (is_major_state mpc)) t,
     (d                  when (is_major_state mpc)) t,
     (free               when (is_major_state mpc)) t, 
     ((mem_abs o memory) when (is_major_state mpc)) t, 
      error0))"
  ),
 FIRST_ASSUM				% state_abs is top_of_cycle %
      (\th. (ASSUME_TAC o (porr[state_abs_thm])
			o (AP_TERM "state_abs")) th ? NO_TAC)
 THEN port[when]
 THEN BETA_TAC
 THEN port[o_THM]
					% introduce the two conditional theorems %
 THEN IMP_RES_THEN ((\th. ASSUME_TAC th
		          THEN UNDISCH_TAC (concl th))) error0_state'
 THEN IMP_RES_THEN ((\th. ASSUME_TAC th
		          THEN UNDISCH_TAC (concl th))) error0_Next'
 THEN COND_CASES_TAC			% split on the branch %
 THEN prt[COND_CLAUSES]
 THEN STRIP_TAC THEN STRIP_TAC
 THEN IMP_RES_n_THEN 2 port1 TimeOf_Next_lemma
 THEN part[state_abs_thm]		% simplify _imp view %
 THEN REFL_TAC
 );;

% ================================================================= %
let correctness_error1 = TAC_PROOF
(([
   % ----------------------------- error0 state %
   "mpc(TimeOf(is_major_state mpc)t) = #000011010" 
 ; "Inf(is_major_state mpc)"
 ; SYS_imp
 ; "clock_constraint SYS_Clocked" 
 ],
  "button_pin(TimeOf(is_major_state mpc)t) 
   => 
   ((((s:^w14_mvec)      when (is_major_state mpc))(SUC t),    
     ((e:^w14_mvec)      when (is_major_state mpc))(SUC t),
     ((c:^w14_mvec)      when (is_major_state mpc))(SUC t),
     ((d:^w14_mvec)      when (is_major_state mpc))(SUC t),
     ((free:^w14_mvec)   when (is_major_state mpc))(SUC t), 
     ((mem_abs o memory) when (is_major_state mpc))(SUC t), 
     ((state_abs o mpc)  when (is_major_state mpc))(SUC t)) =
    ((s                  when (is_major_state mpc)) t,    
     (e                  when (is_major_state mpc)) t,
     (c                  when (is_major_state mpc)) t,
     (d                  when (is_major_state mpc)) t,
     (free               when (is_major_state mpc)) t, 
     ((mem_abs o memory) when (is_major_state mpc)) t, 
     error1))
   | 
   (((s                  when (is_major_state mpc))(SUC t),    
     (e                  when (is_major_state mpc))(SUC t),
     (c                  when (is_major_state mpc))(SUC t),
     (d                  when (is_major_state mpc))(SUC t),
     (free               when (is_major_state mpc))(SUC t), 
     ((mem_abs o memory) when (is_major_state mpc))(SUC t), 
     ((state_abs o mpc)  when (is_major_state mpc))(SUC t)) =
    ((s                  when (is_major_state mpc)) t,    
     (e                  when (is_major_state mpc)) t,
     (c                  when (is_major_state mpc)) t,
     (d                  when (is_major_state mpc)) t,
     (free               when (is_major_state mpc)) t, 
     ((mem_abs o memory) when (is_major_state mpc)) t, 
      idle))"
  ),
 FIRST_ASSUM				% state_abs is top_of_cycle %
      (\th. (ASSUME_TAC o (porr[state_abs_thm])
			o (AP_TERM "state_abs")) th ? NO_TAC)
 THEN port[when]
 THEN BETA_TAC
 THEN port[o_THM]
					% introduce the two conditional theorems %
 THEN IMP_RES_THEN ((\th. ASSUME_TAC th
		          THEN UNDISCH_TAC (concl th))) error1_state'
 THEN IMP_RES_THEN ((\th. ASSUME_TAC th
		          THEN UNDISCH_TAC (concl th))) error1_Next'
 THEN COND_CASES_TAC			% split on the branch %
 THEN prt[COND_CLAUSES]
 THEN STRIP_TAC THEN STRIP_TAC
 THEN IMP_RES_n_THEN 2 port1 TimeOf_Next_lemma
 THEN part[state_abs_thm]		% simplify _imp view %
 THEN REFL_TAC
 );;

timer false;;
% ================================================================= %
save_thm(`correctness_idle_1`,correctness_idle_1);;
save_thm(`correctness_idle_2`,correctness_idle_2);;
save_thm(`correctness_error0`,correctness_error0);;
save_thm(`correctness_error1`,correctness_error1);;
% ================================================================= %

close_theory ();;
print_theory `-`;;
