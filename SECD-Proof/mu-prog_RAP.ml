new_theory `mu-prog_RAP`;;
loadf `mu-prog_proof_fcn`;;

timer false;;

let ptheory = `phase_lemmas4`;;
new_parent ptheory;;

map (load_theorem `mu-prog_level`)
 [ `Start_lem`
 ; `Next_interval'`
 ];;

let f = prove_next_step ptheory;;
% ================================================================= %
let mtime = ":num";;
let msig = ":^mtime->bool"
and mem14_32 = ":word14->word32";;

let w9_mvec = ":^mtime->word9"
and w14_mvec = ":^mtime->word14"
and w32_mvec = ":^mtime->word32"
and m14_32_mvec = ":^mtime->^mem14_32";;
% ================================================================= %
timer true;;
% ================================================================= %
% snd_thm :                                                         %
% |- !t''. (PRE t) < t'' /\ t'' < t ==> ~is_major_state mpc t''     %
% ================================================================= %
let snd_thm = SPECL ["t:^mtime"; "is_major_state mpc"] Start_lem;;

let consx1x2 = reformat (theorem `mu-prog_sr_proofs` `Consx1x2_state`)
                        (theorem `mu-prog_sr_proofs` `Consx1x2_nonmajor`);;

let head =
 S (pair o CONJUNCT1)
   CONJUNCT2 
   ((uncurry reformat)
             (stepper f (theorem `mu-prog_init_proofs` `toc_RAP_state`,
                         theorem `mu-prog_init_proofs` `toc_RAP_nonmajor`)));;

% ================================================================= %
% Several intermediate theorems are unnecessarily saved: this was   %
% done during development so not everything was lost if a           %
% system limit was reached.                                         %
% ================================================================= %
let mid1 = uncurry reformat
  (stepper f
   (CONJ (ASSUME "(mpc (t:^mtime)) = ^(mk_word9_from_num 164)")
         (REFL "T"),
    snd_thm))
 ;;

let mid2 = uncurry reformat
 (stepper f
  (CONJ (ASSUME "(mpc (t:^mtime)) = ^(mk_word9_from_num 167)")
        (REFL "T"),
   snd_thm))
 ;;

let tail = uncurry reformat 
 (stepper f
  (CONJ (ASSUME "(mpc (t:^mtime)) = ^(mk_word9_from_num 172)")
        (REFL "T"),
   snd_thm))
 ;;

% ================================================================= %
% The things needed to paste the intervals together.                %
% ================================================================= %
letrec DISCHL l th =
  (l = []) => th | DISCH (hd l) (DISCHL (tl l) th);;

let Z_refld = EQT_INTRO(EQT_INTRO(REFL "ZERO28"));;
% ================================================================= %
% The interval proof function:                                      %
%                                                                   %
% ================================================================= %
let prove_next_interval (th1a,th1b) th2 =
 let mpc_t = hd (filter
                  (\th. "mpc:^w9_mvec" =
                ((fst o dest_comb o fst o dest_eq o concl)th))
       (CONJUNCTS th1a))
 in
 let mpc_assum = "mpc (t:^mtime) = ^((snd o dest_eq o concl) mpc_t)"
 in
 let thm =
     (porr[PRE_SUC]	% CONJ together & do once only %
	  (MATCH_MP(((DISCH mpc_assum)
                     o (\th.DISCHL(filter(\a.not(a=mpc_assum))
                                         (filter(free_in "t:^mtime")
                                                (hyp th)))
                                  th)
		     )th2)
                   mpc_t))
 in
 let thmA = 
 (( UNDISCH_ALL
  o (porr[IMP_CLAUSES])
  o (SUBS [F_refld;Z_refld])
  o ((Consx1x2=(snd(dest_eq mpc_assum)))
     => porr free_list_conjuncts 
     | I)
  o (SUBS (CONJUNCTS th1a))
  ) thm)
 in
 (CONJUNCT1 thmA,
  MATCH_MP Next_interval'
           (CONJ th1b (CONJUNCT2 thmA)))
 ;;


letrec sequencer th thl =
  (thl = [])
  => th
  |  sequencer (prove_next_interval th (hd thl)) (tl thl);;

% ================================================================= %
% The sequence proof:                                               %
% ================================================================= %
let (RAP_st, RAP_non) =
 sequencer head
 [ consx1x2; mid1; consx1x2; mid2; consx1x2; tail ];;

let time = (snd o dest_comb o fst o dest_eq o concl o CONJUNCT1) RAP_st;;

let ADD_0 = CONJUNCT1 ADD_CLAUSES
and ADD_SUC = (CONJUNCT1 (CONJUNCT2 (CONJUNCT2 ADD_CLAUSES)));;

let num_inst_simp = TAC_PROOF
(([], "8+(4+(3+(4+(5+(4+20))))) = 48"),
 CONV_TAC
 (REPEATC
  (CHANGED_CONV
   ((RATOR_CONV(RAND_CONV(RATOR_CONV(RAND_CONV num_CONV)))
     THENC RAND_CONV num_CONV
     THENC ONCE_DEPTH_CONV (REWR_CONV ADD_SUC)
     THENC ONCE_DEPTH_CONV (REWR_CONV INV_SUC_EQ))
    ORELSEC (ONCE_DEPTH_CONV (REWR_CONV ADD_0)
	     THENC (ONCE_DEPTH_CONV REFL ORELSEC ALL_CONV)))))
 THEN REFL_TAC
 );;

let num_simp = prr[ADD_ASSOC](AP_TERM "$+ t" num_inst_simp);;

let RAP_state,RAP_Next =
 let thm1,thm2 = (SUBS[num_simp]RAP_st,
                  SUBS[num_simp]RAP_non)
 in
 let mpc_t = CONJUNCT1 thm1
 in
 let nextA = (snd o dest_eq o concl) mpc_t
 in
 let n = int_of_word9 nextA
 in
 let thm = theorem `phase_lemmas1` (`phase_lemma_`^(string_of_int n))
 in
 let hy = (fst o dest_imp o concl) thm
 in 
 let time = (snd o dest_comb o fst o dest_eq o concl) mpc_t
 in
 let new_state_thm = (porr[PRE_SUC]
		      (MATCH_MP ( ((DISCH hy)
				   o LIST_CONJ
				   o tl o tl o tl o tl o tl o tl
				   o CONJUNCTS
				   o UNDISCH)
				  thm)
				mpc_t))
 in
 let new_whole_conj = (SUBS (CONJUNCTS thm1)
			    (LIST_CONJ (filter(\th.
			    ((mem o fst o dest_comb o fst
				  o dest_eq o concl) th)
			    [ "s:^w14_mvec"
			    ; "e:^w14_mvec"
			    ; "c:^w14_mvec"
			    ; "d:^w14_mvec"
			    ; "free:^w14_mvec"
			    ]) (CONJUNCTS new_state_thm))))
 in
 let time_less = TAC_PROOF
 (([], "t < ^time"),
  MATCH_MP_TAC LESS_ADD_NONZERO
  THEN in1_conv_tac num_CONV
  THEN port[ADD_CLAUSES]
  THEN SYM_TAC
  THEN MATCH_MP_TAC LESS_NOT_EQ
  THEN MATCH_ACCEPT_TAC LESS_0)
 in
 (save_thm(`RAP_state`,
	   (LIST_CONJ
	    (append ((filter(\th.
			     ((mem o fst o dest_comb o fst
				   o dest_eq o concl) th)
			     [ "mpc:^w9_mvec"
 			     ; "memory:^m14_32_mvec"
			     ])) (CONJUNCTS thm1))
		    [ new_whole_conj]))),
  save_thm (`RAP_Next`,
	    porr [SYM_RULE Next]
	          (CONJ time_less
			(CONJ (prove_state_value mpc_t) thm2))));;

timer false;;
close_theory ();;
print_theory `-`;;
