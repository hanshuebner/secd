% SECD verification                                               %
%                                                                 %
% FILE:        mu-prog_LD.ml                                      %
%                                                                 %
% DESCRIPTION: proves the effect of computing the LD              %
%              microinstruction sequence.                         %
%                                                                 %
% USES FILES:   proof_LD2.th                                      %
%                                                                 %
% Brian Graham 90.04.12                                           %
%                                                                 %
% Modifications:                                                  %
% 06.08.91 - BtG - updated to HOL2                                %
%=================================================================%
new_theory `mu-prog_LD`;;
loadt `mu-prog_proof_fcn`;;

timer false;;
new_parent `mu-prog_LD2`;;
% ================================================================= %
let msig = ":^mtime->bool"
and mem14_32 = ":word14->word32";;

let w9_mvec = ":^mtime->word9"
and w14_mvec = ":^mtime->word14"
and w32_mvec = ":^mtime->word32"
and m14_32_mvec = ":^mtime->^mem14_32";;
% ================================================================= %

let ptheory = `phase_lemmas2`;;

load_definition `top_SECD` `nth`;;

map (load_theorem `mu-prog_LD2`)
 [ `loop1_nth`
 ; `loop2_nth`
 ];;
let head = (\th. CONJUNCT1 th, CONJUNCT2 th)
           (theorem `mu-prog_LD1` `base`);;
map (load_theorem `mu-prog_LD1`)
 [ `loop1_exit`
 ; `loop2_exit`
 ; `tail`
 ];;
load_theorem `mu-prog_level` `Next_interval'`;;
map (load_theorem `mu-prog_sr_proofs`)
 [ `Consx1x2_state`
 ; `Consx1x2_nonmajor`
 ];;

letrec DISCHL l th =
  (l = []) => th | DISCH (hd l) (DISCHL (tl l) th);;

timer true;;

let Z_refld = EQT_INTRO(EQT_INTRO(REFL "ZERO28"));;

% ================================================================= %
% The interval theorems are modified for use with the interval      %
% proof function.                                                   %
% ================================================================= %
let consx1x2 = reformat Consx1x2_state Consx1x2_nonmajor;;
let head =
 (\th. CONJUNCT1 th, CONJUNCT2 th)
  (reformat (fst head)(snd head));;

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
let (LD_st, LD_non) =
  sequencer head
            [ loop1_nth; loop1_exit; loop2_nth
	    ; loop2_exit; consx1x2; tail
            ];;

let time = (snd o dest_comb o fst o dest_eq o concl o CONJUNCT1) LD_st;;

% ================================================================= %
% Simplify the time argument                                        %
% rewrite non to be Next                                            %
% check that final step done properly                               %
% ================================================================= %
let num_simp = prove
("!t n1 n2 n3 n4 n5 n6 n7 n8.
    ((((((t + n1) + (n2 * n3)) + n4) + (n2 * n5)) + n6) + n7) + n8 =
    t + (n1 + n4 + n6 + n7 + n8) + (n2 * (n3 + n5))",
 REPEAT GEN_TAC
 THEN port[LEFT_ADD_DISTRIB]
 THEN prt[SYM_RULE ADD_ASSOC]
 THEN port[SPECL ["n*m"; "p:num"]ADD_SYM]
 THEN prt[SYM_RULE ADD_ASSOC]
 THEN port[SPECL ["n*m"; "p:num"]ADD_SYM]
 THEN prt[SYM_RULE ADD_ASSOC]
 THEN REFL_TAC
 );;

% ================================================================= %
let ADD_0 = CONJUNCT1 ADD_CLAUSES
and ADD_SUC = (CONJUNCT1 (CONJUNCT2 (CONJUNCT2 ADD_CLAUSES)));;

% ================================================================= %
let num_inst_simp = prove
("14 + 12 + 5 + 4 + 5 = 40",
 CONV_TAC
 (REPEATC
  (CHANGED_CONV
   (ONCE_DEPTH_CONV num_CONV
    THENC ONCE_DEPTH_CONV (REWR_CONV ADD_0)
    THENC ONCE_DEPTH_CONV (REWR_CONV ADD_SUC)
    THENC ONCE_DEPTH_CONV (REWR_CONV INV_SUC_EQ))))
 THEN REFL_TAC
 );;

% ================================================================= %
%  The near final theorems                                          %
% Tidies up the last step which stepper left out - updates the      %
% dp registers to time t+n instead of (PRE (t+n)), and converts the %
% nonmajor theorem to Next.                                         %
% ================================================================= %
let LD_state,LD_Next =
 let thm1,thm2 = (SUBS[num_inst_simp](porr[num_simp]LD_st),
                  SUBS[num_inst_simp](porr[num_simp]LD_non))
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
  in1_conv_tac num_CONV
  THEN port[ADD_CLAUSES]
  THEN MATCH_MP_TAC LESS_ADD_NONZERO
  THEN SYM_TAC
  THEN MATCH_MP_TAC LESS_NOT_EQ
  THEN MATCH_ACCEPT_TAC LESS_0)
 in
 (LIST_CONJ
   (append ((filter(\th.
		    ((mem o fst o dest_comb o fst
			  o dest_eq o concl) th)
		    [ "mpc:^w9_mvec"
		    ; "memory:^m14_32_mvec"
		    ])) (CONJUNCTS thm1))
	   [new_whole_conj]),
  porr [SYM_RULE Next]
       (CONJ time_less
	     (CONJ (prove_state_value mpc_t) thm2)));;

% ================================================================= %
% The final step: eliminate the substitute the expression for       %
% the genvar'ed values, and remove the assumption defining them.    %
% Save the resulting theorems.                                      %
%   Notice that the assumptions include:                            %
% 	clock_constraint                                            %
% 	^SYS_imp                                                    %
% 	reserved_words_constraint                                   %
% 	well_formed_free_list                                       %
% 	"mpc t = #000101011"                                        %
% 	the 2 DEC28 assumptions                                     %
% 	"opcode_bits(memory t(car_bits(memory t(c t)))) =           %
%             #000000001"                                           %
% 	~NEG(iVal(Bits28(atom_bits(memory t(car_bits(...))))))      %
% 	~NEG(iVal(Bits28(atom_bits(memory t(cdr_bits(...))))))      %
%                                                                   %
% The last 3 assumptions are part of the valid_program_constraint.  %
% ================================================================= %
save_thm (`LD_state`,
	  prr[REFL_CLAUSE; IMP_CLAUSES]
	  ((\thl. (SPECL (map(snd o dest_eq)thl)
		   (GENL (map(fst o dest_eq)thl)
			 (DISCHL thl LD_state))))
	   (filter (\th. (is_eq th)
		         => ((is_comb o fst o dest_eq)th)
		            => false
		             | true
                          | false)
		   (hyp LD_state))));;

save_thm (`LD_Next`,
	  prr[REFL_CLAUSE; IMP_CLAUSES]
	  ((\thl. (SPECL (map(snd o dest_eq)thl)
		   (GENL (map(fst o dest_eq)thl)
			 (DISCHL thl LD_Next))))
	   (filter (\th. (is_eq th)
		         => ((is_comb o fst o dest_eq)th)
		            => false
		             | true
                          | false)
		   (hyp LD_Next))));;


timer false;;
close_theory ();;
print_theory `-`;;
