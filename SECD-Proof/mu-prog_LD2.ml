% SECD verification                                               %
%                                                                 %
% FILE:        mu-prog_LD2.ml                                     %
%                                                                 %
% DESCRIPTION: This file proves the termination, state, and       %
%              non-major state for the 1st while loop of LD.      %
%                                                                 %
% USES FILES:  mu-prog_LD1.th,                                    %
%                                                                 %
% Brian Graham 90.04.11                                           %
%                                                                 %
% Modifications:                                                  %
% 06.08.91 - BtG - updated to HOL2                                %
%=================================================================%
new_theory `mu-prog_LD2`;;

new_parent `mu-prog_LD1`;;
% ================================================================= %
let mtime = ":num";;
let msig = ":^mtime->bool"
and mem14_32 = ":word14->word32";;

let w9_mvec = ":^mtime->word9"
and w14_mvec = ":^mtime->word14"
and w32_mvec = ":^mtime->word32"
and m14_32_mvec = ":^mtime->^mem14_32";;
% ================================================================= %

map (load_theorem `mu-prog_level`)
    [ `Next_interval'`
    ; `F_refld`		
    ; `PRE_SUC`		
    ];;

map (load_theorem `loop_proofs`)
 [ `loop_terminates_lemma`
 ; `nth_DEC_NOT_ZERO`		
 ];;
load_definition `top_SECD` `nth`;;

timer true;;
% ***************************************************************** %
% Getting rid of SUC^n                                              %
% ***************************************************************** %
letrec num_of_SUC tm =
  (is_comb tm) => 1 + (num_of_SUC ((snd o dest_comb) tm))
  	        | 0;;

let MK_t_plus_num_THM n =
 SYM (porr[porr[ADD_SYM](CONJUNCT1 ADD)]
          (prr[porr[ADD_SYM](CONJUNCT2 ADD)]
	      (REDEPTH_CONV num_CONV
			    "t + ^(mk_const(string_of_int n,":num"))")));;

% ================================================================= %
% loop1_state =                                                     %
% .... |- (mpc(SUC(SUC(SUC(SUC(SUC t))))) = #000111000) /\          %
%         (s0(SUC(SUC(SUC(SUC(SUC t))))) = s0 t) /\                 %
%         (s1(SUC(SUC(SUC(SUC(SUC t))))) = s1 t) /\                 %
%         (s2(SUC(SUC(SUC(SUC(SUC t))))) = s2 t) /\                 %
%         (s3(SUC(SUC(SUC(SUC(SUC t))))) = s3 t) /\                 %
%         (memory(SUC(SUC(SUC(SUC(SUC t))))) = memory t) /\         %
%         (arg(SUC(SUC(SUC(SUC t)))) =                              %
%           DEC28(atom_bits(arg(PRE t)))) /\                        %
%         (rmem_pin(SUC(SUC(SUC(SUC t)))) = F) /\                   %
%         (buf1(SUC(SUC(SUC(SUC t)))) =                             %
%           DEC28(atom_bits(arg(PRE t)))) /\                        %
%         (buf2(SUC(SUC(SUC(SUC t)))) = buf2(PRE t)) /\             %
%         (mar_pins(SUC(SUC(SUC(SUC t)))) = x1(PRE t)) /\           %
%         (s(SUC(SUC(SUC(SUC t)))) = s(PRE t)) /\                   %
%         (e(SUC(SUC(SUC(SUC t)))) = e(PRE t)) /\                   %
%         (c(SUC(SUC(SUC(SUC t)))) = c(PRE t)) /\                   %
%         (d(SUC(SUC(SUC(SUC t)))) = d(PRE t)) /\                   %
%         (free(SUC(SUC(SUC(SUC t)))) = free(PRE t)) /\             %
%         (x1(SUC(SUC(SUC(SUC t)))) =                               %
%           cdr_bits(memory t(x1(PRE t)))) /\                       %
%         (x2(SUC(SUC(SUC(SUC t)))) = x2(PRE t)) /\                 %
%         (car(SUC(SUC(SUC(SUC t)))) = car(PRE t)) /\               %
%         (parent(SUC(SUC(SUC(SUC t)))) = parent(PRE t)) /\         %
%         (root(SUC(SUC(SUC(SUC t)))) = root(PRE t)) /\             %
%         (y1(SUC(SUC(SUC(SUC t)))) = y1(PRE t)) /\                 %
%         (y2(SUC(SUC(SUC(SUC t)))) = y2(PRE t)) /\                 %
%         (write_bit_pin(SUC(SUC(SUC(SUC t)))) = T) /\              %
%         (flag0_pin(SUC(SUC(SUC(SUC t)))) = F) /\                  %
%         (flag1_pin(SUC(SUC(SUC(SUC t)))) = F)                     %
% ================================================================= %

% ================================================================= %
% Substitute :                                                      %
% [|- SUC(SUC(SUC(SUC(SUC t)))) = t + 5;                            %
%  |- SUC(SUC(SUC(SUC t))) = PRE(t + 5)]                            %
% To get:                                                           %
% loop1_state =                                                             %
% .. |- !t.                                                         %
%       ((atom_bits(arg(PRE t)) = ZERO28) = F) ==>                  %
%       (mpc t = #000111000) ==>                                    %
% **    (mpc(t + 5) = #000111000) /\                                %
%       (s0(t + 5) = s0 t) /\                                       %
%       (s1(t + 5) = s1 t) /\                                       %
%       (s2(t + 5) = s2 t) /\                                       %
%       (s3(t + 5) = s3 t) /\                                       %
%       (memory(t + 5) = memory t) /\                               %
% **    (arg(PRE(t + 5)) = DEC28(atom_bits(arg(PRE t)))) /\         %
%       (rmem_pin(PRE(t + 5)) = F) /\                               %
%       (buf1(PRE(t + 5)) = DEC28(atom_bits(arg(PRE t)))) /\        %
%       (buf2(PRE(t + 5)) = buf2(PRE t)) /\                         %
%       (mar_pins(PRE(t + 5)) = x1(PRE t)) /\                       %
%       (s(PRE(t + 5)) = s(PRE t)) /\                               %
%       (e(PRE(t + 5)) = e(PRE t)) /\                               %
%       (c(PRE(t + 5)) = c(PRE t)) /\                               %
%       (d(PRE(t + 5)) = d(PRE t)) /\                               %
%       (free(PRE(t + 5)) = free(PRE t)) /\                         %
% **    (x1(PRE(t + 5)) = cdr_bits(memory t(x1(PRE t)))) /\         %
%       (x2(PRE(t + 5)) = x2(PRE t)) /\                             %
%       (car(PRE(t + 5)) = car(PRE t)) /\                           %
%       (parent(PRE(t + 5)) = parent(PRE t)) /\                     %
%       (root(PRE(t + 5)) = root(PRE t)) /\                         %
%       (y1(PRE(t + 5)) = y1(PRE t)) /\                             %
%       (y2(PRE(t + 5)) = y2(PRE t)) /\                             %
%       (write_bit_pin(PRE(t + 5)) = T) /\                          %
%       (flag0_pin(PRE(t + 5)) = F) /\                              %
%       (flag1_pin(PRE(t + 5)) = F)                                 %
% ================================================================= %
let loop1_state =
 GEN "t:^mtime"
 (DISCH "(atom_bits(arg(PRE t)) = ZERO28) = F"
        (DISCH "mpc (t:^mtime) = #000111000"
               (SUBS (let num_l = MK_t_plus_num_THM 5
	 	      in
                      let pre_l = porr[PRE_SUC](AP_TERM "PRE" num_l)
		      in
		      [num_l; pre_l])
                     (theorem `mu-prog_LD1` `loop1_state`))));;

let loop1_nonmajor =
 GEN "t:^mtime"
 (DISCH "(atom_bits(arg(PRE t)) = ZERO28) = F"
        (DISCH "mpc (t:^mtime) = #000111000"
               (SUBS [MK_t_plus_num_THM 5]
                     (theorem `mu-prog_LD1` `loop1_nonmajor`))));;


let loop2_state =
 GEN "t:^mtime"
 (DISCH "(atom_bits(arg(PRE t)) = ZERO28) = F"
        (DISCH "mpc (t:^mtime) = #001001000"
               (SUBS (let num_l = MK_t_plus_num_THM 5
	 	      in
		      let pre_l = SUBS [num_l]
		                       (SPEC "SUC (SUC (SUC (SUC t)))"
			 		     (SYM_RULE (CONJUNCT2 PRE)))
		      in
		      [num_l; pre_l])
                     (theorem `mu-prog_LD1` `loop2_state`))));;

let loop2_nonmajor =
 GEN "t:^mtime"
 (DISCH "(atom_bits(arg(PRE t)) = ZERO28) = F"
        (DISCH "mpc (t:^mtime) = #001001000"
               (SUBS [MK_t_plus_num_THM 5]
                     (theorem `mu-prog_LD1` `loop2_nonmajor`))));;

% ================================================================= %
let DEC28_assum1 =
"!w28. (POS (iVal (Bits28 w28)))==>
        (PRE(pos_num_of(iVal(Bits28 w28))) =
           pos_num_of(iVal(Bits28((atom_bits o DEC28) w28))))"
and DEC28_assum2 =
"!w28.(POS (iVal (Bits28 w28)))==>
     ~(NEG (iVal (Bits28 ((atom_bits o DEC28) w28))))";;

% ================================================================= %
let nth_o_lemma = prove
("!w n.atom_bits (nth n (DEC28 o atom_bits) w) =
                          nth n (atom_bits o DEC28)(atom_bits w)",
 GEN_TAC
 THEN INDUCT_TAC
 THEN port[nth]
 THENL
 [ REFL_TAC
 ; port[o_THM]
   THEN poart[]
   THEN REFL_TAC
 ]);;


let loop1_nth_state = TAC_PROOF
((DEC28_assum1.DEC28_assum2.hyp loop1_state,
 "!m t.
   (~(NEG(iVal(Bits28(atom_bits(arg(PRE t))))))) ==>
   (m <= (pos_num_of(iVal(Bits28(atom_bits(arg(PRE t))))))) ==>
   (mpc t = #000111000) ==>
      (mpc(t + (5*m)) = #000111000) /\
      ((s0:^w9_mvec)(t + (5*m)) = s0 t) /\
      ((s1:^w9_mvec)(t + (5*m)) = s1 t) /\
      ((s2:^w9_mvec)(t + (5*m)) = s2 t) /\
      ((s3:^w9_mvec)(t + (5*m)) = s3 t) /\
      ((memory:^m14_32_mvec)(t + (5*m)) = memory t) /\
      ((arg:^w32_mvec)(PRE(t + (5*m))) = nth m (DEC28 o atom_bits)(arg(PRE t))) /\
      ((buf2:^w32_mvec)(PRE(t + (5*m))) = buf2(PRE t)) /\
      ((s:^w14_mvec)(PRE(t + (5*m))) = s(PRE t)) /\
      ((e:^w14_mvec)(PRE(t + (5*m))) = e(PRE t)) /\
      ((c:^w14_mvec)(PRE(t + (5*m))) = c(PRE t)) /\
      ((d:^w14_mvec)(PRE(t + (5*m))) = d(PRE t)) /\
      ((free:^w14_mvec)(PRE(t + (5*m))) = free(PRE t)) /\
      ((x1:^w14_mvec)(PRE(t + (5*m))) = nth m (cdr_bits o (memory t))(x1(PRE t))) /\
      ((x2:^w14_mvec)(PRE(t + (5*m))) = x2(PRE t)) /\
      ((car:^w14_mvec)(PRE(t + (5*m))) = car(PRE t)) /\
      ((parent:^w14_mvec)(PRE(t + (5*m))) = parent(PRE t)) /\
      ((root:^w14_mvec)(PRE(t + (5*m))) = root(PRE t)) /\
      ((y1:^w14_mvec)(PRE(t + (5*m))) = y1(PRE t)) /\
      ((y2:^w14_mvec)(PRE(t + (5*m))) = y2(PRE t))"),
 INDUCT_TAC
 THEN GEN_TAC
 THENL
 [ DISCH_THEN (K ALL_TAC)
   THEN DISCH_THEN (K ALL_TAC)
   THEN prt[MULT_CLAUSES; ADD_CLAUSES; nth]
   THEN DISCH_THEN SUBST1_TAC
   THEN rt[]
 ; SUBST1_TAC ((porr[ADD_ASSOC]           % rewrite "t+(5*(SUC m))" %
                o (AP_TERM "$+ t")
		o (porr[MULT_SYM])
		o (REWR_CONV (CONJUNCT2 MULT)))
               "(SUC m) * 5")
   THEN port[nth]
   THEN DISCH_THEN
   (\a2. DISCH_THEN                         % ~NEG ... %
    \a3. DISCH_THEN                         % SUC n <= %
    \a6. ASSUME_TAC a2                      % mpc t =  %
         THEN ((\a4. ASSUME_TAC a4          % n < ...  %
	             THEN ANTE_RES_THEN
		    (\a7. ASSUME_TAC        % MP (ind assum) a2 %
		      (SUBS
		       (CONJUNCTS
		        (MATCH_MP
		         (MATCH_MP a7 (MATCH_MP LESS_IMP_LESS_OR_EQ a4))
		         a6))
		       (SPEC "t+(5*m)" loop1_state))
		      )
		    a2)
	       (MATCH_MP OR_LESS a3)))
                                    % resolve nth_DEC_NOT_ZERO  %
                                    % with asm's, then use on   %
                                    % loop1_state assum to get rewrites %
   THEN IMP_RES_n_THEN 2 (ANTE_RES_THEN (port1 o (rr[]))
				        o (porr[SYM_RULE nth_o_lemma])
				        o (MATCH_MP NOT_F))
        (SPECL ["m:num"; "atom_bits(arg(PRE t))"]nth_DEC_NOT_ZERO)
   THEN port[o_THM]
   THEN rt[]
 ]);;

let loop1_nth_nonmajor = TAC_PROOF
((DEC28_assum1.DEC28_assum2.hyp loop1_nonmajor,
  "!m t.
   (~(NEG(iVal(Bits28(atom_bits(arg(PRE t))))))) ==>
   (m <= (pos_num_of(iVal(Bits28(atom_bits(arg(PRE t))))))) ==>
   (mpc t = #000111000) ==>
   !t'. (PRE t) < t' /\ t' < (t + (5*m)) ==>
        ~(is_major_state mpc t')"),
 INDUCT_TAC
 THEN GEN_TAC
 THENL
 [ prt[MULT_CLAUSES; ADD_CLAUSES]
   THEN STRIP_TAC
   THEN STRIP_TAC
   THEN STRIP_TAC
   THEN port[theorem `mu-prog_level` `Empty_range`]
   THEN rt[]
 ; SUBST1_TAC ((porr[ADD_ASSOC]           % rewrite "t+(5*(SUC m))" %
                o (AP_TERM "$+ t")
		o (porr[MULT_SYM])
		o (REWR_CONV (CONJUNCT2 MULT)))
               "(SUC m) * 5")
   THEN DISCH_THEN
   (\th1. ANTE_RES_THEN                       % ~NEG ...     %
   (\th2. DISCH_THEN                          % MP i_h ~NEG  %
    \th3. DISCH_THEN                          % SUC n <= ... %
    \th4. (                                   % mpc t = ... %
   (\th5. ACCEPT_TAC			      % m <= ...    %
           (MATCH_MP Next_interval'
	    (CONJ	
             (MATCH_MP(MATCH_MP th2 th5)th4)  % PRE t < t' < t+5*m ==>%

	     (MATCH_MP                         % PRE(t+5*n)<t'<t+5*(m+1) %
	      (rr(nth_o_lemma . 
	          (map ((\thl. \n. el n (CONJUNCTS thl))
		        (MATCH_MP(MATCH_MP(MATCH_MP loop1_nth_state th1)th5)th4))
		       [1;7]))
	         (SPEC "t+(5*m)" loop1_nonmajor))
	      (MATCH_MP(MATCH_MP(SPECL["m:num"; "atom_bits(arg(PRE t))"]nth_DEC_NOT_ZERO)
			        th1)
		       (MATCH_MP OR_LESS th3)))))
   )
    (MATCH_MP LESS_IMP_LESS_OR_EQ (MATCH_MP OR_LESS th3)))
   ) th1)
 ]);;

let loop2_nth_state = TAC_PROOF
((DEC28_assum1.DEC28_assum2.hyp loop2_state,
 "!n t.
   (~(NEG(iVal(Bits28(atom_bits(arg(PRE t))))))) ==>
   (n <= (pos_num_of(iVal(Bits28(atom_bits(arg(PRE t))))))) ==>
   (mpc t = #001001000) ==>
      (mpc(t + (5*n)) = #001001000) /\
      ((s0:^w9_mvec)(t + (5*n)) = s0 t) /\
      ((s1:^w9_mvec)(t + (5*n)) = s1 t) /\
      ((s2:^w9_mvec)(t + (5*n)) = s2 t) /\
      ((s3:^w9_mvec)(t + (5*n)) = s3 t) /\
      ((memory:^m14_32_mvec)(t + (5*n)) = memory t) /\
      ((arg:^w32_mvec)(PRE(t + (5*n))) = nth n (DEC28 o atom_bits)(arg(PRE t))) /\
      ((buf2:^w32_mvec)(PRE(t + (5*n))) = buf2(PRE t)) /\
      ((s:^w14_mvec)(PRE(t + (5*n))) = s(PRE t)) /\
      ((e:^w14_mvec)(PRE(t + (5*n))) = e(PRE t)) /\
      ((c:^w14_mvec)(PRE(t + (5*n))) = c(PRE t)) /\
      ((d:^w14_mvec)(PRE(t + (5*n))) = d(PRE t)) /\
      ((free:^w14_mvec)(PRE(t + (5*n))) = free(PRE t)) /\
      ((x1:^w14_mvec)(PRE(t + (5*n))) = nth n (cdr_bits o (memory t))(x1(PRE t))) /\
      ((x2:^w14_mvec)(PRE(t + (5*n))) = x2(PRE t)) /\
      ((car:^w14_mvec)(PRE(t + (5*n))) = car(PRE t)) /\
      ((parent:^w14_mvec)(PRE(t + (5*n))) = parent(PRE t)) /\
      ((root:^w14_mvec)(PRE(t + (5*n))) = root(PRE t)) /\
      ((y1:^w14_mvec)(PRE(t + (5*n))) = y1(PRE t)) /\
      ((y2:^w14_mvec)(PRE(t + (5*n))) = y2(PRE t))"),
 INDUCT_TAC
 THEN GEN_TAC
 THENL
 [ DISCH_THEN (K ALL_TAC)
   THEN DISCH_THEN (K ALL_TAC)
   THEN prt[MULT_CLAUSES; ADD_CLAUSES; nth]
   THEN DISCH_THEN SUBST1_TAC
   THEN rt[]
 ; SUBST1_TAC ((porr[ADD_ASSOC]           % rewrite "t+(5*(SUC n))" %
                o (AP_TERM "$+ t")
		o (porr[MULT_SYM])
		o (REWR_CONV (CONJUNCT2 MULT)))
               "(SUC n) * 5")
   THEN port[nth]
   THEN DISCH_THEN
   (\a2. DISCH_THEN                         % ~NEG ... %
    \a3. DISCH_THEN                         % SUC n <= %
    \a6. ASSUME_TAC a2                      % mpc t =  %
         THEN ((\a4. ASSUME_TAC a4          % n < ...  %
	             THEN ANTE_RES_THEN
		    (\a7. ASSUME_TAC        % MP (ind assum) a2 %
		      (SUBS
		       (CONJUNCTS
		        (MATCH_MP
		         (MATCH_MP a7 (MATCH_MP LESS_IMP_LESS_OR_EQ a4))
		         a6))
		       (SPEC "t+(5*n)" loop2_state))
		      )
		    a2)
	       (MATCH_MP OR_LESS a3)))
                                    % resolve nth_DEC_NOT_ZERO  %
                                    % with asm's, then use on   %
                                    % loop2_state assum to get rewrites %
   THEN IMP_RES_n_THEN 2 (ANTE_RES_THEN (port1 o (rr[]))
				    o (porr[SYM_RULE nth_o_lemma])
				    o (MATCH_MP NOT_F))
        (SPECL ["n:num"; "atom_bits(arg(PRE t))"]nth_DEC_NOT_ZERO)
   THEN port[o_THM]
   THEN rt[]
 ]);;

let loop2_nth_nonmajor = TAC_PROOF
((DEC28_assum1.DEC28_assum2.hyp loop2_nonmajor,
  "!n t.
   (~(NEG(iVal(Bits28(atom_bits(arg(PRE t))))))) ==>
   (n <= (pos_num_of(iVal(Bits28(atom_bits(arg(PRE t))))))) ==>
   (mpc t = #001001000) ==>
   !t'. (PRE t) < t' /\ t' < (t + (5*n)) ==>
        ~(is_major_state mpc t')"),
 INDUCT_TAC
 THEN GEN_TAC
 THENL
 [ prt[MULT_CLAUSES; ADD_CLAUSES]
   THEN STRIP_TAC
   THEN STRIP_TAC
   THEN STRIP_TAC
   THEN port[theorem `mu-prog_level` `Empty_range`]
   THEN rt[]
 ; SUBST1_TAC ((porr[ADD_ASSOC]           % rewrite "t+(5*(SUC n))" %
                o (AP_TERM "$+ t")
		o (porr[MULT_SYM])
		o (REWR_CONV (CONJUNCT2 MULT)))
               "(SUC n) * 5")
   THEN DISCH_THEN
   (\th1. ANTE_RES_THEN                       % ~NEG ...     %
   (\th2. DISCH_THEN                          % MP i_h ~NEG  %
    \th3. DISCH_THEN                          % SUC n <= ... %
    \th4. (                                   % mpc t = ... %
   (\th5. ACCEPT_TAC			      % n <= ...    %
           (MATCH_MP Next_interval'
	    (CONJ	
             (MATCH_MP(MATCH_MP th2 th5)th4)  % PRE t < t' < t+5*n ==>%
	     (MATCH_MP                          % PRE(t+5*n)<t'<t+5*(n+1) %
	      (rr(nth_o_lemma . 
	          (map ((\thl. \n. el n (CONJUNCTS thl))
		        (MATCH_MP(MATCH_MP(MATCH_MP loop2_nth_state th1)th5)th4))
		       [1;7]))
	         (SPEC "t+(5*n)" loop2_nonmajor))
	      (MATCH_MP(MATCH_MP(SPECL["n:num"; "atom_bits(arg(PRE t))"]nth_DEC_NOT_ZERO)
			        th1)
		       (MATCH_MP OR_LESS th3)))))
   )
    (MATCH_MP LESS_IMP_LESS_OR_EQ (MATCH_MP OR_LESS th3)))
   ) th1)
 ]);;


% ================================================================= %
% loop_test_lemma =                                                 %
% .... |- atom_bits(nth n(DEC28 o atom_bits)(arg(PRE t))) =         %
%         ZERO28                                                    %
% ================================================================= %
let loop_test_lemma = 
((porr[SYM_RULE
    (ASSUME "n=(pos_num_of(iVal(Bits28(atom_bits(arg(PRE t))))))" )])
 o (porr[SYM_RULE nth_o_lemma])
 o UNDISCH
 o (SPEC "atom_bits(arg(PRE t))"))
(theorem `loop_proofs` `loop_terminates_lemma`);;


% ================================================================= %
% ....... |- (atom_bits(arg(PRE(t + (5 * n)))) = ZERO28) /\         %
%            (mpc(t + (5 * n)) = #000111000) /\                     %
%            (s0(t + (5 * n)) = s0 t) /\                            %
%            (s1(t + (5 * n)) = s1 t) /\                            %
%            (s2(t + (5 * n)) = s2 t) /\                            %
%            (s3(t + (5 * n)) = s3 t) /\                            %
%            (memory(t + (5 * n)) = memory t) /\                    %
%            (arg(PRE(t + (5 * n))) =                               %
%             nth n(DEC28 o atom_bits)(arg(PRE t))) /\              %
%            (buf2(PRE(t + (5 * n))) = buf2(PRE t)) /\              %
%            (s(PRE(t + (5 * n))) = s(PRE t)) /\                    %
%            (e(PRE(t + (5 * n))) = e(PRE t)) /\                    %
%            (c(PRE(t + (5 * n))) = c(PRE t)) /\                    %
%            (d(PRE(t + (5 * n))) = d(PRE t)) /\                    %
%            (free(PRE(t + (5 * n))) = free(PRE t)) /\              %
%            (x1(PRE(t + (5 * n))) =                                %
%             nth n(cdr_bits o (memory t))(x1(PRE t))) /\           %
%            (x2(PRE(t + (5 * n))) = x2(PRE t)) /\                  %
%            (car(PRE(t + (5 * n))) = car(PRE t)) /\                %
%            (parent(PRE(t + (5 * n))) = parent(PRE t)) /\          %
%            (root(PRE(t + (5 * n))) = root(PRE t)) /\              %
%            (y1(PRE(t + (5 * n))) = y1(PRE t)) /\                  %
%            (y2(PRE(t + (5 * n))) = y2(PRE t))                     %
% ================================================================= %
let state_prover test_lemma thm = 
let asm = (mk_comb
          o ((\th. (mk_comb ("$=:num->num->bool", (snd o dest_comb) th))) # I)
          o dest_comb o fst o dest_imp o snd o dest_imp
          o snd o strip_forall o concl) thm
in
(((\th. CONJ
      (((porr[test_lemma])
	o (AP_TERM "atom_bits")
	o CONJUNCT1
	o CONJUNCT2 o CONJUNCT2 o CONJUNCT2
	o CONJUNCT2 o CONJUNCT2 o CONJUNCT2)
       th)
      th)
 o UNDISCH
 o UNDISCH
 o (porr[IMP_CLAUSES])
 o (porr[LESS_EQ_REFL])
 o (SUBS[SYM_RULE
    (ASSUME asm)])
 o SPEC_ALL) thm);;

% ================================================================= %
% ....... |- !t'.                                                   %
%             (PRE t) < t' /\ t' < (t + (5 * n)) ==>                %
%             ~is_major_state mpc t'                                %
% ================================================================= %
let nonmajor_prover thm =
let asm = (mk_comb
          o ((\th. (mk_comb ("$=:num->num->bool", (snd o dest_comb) th))) # I)
          o dest_comb o fst o dest_imp o snd o dest_imp
          o snd o strip_forall o concl) thm
in 					
((UNDISCH
 o UNDISCH
 o (porr[IMP_CLAUSES])
 o (porr[LESS_EQ_REFL])
 o (SUBS[SYM_RULE
    (ASSUME asm)])
 o SPEC_ALL) thm);;

save_thm (`loop1_nth`, CONJ (state_prover
			     ((UNDISCH_ALL o (SPEC "m:num")
					   o (GEN "n:num")
					   o DISCH_ALL) loop_test_lemma)
			     loop1_nth_state)
		            (nonmajor_prover loop1_nth_nonmajor));;
save_thm (`loop2_nth`, CONJ (state_prover loop_test_lemma loop2_nth_state)
		            (nonmajor_prover loop2_nth_nonmajor));;

timer false;;
close_theory ();;
print_theory `-`;;
