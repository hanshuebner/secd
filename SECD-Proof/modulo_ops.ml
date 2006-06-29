% SECD verification                                                 %
%                                                                   %
% FILE:                modulo_ops.ml                                %
%                                                                   %
% DESCRIPTION:                                                      %
% This theory merely introduces the constant names for the          %
% modulo 28 arithmetic operations performed by the secd's ALU.      %
% These names are used in both the rt level spec, as well as        %
% the top level spec, and thus for this stage of proof, no          %
% definition for the terms is necessary.                            %
% The decriment operation will need definition, however, for        %
% proof of the LD instruction.                                      %
%                                                                   %
% USES FILES:   integer library                                     %
%                                                                   %
% Brian Graham 89.10.06                                             %
%                                                                   %
% Modifications:                                                    %
% 10.04.91 - BtG - updated to HOL12                                 %
% ================================================================= %
new_theory `modulo_ops`;;

load_library `integer`;;

loadt `COND_CASES_THEN`;;
loadt `ABBREV_TAC`;;
%=================================================================%
% We create new constants for the modulo arithmetic operations    %
% that the machine executes.  The definition of these operations  %
% will propagate through from the lower level definitions:        %
% in proving the alu, we will show that the abstraction to        %
% integers and operations performed on them constitutes a modulo  %
% arithmetic operation.                                           %
%=================================================================%
timer true;;

% ================================================================= %
% Specify a partial function to map positive integers to num's.     %
% ================================================================= %
let pos_num_of = 
 let exists_rep = prove
 ("!n. ?N. n,0 = REP_integer N",
  GEN_TAC
  THEN EXISTS_TAC "ABS_integer (n,0)"
  THEN SYM_TAC
  THEN port[SYM_RULE integer_ISO_DEF]
  THEN port[IS_INTEGER_DEF]
  THEN DISJ1_TAC
  THEN EXISTS_TAC "n:num"
  THEN REFL_TAC
 )
 in
 let exists_fcn = prove
 ("?f. !n. f(INT n) = n",
  port[INT_DEF]
  THEN EXISTS_TAC "\i. FST (REP_integer (i))"
  THEN GEN_TAC
  THEN BETA_TAC
  THEN (port1 o SYM o SELECT_RULE o SPEC_ALL) exists_rep
  THEN port[FST]
  THEN REFL_TAC
 )
 in
 new_specification `pos_num_of` [`constant`,`pos_num_of`] exists_fcn;;

% ================================================================= %
% To define modulo operations, we map integers to the cyclic group  %
% (?) that can be represented by n bits.  First do a MOD to the     %
% magnitude, then map to the appropriate integer value.             %
% ================================================================= %
let normalize = new_definition
 (`normalize`, "normalize n b = b MOD (2 EXP n)");;

let norm28 = new_definition
(`norm28`,
 "norm28 i = (NEG i)
             => let n' = normalize 28 (pos_num_of(neg i))
                in
                (n' <= (2 EXP 27) => neg(INT n')
                                   | INT((2 EXP 28) - n'))
              | let n' = normalize 28 (pos_num_of i)
                in
                (n' <  (2 EXP 27) => INT n'
                                   | neg(INT((2 EXP 28) - n')))"
 );;

let modulo_28_Dec = new_definition
(`modulo_28_Dec`,
 "modulo_28_Dec i1 = norm28 (i1 minus (INT 1))");;

let modulo_28_Add = new_infix_definition
(`modulo_28_Add`,
 "$modulo_28_Add i1 i2 = norm28 (i1 plus i2)");;

let modulo_28_Sub = new_infix_definition
(`modulo_28_Sub`,
 "$modulo_28_Sub i1 i2 = norm28 (i1 minus i2)");;

close_theory();;

% ================================================================= %
% |- !n. 0 <= n                                                     %
% ================================================================= %
let ZERO_LESS_EQ =
  GEN_ALL(rr[SPECL["n:num";"0"]NOT_LESS]NOT_LESS_0);;

% ================================================================= %
let LESS_LESS_ADD = prove
("!n m. (n < m) ==> !p. n < (m + p)",
 REPEAT GEN_TAC
 THEN STRIP_TAC
 THEN INDUCT_TAC
 THENL
 [ port[ADD_CLAUSES] THEN art[]
 ; port[ADD_CLAUSES]
   THEN IMP_RES_TAC LESS_SUC
 ]);;

% ================================================================= %
% |- 0 < m ==> (?n. m = SUC n)                                      %
% ================================================================= %
let NOT_ZERO_SUC =
  DISCH_ALL (rr[SYM_RULE(MATCH_MP (LESS_NOT_EQ) (ASSUME "0 < m"))]
               (SPEC_ALL num_CASES));;


%<
% ================================================================= %
% built in in version 12                                            %
% ================================================================= %
let LESS_EQ_MONO = prove_thm
(`LESS_EQ_MONO`,
 "!n m. (SUC n) <= (SUC m) = (n <= m)",
 REPEAT GEN_TAC
 THEN port[LESS_OR_EQ]
 THEN port[LESS_MONO_EQ;INV_SUC_EQ]
 THEN REFL_TAC
 );;

% ================================================================= %
% built in in version 12                                            %
% ================================================================= %
let SUB_MONO_EQ = prove
("!n m. (SUC n) - (SUC m) = n - m",
 INDUCT_TAC
 THENL
 [ port[SUB]
   THEN rt[LESS_0]
 ; port[SUB]
   THEN art[LESS_MONO_EQ]
 ]
 );;

% ================================================================= %
% built in in version 12                                            %
% ================================================================= %
let ADD_SUB = prove
( "!x y. (x+y)-y = x",
 GEN_TAC
 THEN INDUCT_TAC
 THENL
 [ rt[ADD_CLAUSES;SUB_0]
 ; port[ADD_CLAUSES]
   THEN art[SUB_MONO_EQ]
 ]);;
>%

% ================================================================= %
let SUB_SUC_LESS_EQ = prove
("!n m. (n - (SUC m)) <= (n - m)",
 INDUCT_TAC
 THENL
 [ rt[SUB;LESS_EQ_REFL]
 ; GEN_TAC
   THEN port[SUB]
   THEN COND_CASES_TAC
   THENL
   [ rt[ZERO_LESS_EQ]
   ; COND_CASES_THEN (ASSUME_TAC o (rr[]))
     THENL
     [ IMP_RES_TAC LESS_SUC
       THEN RES_TAC
     ; port[LESS_EQ_MONO]
       THEN art[]
     ]
   ]
 ]);;

% ================================================================= %
let SUB_NONZERO = prove
( "!n m. (n < m) ==> (0 < (m - n))",
 GEN_TAC
 THEN INDUCT_TAC
 THENL
 [ rt[NOT_LESS_0]
 ; rt[SUB]
   THEN STRIP_TAC
   THEN IMP_RES_THEN (ASSUME_TAC o (rr[LESS_EQ_MONO]))LESS_OR
   THEN IMP_RES_THEN (port1) NOT_LESS
   THEN rt[LESS_0]
 ]);;

% ================================================================= %
% THEOREMS ABOUT MOD and DIV                                        %
% ================================================================= %

% ================================================================= %
% Quotients and remainders exist.                                   %
% ================================================================= %
let EXISTS_q_r = prove
("!k n. (0 < n) ==>  ?r q. (k = (q * n) + r) /\ r < n",
 INDUCT_TAC
 THEN STRIP_TAC
 THEN STRIP_TAC
 THENL
 [ EXISTS_TAC "0"
   THEN EXISTS_TAC "0"
   THEN art[ADD_CLAUSES;MULT_CLAUSES]
 ; RES_THEN(CHOOSE_THEN (CHOOSE_THEN STRIP_ASSUME_TAC))
   THEN EXISTS_TAC "(SUC r = n) => 0 | (SUC r)"
   THEN EXISTS_TAC "(SUC r = n) => SUC q | q"
   THEN COND_CASES_THEN (ASSUME_TAC o (rr[]))
   THEN art[ADD_CLAUSES]
   THENL
   [ port[MULT_CLAUSES]
     THEN port[SYM(CONJUNCT2(CONJUNCT2(CONJUNCT2 ADD_CLAUSES)))]
     THEN art[]
   ; MATCH_MP_TAC LESS_SUC_EQ_COR
     THEN art[]
   ]
 ]);;

% ================================================================= %
% MOD result is bounded                                             %
% ================================================================= %
let MOD_LESS =
 (GEN_ALL o DISCH_ALL
	  o GEN_ALL
	  o CONJUNCT2
	  o SPEC_ALL
	  o UNDISCH
	  o SPEC_ALL) DIVISION;;

% ================================================================= %
% THEOREMS ABOUT EXP                                                %
% ================================================================= %

% ================================================================= %
% 2 EXP n is always greater than 0                                  %
% ================================================================= %
let EXP_POS = prove
( "!n. 0 < (2 EXP n)",
 INDUCT_TAC
 THEN port[EXP]
 THEN in_conv_tac num_CONV
 THEN port[LESS_0]
 THEN prt[MULT_CLAUSES]
 THEN port[SYM(num_CONV "2")]
 THEN IMP_RES_THEN (ASSUME_TAC o (rr[ADD_CLAUSES]) o (SPEC "2 EXP n") o GEN_ALL)
                   LESS_MONO_ADD
 THEN IMP_RES_TAC LESS_TRANS
 );;

% ================================================================= %
let EXP_INCREASING = prove_thm
(`EXP_INCREASING`,
 "!m. (2 EXP m) < (2 EXP (SUC m))",
 port[EXP]
 THEN port[TIMES2]
 THEN GEN_TAC
 THEN MATCH_MP_TAC LESS_ADD_NONZERO
 THEN SYM_TAC
 THEN MATCH_MP_TAC LESS_NOT_EQ
 THEN MATCH_ACCEPT_TAC EXP_POS
 );;
 
% ================================================================= %
% THEOREMS ABOUT integers                                           %
% ================================================================= %

% ================================================================= %
% This reproves Konrad's theorem, a bit more easily.                %
% It proves that both zero's are identical.                         %
% ================================================================= %
let TWO_ZEROS = prove_thm
(`TWO_ZEROS`,
 "neg(INT 0) = INT 0",
 rt[neg_IS_TIMES_neg1; TIMES_ZERO]);;

% ================================================================= %
% The subtraction of zero occurs often in the definition of iVal,   %
% when it is applied to a non-negative integer.                     %
% INT 0 is the identity for minus.                                  %
% ================================================================= %
let MINUS_ID = prove_thm
(`MINUS_ID`,
 "!i. i minus (INT 0) = i",
 rt[MINUS_DEF; TWO_ZEROS; PLUS_ID_LEMMA]
 );;

% ================================================================= %
% This theorem translates less for nums to the fact that the        %
% minus operation of the corresponding INT's is negative.           %
% ================================================================= %
let LESS_MINUS_LEMMA = prove_thm
(`LESS_MINUS_LEMMA`,
 "(x < y) ==> (NEG ((INT x) minus (INT y)))",
 port[NUM_LESS_IS_INT_BELOW]
 THEN port[BELOW_DEF]
 THEN DISCH_THEN
 (\th. port[NEG_DEF]
       THEN port[MINUS_DEF]
       THEN port[SYM_RULE PLUS_DIST_INV_LEMMA]
       THEN port[NEG_NEG_IS_IDENTITY]
       THEN port[SYM_RULE MINUS_DEF]
       THEN ACCEPT_TAC th)
 );;

% ================================================================= %
% An integer cannot be both positive and negative.                  %
% ================================================================= %
let POS_NOT_NEG = prove_thm
(`POS_NOT_NEG`,
 "POS i ==> ~(NEG i)",
 port[NON_NEG_INT_IS_NUM; POS_DEF]
 THEN DISCH_THEN
      (CHOOSE_THEN (\th. EXISTS_TAC "SUC n" THEN ACCEPT_TAC th )));;

% ================================================================= %
% NEG_NOT_POS =                                                     %
% |- NEG i ==> ~POS i                                               %
% ================================================================= %
let NEG_NOT_POS = save_thm
(`NEG_NOT_POS`,
 DISCH_ALL (NEG_DISCH "POS i" (UNDISCH (UNDISCH POS_NOT_NEG))));;

% ================================================================= %
% ~NEG is equivalent to POS or ZERO                                 %
% ================================================================= %
let nonNEG_POS_OR_ZERO = prove_thm
(`nonNEG_POS_OR_ZERO`,
 "!i. ~NEG i = POS i \/ (i = INT 0)",
 port[NON_NEG_INT_IS_NUM; POS_DEF]
 THEN GEN_TAC
 THEN EQ_TAC
 THEN STRIP_TAC
 THENL
 [ DISJ_CASES_THEN2 (\th. SUBST_ALL_TAC th THEN art[])
		    (\th. CHOOSE_THEN SUBST_ALL_TAC th
			  THEN DISJ1_TAC
			  THEN poart[]
			  THEN EXISTS_TAC "n':num"
			  THEN REFL_TAC)
		    (SPEC "n:num" num_CASES)
 ; EXISTS_TAC "SUC n" THEN art[]
 ; EXISTS_TAC "0" THEN art[]
 ]);;

% ================================================================= %
% positive and negative integers are distinct.                      %
% ================================================================= %
let NEQ_POS_NEG = prove_thm
(`NEQ_POS_NEG`,
 "POS i /\ NEG j ==> ~(i = j)",
 STRIP_TAC
 THEN DISCH_THEN SUBST_ALL_TAC
 THEN IMP_RES_TAC NEG_NOT_POS);;

% ================================================================= %
% non-negative and negative integers are distinct.                  %
% ================================================================= %
let NEQ_NON_NEG_NEG = prove_thm
(`NEQ_NON_NEG_NEG`,
 "(~NEG i) /\ NEG j ==> ~(i = j)",
 STRIP_TAC
 THEN DISCH_THEN SUBST_ALL_TAC
 THEN RES_TAC);;

% ================================================================= %
let NOT_NEG_INT = prove_thm
(`NOT_NEG_INT`,
 "!n. ~NEG(INT n)",
 port[NON_NEG_INT_IS_NUM]
 THEN GEN_TAC
 THEN EXISTS_TAC "n:num"
 THEN REFL_TAC
 );;

% ================================================================= %
% |- !n.~POS(neg(INT n))                                            %
% ================================================================= %
let NOT_POS_NEG_INT = save_thm
(`NOT_POS_NEG_INT`, porr[NEG_DEF] NOT_NEG_INT);;

% ================================================================= %
let NOT_POSNEG_ZERO = prove_thm
(`NOT_POSNEG_ZERO`,
 "~NEG(INT 0) /\ ~POS(INT 0)",
 rt[NOT_NEG_INT]
 THEN SUBST1_TAC (SYM TWO_ZEROS)
 THEN rt[NOT_POS_NEG_INT]
 );;

% ================================================================= %
let POS_INT = prove_thm
(`POS_INT`,
 "!n.POS(INT(SUC n))",
 port[POS_DEF]
 THEN GEN_TAC
 THEN EXISTS_TAC "n:num"
 THEN REFL_TAC
 );;

% ================================================================= %
let NEG_INT = prove_thm
(`NEG_INT`,
 "!n.NEG(neg(INT(SUC n)))",
 port[NEG_DEF]
 THEN port[NEG_NEG_IS_IDENTITY]
 THEN ACCEPT_TAC POS_INT
 );;

% ================================================================= %
let NEG_below_NONNEG = prove_thm
(`NEG_below_NONNEG`,
 "((neg(INT n)) below (INT m)) \/
    ((n = 0) /\ (m = 0))",
 port[BELOW_DEF]
 THEN port[MINUS_DEF]
 THEN port[NEG_NEG_IS_IDENTITY]
 THEN port[NUM_ADD_IS_INT_ADD]
 THEN DISJ_CASES_THEN2 (\th. ASSUME_TAC th
			     THEN IMP_RES_THEN port1 ADD_EQ_0
			     THEN rt[])
                       (\th. CHOOSE_THEN SUBST1_TAC th
			     THEN rt[POS_INT])
      (SPEC "m+n" num_CASES)
 );;

% ================================================================= %
let NEG_BELOW_POS_SUC = prove
( "!n m. (neg(INT n)) below (INT (SUC m))",
 port[BELOW_DEF]
 THEN port[MINUS_DEF]
 THEN port[NEG_NEG_IS_IDENTITY]
 THEN port[NUM_ADD_IS_INT_ADD]
 THEN port[ADD_CLAUSES]
 THEN MATCH_ACCEPT_TAC POS_INT
 );;

% ================================================================= %
let NEG_SUC_BELOW_POS = prove
( "!n m. (neg(INT (SUC n))) below (INT m)",
 port[BELOW_DEF]
 THEN port[MINUS_DEF]
 THEN port[NEG_NEG_IS_IDENTITY]
 THEN port[NUM_ADD_IS_INT_ADD]
 THEN port[ADD_CLAUSES]
 THEN MATCH_ACCEPT_TAC POS_INT
 );;

% ================================================================= %
let NEG_BELOW = prove
( "!n m. (neg(INT n)) below (neg(INT m)) = (m < n)",
 port[neg_REV_BELOW]
 THEN rt[NUM_LESS_IS_INT_BELOW]
 );;


% ================================================================= %
% THEOREMS ABOUT pos_num_of                                         %
% ================================================================= %

% ================================================================= %
% The function pos_num_of is well defined when applied to non       %
% negative integers.                                                %
% integer, pos_num_of                                               %
% ================================================================= %
let NON_NEG_pos_num_of_lemma = prove_thm
(`NON_NEG_pos_num_of_lemma`,
 "~NEG i ==> (?m. m = pos_num_of i)",
 port[NON_NEG_INT_IS_NUM]
 THEN DISCH_THEN (CHOOSE_THEN SUBST1_TAC)
 THEN port[pos_num_of]
 THEN EXISTS_TAC "n:num"
 THEN REFL_TAC
 );;

% ================================================================= %
let norm28_lemma = prove_thm
(`norm28_lemma`,
 "(norm28 (INT n) =
   let n' = normalize 28 n
   in
   (n' < (2 EXP 27) => INT n' | neg(INT((2 EXP 28)-n')))) /\
  (norm28 (neg(INT n)) =
   let n' = normalize 28 n
   in
   (n' <= (2 EXP 27) => neg(INT n') | INT ((2 EXP 28) - n')))",
 port[norm28]
 THEN CONJ_TAC
 THENL
 [ rt[NOT_NEG_INT]
 ; DISJ_CASES_THEN2 SUBST1_TAC (CHOOSE_THEN SUBST1_TAC) (SPEC "n:num" num_CASES)
   THENL
   [ port[TWO_ZEROS]
     THEN rt[NOT_NEG_INT]
     THEN port[pos_num_of]
     THEN port[normalize]
     THEN port1(MATCH_MP (SPEC "2 EXP 28" ZERO_MOD) (SPEC "28" EXP_POS) )
     THEN port[LET_DEF] THEN in_conv_tac BETA_CONV
     THEN rt[EXP_POS; ZERO_LESS_EQ; TWO_ZEROS]
   ; rt[NEG_INT;NEG_NEG_IS_IDENTITY]
   ]
 ]
 THEN port[pos_num_of]
 THEN REFL_TAC
 );;
 
% ================================================================= %
% normalize_inrange = |- !m. (normalize n m) < (2 EXP n)            %
% ================================================================= %
let normalize_inrange =
 porr[SYM_RULE normalize](MATCH_MP MOD_LESS (SPEC_ALL EXP_POS));;

% ================================================================= %
% Specialized result for final theorem proof.                       %
% ================================================================= %
let lemma1 = prove
( "!n m. ~(n < m) ==> ((m + m) - n) <= m",
 INDUCT_TAC
 THENL
 [ GEN_TAC
   THEN DISCH_THEN (\th.SUBST1_TAC (SYM (rr[th](SPEC "m:num" LESS_0_CASES))))
   THEN rt[ADD_CLAUSES;SUB_0;LESS_EQ_REFL]
 ; GEN_TAC
   THEN STRIP_TAC
   THEN IMP_RES_THEN (DISJ_CASES_TAC o (rr[LESS_OR_EQ]))  NOT_LESS
   THENL
   [ IMP_RES_THEN (ASSUME_TAC o (rr[LESS_MONO_EQ])) LESS_SUC_NOT
     THEN RES_TAC
     THEN ASSUME_TAC (SPECL["m+m";"n:num"]SUB_SUC_LESS_EQ)
     THEN IMP_RES_THEN(IMP_RES_TAC)LESS_EQ_TRANS 
   ; art[ADD_SUB;LESS_EQ_REFL]
   ]
 ]);;

% ================================================================= %
% A specialized lemma used for the proof of the next theorem.       %
% ================================================================= %
let lemma2 = prove
("!m.(0 < m) ==> !n.(((m + m) - n = m) = (n = m))",
 INDUCT_TAC
 THENL
 [ rt[NOT_LESS_0]
 ; STRIP_TAC
   THEN INDUCT_TAC
   THENL
   [ port[SUB_0]
     THEN port[ADD_INV_0_EQ]
     THEN IMP_RES_THEN (\th. port1 th THEN port1 (SYM_RULE th)) LESS_NOT_EQ
     THEN REFL_TAC
   ; prt[ADD_CLAUSES; SUB_MONO_EQ; SUB]
     THEN COND_CASES_THEN (ASSUME_TAC o (rr[]))
     THENL
     [ IMP_RES_THEN (port1) LESS_NOT_EQ
       THEN rt[INV_SUC_EQ]
       THEN DISCH_THEN SUBST_ALL_TAC
       THEN IMP_RES_THEN (ASSUME_TAC o (SPEC "m:num"))
                         (SPECL["m+m";"m:num"] LESS_LESS_ADD)
       THEN IMP_RES_TAC LESS_REFL
     ; port[INV_SUC_EQ]
       THEN IMP_RES_TAC NOT_LESS
       THEN SUBST1_TAC(SPECL["(m+m)-n";"m:num";"n:num"](SYM_RULE EQ_MONO_ADD_EQ))
       THEN IMP_RES_THEN port1 SUB_ADD
       THEN port[ADD_SYM]
       THEN port[EQ_MONO_ADD_EQ]
       THEN MATCH_ACCEPT_TAC EQ_SYM_EQ
     ]
   ]
  ]);;

% ================================================================= %
% The major result: hard bounds for normalized integer values.      %
% The proof is very rough, and could be significantly improved.     %
% ================================================================= %
let norm28_bounds = prove_thm
(`norm28_bounds`,
 "!n. ((neg(INT(2 EXP 27)) below norm28 n) \/
         (neg(INT(2 EXP 27)) = norm28 n)) /\
        norm28 n below INT(2 EXP 27)",
 INT_CASES_TAC
 THENL
 [ GEN_TAC
   THEN port[norm28_lemma]
   THEN CONJ_TAC
   THEN port[LET_DEF] THEN in_conv_tac BETA_CONV
   THEN ABBREV_TAC "normalize 28 n1" "n':num"
   THEN COND_CASES_THEN (ASSUME_TAC o (rr[]))
   THENL
   [ ASSUME_TAC (SPEC "27" EXP_POS)
     THEN IMP_RES_THEN (CHOOSE_THEN port1) NOT_ZERO_SUC
     THEN rt[NEG_SUC_BELOW_POS]
   ; port[NEG_BELOW]
     THEN port[num_CONV "28"]
     THEN prt[EXP;TIMES2]
     THEN IMP_RES_THEN ((DISJ_CASES_THEN2 (\th.rt[th])
					  (\th.DISJ2_TAC
					       THEN SUBST_OCCS_TAC[[1],SYM th]
					       THEN REFL_TAC))
			o (rr[LESS_OR_EQ])) lemma1
   ; port[SYM_RULE NUM_LESS_IS_INT_BELOW]
     THEN art[]
   ; ASSUME_TAC (SPEC "27" EXP_POS)
     THEN IMP_RES_THEN (CHOOSE_THEN port1) NOT_ZERO_SUC
     THEN rt[NEG_BELOW_POS_SUC]
   ]
 ; GEN_TAC
   THEN port[norm28_lemma]
   THEN CONJ_TAC
   THEN port[LET_DEF] THEN in_conv_tac BETA_CONV
   THEN ABBREV_TAC "normalize 28 n2" "n':num"
   THEN COND_CASES_THEN (ASSUME_TAC o (rr[LESS_OR_EQ]))
   THENL
   [ port[NEG_BELOW]
     THEN FIRST_ASSUM (\th. (is_disj (concl th)) => DISJ_CASES_TAC th THEN art[]
		                                 | NO_TAC)
   ; ASSUME_TAC (SPEC "27" EXP_POS)
     THEN IMP_RES_THEN (CHOOSE_THEN port1) NOT_ZERO_SUC
     THEN rt[NEG_SUC_BELOW_POS]
   ; ASSUME_TAC (SPEC "27" EXP_POS)
     THEN IMP_RES_THEN (CHOOSE_THEN port1) NOT_ZERO_SUC
     THEN rt[NEG_BELOW_POS_SUC]

   ; port[SYM_RULE NUM_LESS_IS_INT_BELOW]
     THEN port[num_CONV "28"]
     THEN prt[EXP;TIMES2]
     THEN FIRST_ASSUM (\th. (is_neg (concl th))
                            => STRIP_ASSUME_TAC (porr[DE_MORGAN_THM]th)
		             | NO_TAC)
     THEN IMP_RES_THEN ((DISJ_CASES_THEN ASSUME_TAC) o (rr[LESS_OR_EQ]) ) lemma1
     THENL
     [ art[]
     ; IMP_RES_THEN ASSUME_TAC (MATCH_MP (SPEC "2 EXP 27" lemma2)
					 (SPEC "27" EXP_POS))
       THEN RES_TAC
     ]
   ]
 ]);;

timer false;;

map save_thm
[ `ZERO_LESS_EQ`, ZERO_LESS_EQ
; `LESS_LESS_ADD`, LESS_LESS_ADD
; `SUB_MONO_EQ`, SUB_MONO_EQ
; `EXP_POS`, EXP_POS
; `NEG_BELOW_POS_SUC`, NEG_BELOW_POS_SUC
; `NEG_SUC_BELOW_POS`, NEG_SUC_BELOW_POS
; `NEG_BELOW`, NEG_BELOW
];;

print_theory `-`;;
