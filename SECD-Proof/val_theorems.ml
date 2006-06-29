% SECD verification                                                 %
%                                                                   %
% FILE:        val_theorems.ml                                      %
%                                                                   %
% DESCRIPTION:  Develops theorems about val, Val, and iVal, which   %
%               show the abstraction has many nice properties.      %
%                                                                   %
% USES FILES:				                            %
%                                                                   %
% Brian Graham 03.01.91                                             %
%                                                                   %
% Modifications:                                                    %
% 16.04.91 - BtG - updated to HOL12                                 %
% 16.01.92 - BtG - DEC28 assumptions proved.                        %
% ================================================================= %
new_theory `val_theorems`;;

loadf `wordn`;;
load_library `integer`;;

map new_parent
[ `val_defs`
; `bus_theorems`
; `rt_SYS`
];;

load_theorem `bus` `bus_Induct`;;
loadt `bus_theorems`;;

map (load_definition `cu_types`)
[ `inc`
];;

load_all `modulo_ops`;;

load_definition `bus` `Width`;;
load_theorem `bus` `Width_non_zero`;;

map (load_definition `val_defs`)
[ `bv`
; `val`
; `Val`
; `iVal`
];;

map (load_theorem `dp_types`)
[ `bus32_num_fields_lemma_1`
; `Width_Bits28_Word28`
; `Width_Bits28`
; `Bits28_11`
];;
load_definition `rt_DP` `DEC28`;;

close_theory();;

timer true;;
% ***************************************************************** %
% GENERAL ARITHMETIC THEOREMS                                       %
% ***************************************************************** %

% ================================================================= %
% AP_TERM_INV = |- !f a b. ~(f a = f b) ==> ~(a = b)                %
% ================================================================= %
let AP_TERM_INV = save_thm
(`AP_TERM_INV`,
 GEN_ALL(porr[GEN_ALL(CONTRAPOS_CONV "c==>d")]
		     (DISCH_ALL (AP_TERM "f:*->**"(ASSUME "a:* = b")))));;

% ================================================================= %
% NOT_ZERO_SUC = |- 0 < m ==> (?n. m = SUC n)                       %
% ================================================================= %
let NOT_ZERO_SUC =
  DISCH_ALL (rr[SYM_RULE(MATCH_MP (LESS_NOT_EQ) (ASSUME "0 < m"))]
               (SPEC_ALL num_CASES));;

% ================================================================= %
let LESS_1_IS_0 = prove
("!n. (n < 1) = (n = 0)",
 port[num_CONV"1"]
 THEN INDUCT_TAC
 THENL
 [ rt[LESS_0]
 ; rt[LESS_MONO_EQ; NOT_LESS_0]
   THEN SYM_TAC
   THEN MATCH_MP_TAC LESS_NOT_EQ
   THEN MATCH_ACCEPT_TAC LESS_0
 ]);;

% ================================================================= %
% LESS_EQ_0_IS_0 = |- !n. n <= 0 = (n = 0)                          %
% ================================================================= %
let LESS_EQ_0_IS_0 = 
  prr[num_CONV "1"; LESS_EQ; LESS_EQ_MONO] LESS_1_IS_0;;

% ================================================================= %
let less_eq_sub_lemma = prove
("!n m. (n <= m) ==> (m - n) <= m",
 REPEAT GEN_TAC THEN STRIP_TAC THEN IMP_RES_TAC SUB_ADD
 THEN port[SYM_RULE(SPECL ["m - n"; "m:num"; "n:num"] LESS_EQ_MONO_ADD_EQ)]
 THEN poart[]
 THEN MATCH_ACCEPT_TAC LESS_EQ_ADD
 );;


% ***************************************************************** %
% val and inc THEOREMS                                              %
% ***************************************************************** %

let bv_thm = prove_thm
 (`bv_thm`,
   "(bv T = 1)  /\  (bv F = 0)",
   REWRITE_TAC [bv]);;
   
let val_0_lemma = prove_thm
(`val_0_lemma`,
 "(val 0 (Bus F b) = val 0 b) /\ (val 0 (Wire F) = 0)",
  prt[val; ADD_CLAUSES; bv_thm]
  THEN CONJ_TAC THEN REFL_TAC
 );;

% ================================================================= %
let inc_Width_lemma = prove
("!b. Width b = Width(FST(inc b))",
 INDUCT_THEN (bus_Induct) ASSUME_TAC
 THENL
 [ port[inc]
   THEN port[FST]
   THEN port[Width]
   THEN rt[]
 ; port[inc]
   THEN port[LET_DEF] THEN in_conv_tac BETA_CONV
   THEN SUBST1_TAC
        (SPEC "inc b"(SYM_RULE(INST_TYPE[":(bool)bus",":*";":bool",":**"]PAIR)))
   THEN port[UNCURRY_DEF]
   THEN in_conv_tac BETA_CONV
   THEN port[FST]
   THEN port[Width]
   THEN poart[]
   THEN rt[]
 ]);;

% ================================================================= %
let bv_11 = prove_thm
(`bv_11`,
 "!a b. (bv a = bv b) = (a = b)",
 REPEAT GEN_TAC
 THEN BOOL_CASES_TAC "a:bool"
 THEN BOOL_CASES_TAC "b:bool"
 THEN rt[bv_thm]
 THEN port[num_CONV "1"]
 THENL
 [ MATCH_ACCEPT_TAC SUC_ID
 ; MATCH_ACCEPT_TAC (SYM_RULE SUC_ID)
 ]
 );;

% ================================================================= %
let val_n_bound = prove_thm
(`val_n_bound`,
 "!b n. let m = Width b in (val n b < ((n+1) * (2 EXP m)))",
 port[LET_DEF]
 THEN BETA_TAC
 THEN INDUCT_THEN (bus_Induct) ASSUME_TAC
 THEN GEN_TAC
 THEN GEN_TAC
 THEN port[val; Width]
 THEN prt[bv;EXP]
 THENL
 [ rt[MULT_CLAUSES; ADD_CLAUSES]
   THEN port[MULT_SYM]
   THEN port[TIMES2]
   THEN port[SYM_RULE ADD1]
   THEN prt[ADD_CLAUSES]
   THEN COND_CASES_TAC
   THENL
   [ port[SYM_RULE ADD1]
     THEN prt[ADD_CLAUSES]
     THEN MATCH_ACCEPT_TAC LESS_SUC_REFL
   ; port[ADD_CLAUSES]
     THEN port[LESS_SUC_SUC]
   ]
 ; port[MULT_ASSOC]
   THEN port[porr[MULT_SYM]TIMES2]
   THEN prt[SYM_RULE ADD1; ADD_CLAUSES]
   THEN COND_CASES_TAC
   THENL
   [ prt[SYM_RULE ADD1; ADD_CLAUSES]
     THEN FIRST_ASSUM (\th. is_forall (concl th)
                         => (MATCH_ACCEPT_TAC
                            o (prr[SYM_RULE ADD1;ADD_CLAUSES])
                            o (SPEC "SUC(n+n)")) th
                          | NO_TAC)
   ; prt[ADD_CLAUSES]
     THEN port[MULT]
     THEN FIRST_ASSUM (\th. is_forall (concl th)
                         => (ASSUME_TAC
                            o (prr[SYM_RULE ADD1;ADD_CLAUSES])
                            o (SPEC "n+n")) th
                          | NO_TAC)
     THEN IMP_RES_THEN MATCH_ACCEPT_TAC LESS_LESS_ADD
   ]
 ]);;

% ================================================================= %
% val_0_bound = |- let m = Width b in (val 0 b) < (2 EXP m)         %
% ================================================================= %
let val_0_bound = save_thm
(`val_0_bound`,
  rr[ADD_CLAUSES; MULT_CLAUSES](SPECL ["b:bool bus"; "0"] val_n_bound));;

% ================================================================= %
let val_0_F_bus = save_thm
(`val_0_F_bus`,
 GEN "b:(bool)bus"(CONJUNCT1 val_0_lemma));;

% ================================================================= %
% Val_bound = |- let m = Width b in (Val b) < (2 EXP m)             %
% ================================================================= %
let Val_bound = save_thm
(`Val_bound`,
 in_conv_rule BETA_CONV
 (porr[LET_DEF](rr[SYM_RULE Val] val_0_bound)));;

% ================================================================= %
let val_n_lemma = prove
("!b n. val n b = (n * (2 EXP (Width b))) + (val 0 b)",
 INDUCT_THEN (bus_Induct) ASSUME_TAC
 THENL
 [ re_conv_tac num_CONV
   THEN prt[val; Width; EXP; MULT_CLAUSES; ADD_CLAUSES]
   THEN port[LEFT_ADD_DISTRIB] THEN prt[MULT_CLAUSES]
   THEN port[ADD_ASSOC]
   THEN rt[]
 ; REPEAT GEN_TAC
   THEN prt[val]
   THEN prt[ADD_CLAUSES]
   THEN poart[]
   THEN port[Width]
   THEN port[EXP]
   THEN SUBST_OCCS_TAC [[2],num_CONV "2"]
   THEN prt[MULT_CLAUSES; ADD_CLAUSES]
   THEN prt[RIGHT_ADD_DISTRIB; LEFT_ADD_DISTRIB]
   THEN prt[ADD_ASSOC]
   THEN REFL_TAC
 ]);;

% ================================================================= %
let inc_max_lemma = prove
("!b. SND (inc b) ==> (val 0 b = PRE (2 EXP (Width b)))",
  INDUCT_THEN (bus_Induct) ASSUME_TAC
  THENL
  [ GEN_TAC 
    THEN prt[val;inc;FST;SND;ADD_CLAUSES;Width;EXP;MULT_CLAUSES]
    THEN port[num_CONV "2"]
    THEN rt[PRE]
    THEN port[bv]
    THEN BOOL_CASES_TAC "x:bool" THEN rt[]
  ; GEN_TAC
    THEN port[inc]
    THEN port[LET_DEF] THEN in_conv_tac BETA_CONV
    THEN SUBST1_TAC
        (SPEC "inc b"(SYM_RULE(INST_TYPE[":(bool)bus",":*";":bool",":**"]PAIR)))
    THEN port[UNCURRY_DEF]
    THEN in_conv_tac BETA_CONV
    THEN prt[FST;SND]
    THEN STRIP_TAC
    THEN port[val]
    THEN prt[ADD]
    THEN port[val_n_lemma]
    THEN port[SYM_RULE inc_Width_lemma]
    THEN RES_TAC
    THEN art[]
    THEN port[bv] THEN rt[MULT_CLAUSES]
    THEN port[Width]
    THEN port[EXP]
    THEN SUBST_OCCS_TAC [[3],num_CONV "2"]
    THEN prt[MULT_CLAUSES]
    THEN ASSUME_TAC (SPEC "Width (b:bool bus)" EXP_POS)
    THEN IMP_RES_THEN (CHOOSE_THEN port1) NOT_ZERO_SUC
    THEN rt[ADD_CLAUSES;PRE]
  ]);;

% ================================================================= %
let val_inc_lemma = prove
("!b. (val 0 (FST (inc b)) = ((SND(inc b)) => 0 | SUC(val 0 b)))",
  INDUCT_THEN (bus_Induct) ASSUME_TAC
  THENL
  [ GEN_TAC 
    THEN prt[val;inc;FST;SND;ADD_CLAUSES]
    THEN port[bv]
    THEN BOOL_CASES_TAC "x:bool" THEN rt[]
    THEN in1_conv_tac num_CONV THEN REFL_TAC
  ; GEN_TAC
    THEN port[inc]
    THEN port[LET_DEF] THEN in_conv_tac BETA_CONV
    THEN SUBST1_TAC
        (SPEC "inc b"(SYM_RULE(INST_TYPE[":(bool)bus",":*";":bool",":**"]PAIR)))
    THEN port[UNCURRY_DEF]
    THEN in_conv_tac BETA_CONV
    THEN prt[FST;SND]
    THEN port[val]
    THEN prt[ADD]
    THEN port[val_n_lemma]
    THEN port[SYM_RULE inc_Width_lemma]
    THEN art[]
    THEN ASM_CASES_TAC "SND(inc b)" THEN art[]
    THENL
    [ IMP_RES_THEN port1 inc_max_lemma
      THEN port[bv]
      THEN BOOL_CASES_TAC "x:bool" THEN rt[]
      THEN rt[ADD_CLAUSES; MULT_CLAUSES]
      THEN ASSUME_TAC (SPEC "Width (b:bool bus)" EXP_POS)
      THEN IMP_RES_THEN (CHOOSE_THEN port1) NOT_ZERO_SUC
      THEN rt[PRE]
    ; rt[ADD_CLAUSES]
    ]
  ]);;

% ================================================================= %
let inc_lemma = prove
("!b. (val 0 (FST (inc b)) = SUC(val 0 b)) \/
          (val 0 (FST (inc b)) = 0) /\ (val 0 b = PRE(2 EXP (Width b)))",
 GEN_TAC
 THEN port[val_inc_lemma]
 THEN ASM_CASES_TAC "SND(inc b)" THEN art[]
 THEN IMP_RES_THEN port1 inc_max_lemma
 THEN rt[]
 );;

% ================================================================= %
let binary_rep_exists = prove
("!n. ?b. Val b = n",
 port[Val]
 THEN INDUCT_THEN INDUCTION STRIP_ASSUME_TAC
 THENL
 [ EXISTS_TAC "Wire F"
   THEN rt[val; bv; ADD_CLAUSES]
 ; STRIP_ASSUME_TAC (SPEC_ALL inc_lemma)
   THENL
   [ EXISTS_TAC "FST (inc b)"
     THEN part[]
     THEN REFL_TAC
   ; EXISTS_TAC "Bus T (FST(inc b))"
     THEN port[val]
     THEN port[bv_thm]
     THEN port[val_n_lemma]
     THEN poart[]
     THEN prt[ADD_CLAUSES; MULT_CLAUSES]
     THEN FIRST_ASSUM (\th. free_in "n:num" (concl th)
                            => SUBST1_TAC (SYM th) | NO_TAC)
     THEN poart[SYM_RULE inc_Width_lemma]
     THEN CHOOSE_THEN SUBST1_TAC
                      (MATCH_MP NOT_ZERO_SUC (SPEC "Width (b:(bool)bus)" EXP_POS))
     THEN port[PRE]
     THEN REFL_TAC
   ]
 ]);;

% ================================================================= %
let wordn_rep_exists = prove_thm
(`wordn_rep_exists`,
 "!n m. (n < (2 EXP (SUC m))) ==>
         ?b. (Width b = SUC m) /\ (Val b = n)",
 port[Val]
 THEN INDUCT_TAC
 THENL
 [ INDUCT_TAC
   THENL
   [ STRIP_TAC
     THEN EXISTS_TAC "Wire F"
     THEN rt[Width; val; bv; ADD_CLAUSES]
   ; DISCH_THEN (K ALL_TAC)
     THEN ANTE_RES_THEN STRIP_ASSUME_TAC (SPEC "SUC m" EXP_POS)
     THEN EXISTS_TAC "Bus F b"
     THEN prt[val; bv_thm; Width ]
     THEN prt[ADD_CLAUSES]
     THEN art[]
   ]
 ; GEN_TAC
   THEN DISCH_THEN
   (\th. ASSUME_TAC (MATCH_MP LESS_NOT_EQ th)
         THEN ANTE_RES_THEN
	      (CHOOSE_THEN
	       (\th1. let [th2;th3] = CONJUNCTS th1 in
		      EXISTS_TAC "FST(inc b)"
		      THEN port[SYM_RULE inc_Width_lemma]
		      THEN SUBST_ALL_TAC(SYM th3) THEN rt[th2]
		      THEN DISJ_CASES_THEN2
		           ACCEPT_TAC
			   (SUBST_ALL_TAC o CONJUNCT2)
			   (SPEC_ALL inc_lemma)
		      THEN SUBST_ALL_TAC th2))
	      (MATCH_MP SUC_LESS th))
   THEN CHOOSE_THEN SUBST_ALL_TAC
                    (MATCH_MP NOT_ZERO_SUC (SPEC "SUC m" EXP_POS))
   THEN RULE_ASSUM_TAC (rr[PRE])
   THEN UNDISCH_TAC "F"
   THEN rt[]
 ]);;

% ================================================================= %
let exists_0_rep = prove
("!m. ?b. (Width b = SUC m) /\ (Val b = 0)",
 INDUCT_THEN INDUCTION STRIP_ASSUME_TAC
 THENL
 [ EXISTS_TAC "Wire F"
   THEN rt[Width; Val; val; bv_thm; ADD_CLAUSES]
 ; EXISTS_TAC "Bus F b"
   THEN prt[Width; Val; val; bv_thm; ADD_CLAUSES]
   THEN port[SYM_RULE Val]
   THEN art[]
 ]);;

% ================================================================= %
let Val_11 = prove_thm
(`Val_11`,
 "!b b'. (Width b' = Width b) ==> ((Val b = Val b') = (b = b'))",
 INDUCT_THEN bus_Induct ASSUME_TAC
 THENL
 [ REPEAT GEN_TAC
   THEN wire_width_tac
   THEN port[Wire_11]
   THEN prt[Val; val; ADD_CLAUSES]
   THEN MATCH_ACCEPT_TAC bv_11
 ; REPEAT GEN_TAC
   THEN bus_width_tac
   THEN port[Val]
   THEN prt[val; ADD_CLAUSES]
   THEN port[val_n_lemma]
   THEN port[Bus_11]
   THEN BOOL_CASES_TAC "x:bool"
   THEN BOOL_CASES_TAC "b'':bool"
   THEN rt[bv_thm]
   THEN port[MULT_CLAUSES]
   THEN part[ADD_CLAUSES]
   THEN port[SYM_RULE Val]
   THENL
   [ port[ADD_SYM]
     THEN port[EQ_MONO_ADD_EQ]
     THEN art[]
   ; SYM_TAC
     THEN MATCH_MP_TAC LESS_NOT_EQ
     THEN FIRST_ASSUM (\th. (is_eq(concl th)) &
                           ("Width:(bool)bus->num" = fst(dest_comb(fst(dest_eq(concl th)))))
                      => port1 (SYM th) | NO_TAC)
     THEN port[MATCH_MP LESS_LESS_ADD Val_bound]
   ; MATCH_MP_TAC LESS_NOT_EQ
     THEN port[MATCH_MP LESS_LESS_ADD Val_bound]
   ; art[]
   ]
 ]);;

% ================================================================= %
% Val_Bits28_11 = |- (Val(Bits28 x) = Val(Bits28 y)) = (x = y)      %
% ================================================================= %
let Val_Bits28_11 = save_thm
(`Val_Bits28_11`,
 rr[Bits28_11]
   (prr[Width_Bits28]
       (SPECL ["Bits28 x"; "Bits28 y"] Val_11))
 );;


% ***************************************************************** %
% INTEGER THEOREMS                                                  %
% ***************************************************************** %
%<
% ================================================================= %
% REP_integer_11 =                                                  %
% |- !a a'. (REP_integer a = REP_integer a') = (a = a')             %
% REP_integer_ONTO = |- !r. is_integer r = (?a. r = REP_integer a)  %
% ABS_integer_11 =                                                  %
% |- !r r'.                                                         %
%     is_integer r ==>                                              %
%     is_integer r' ==>                                             %
%     ((ABS_integer r = ABS_integer r') = (r = r'))                 %
% ABS_integer_ONTO = |- !a. ?r. (a = ABS_integer r) /\ is_integer r %
% ABS_integer_REP_integer = |- !a. ABS_integer(REP_integer a) = a   %
% REP_integer_ABS_integer =                                         %
% |- !r. is_integer r = (REP_integer(ABS_integer r) = r)            %
% ================================================================= %
let [ REP_integer_11
    ; REP_integer_ONTO
    ; ABS_integer_11
    ; ABS_integer_ONTO
    ; ABS_integer_REP_integer
    ; REP_integer_ABS_integer
    ]  =
CONJUNCTS
(MATCH_MP
 (MATCH_MP
  (MATCH_MP  ABS_REP_THM (EXPAND_TY_DEF (integer_AXIOM)))
  (REP_integer))
 (ABS_integer));;
>%

% ================================================================= %
% plus_RIGHT_CANCELLATION =                                         %
% |- !y x z. (y plus x = z plus x) = (y = z)                        %
% ================================================================= %
let plus_RIGHT_CANCELLATION =
 GEN_ALL(IMP_ANTISYM_RULE (SPEC_ALL PLUS_RIGHT_CANCELLATION)
        (DISCH_ALL (AP_THM (AP_TERM "$plus" (ASSUME "(y:integer) = z"))
                           "x:integer")));;

% ================================================================= %
% plus_LEFT_CANCELLATION =                                          %
% |- !y x z. (x plus y = x plus z) = (y = z)                        %
% ================================================================= %
let plus_LEFT_CANCELLATION =
 porr[COMM_PLUS] plus_RIGHT_CANCELLATION;;

% ================================================================= %
% BELOW_INT_SUC_REFL = |- !n. (INT n) below (INT(SUC n))            %
% ================================================================= %
let BELOW_INT_SUC_REFL = porr[NUM_LESS_IS_INT_BELOW] LESS_SUC_REFL;;

% ================================================================= %
% NEG_BELOW_INT_SUC_REFL = |- !n. (neg(INT(SUC n))) below (neg(INT n))  %
% ================================================================= %
let NEG_BELOW_INT_SUC_REFL = porr[SYM_RULE NEG_BELOW] LESS_SUC_REFL;;

% ================================================================= %
let PLUS_INCREASING = prove
("!i n. (i below (i plus (INT n))) \/
        (i = (i plus (INT n)))",
 GEN_TAC
 THEN SUBST_OCCS_TAC [[1;3],SYM_RULE(SPEC "i:integer" (porr[COMM_PLUS]PLUS_ID))]
 THEN port[SYM_RULE(porr[COMM_PLUS]PLUS_BELOW_TRANSL)]
 THEN INDUCT_TAC
 THENL
 [ rt[]
 ; DISJ1_TAC
   THEN FIRST_ASSUM DISJ_CASES_TAC
   THENL
   [ MATCH_MP_TAC (SPECL ["INT 0"; "INT n"; "INT(SUC n)"] TRANSIT)
     THEN poart[]
     THEN rt[]
   ; IMP_RES_THEN SUBST1_TAC PLUS_LEFT_CANCELLATION
   ] THEN MATCH_ACCEPT_TAC BELOW_INT_SUC_REFL
 ]);;

% ================================================================= %
let MINUS_DECREASING = prove
("!i n. ((i minus (INT n)) below i) \/
          (i minus (INT n) = i)",
 GEN_TAC
 THEN port[MINUS_DEF]
 THEN SUBST_OCCS_TAC [[2;4],SYM_RULE(SPEC "i:integer" (porr[COMM_PLUS]PLUS_ID))]
 THEN port[SYM_RULE(porr[COMM_PLUS]PLUS_BELOW_TRANSL)]
 THEN INDUCT_TAC
 THENL
 [ rt[TWO_ZEROS]
 ; DISJ1_TAC
   THEN FIRST_ASSUM DISJ_CASES_TAC
   THENL
   [ MATCH_MP_TAC (SPECL ["neg(INT (SUC n))"; "neg(INT n)"; "INT 0"] TRANSIT)
     THEN poart[]
     THEN rt[]
     THEN port[NEG_BELOW]
     THEN MATCH_ACCEPT_TAC LESS_SUC_REFL
   ; IMP_RES_THEN SUBST1_TAC PLUS_LEFT_CANCELLATION
     THEN MATCH_ACCEPT_TAC NEG_SUC_BELOW_POS
   ]
 ]);;

% ================================================================= %
let neg_11 = prove
("!i j. (neg i = neg j) = (i = j)",
 REPEAT GEN_TAC THEN EQ_TAC
 THENL
 [ DISCH_THEN (SUBST1_TAC o (rr[NEG_NEG_IS_IDENTITY]) o (AP_TERM "neg"))
 ; DISCH_THEN SUBST1_TAC
 ]
 THEN REFL_TAC);;

% ================================================================= %
let INT_SUC_ADD1 = prove
("!n. INT(SUC n) = ((INT n) plus (INT 1))",
 port[NUM_ADD_IS_INT_ADD]
 THEN rt[ADD1]
 );;

% ================================================================= %
let INT_SUC_MINUS_ADD1 = prove
("!n m. ((INT (SUC n)) minus m) = ((INT n) minus m) plus (INT 1)",
 port[MINUS_DEF]
 THEN port[SYM_RULE ASSOC_PLUS]
 THEN port[COMM_PLUS]
 THEN port[porr[COMM_PLUS]INT_SUC_ADD1]
 THEN rt[ASSOC_PLUS]);;

% ================================================================= %
let NUM_SUB_IS_INT_MINUS = prove
("!n m. (n <= m) ==> (((INT m) minus (INT n)) = (INT(m - n)))",
 GEN_TAC
 THEN INDUCT_TAC
 THENL
 [ port[LESS_EQ_0_IS_0]
   THEN DISCH_THEN SUBST1_TAC THEN rt[SUB_0; MINUS_ID]
 ; port[LESS_OR_EQ]
   THEN STRIP_TAC
   THENL
   [ port[INT_SUC_MINUS_ADD1]
     THEN IMP_RES_THEN ((ANTE_RES_THEN port1) o (rr[LESS_EQ_MONO])) LESS_OR
     THEN port[SYM_RULE INT_SUC_ADD1]
     THEN port[INT_ONE_ONE]
     THEN port[SUB]
     THEN IMP_RES_THEN (ASSUME_TAC o (rr[LESS_EQ_MONO])) LESS_OR
     THEN IMP_RES_TAC NOT_LESS
     THEN art[]
   ; poart[]
     THEN prt[MINUS_DEF; PLUS_INVERSE; SUB_MONO_EQ]
     THEN port[rr[LESS_EQ_REFL](SPECL["m:num";"m:num"]SUB_EQ_0)]
     THEN REFL_TAC
   ]
 ]);;

% ***************************************************************** %
% iVal THEOREMS                                                     %
% ***************************************************************** %

% ================================================================= %
let iVal_F_b = prove_thm
(`iVal_F_b`,
 "!b. iVal (Bus F b) = INT(val 0 b)",
 port[iVal]
 THEN rt[bv_thm; MULT_CLAUSES; MINUS_ID]);;

% ================================================================= %
let iVal_bound = prove_thm
(`iVal_bound`,
 "!b. let n = Width b
  in (((neg(INT(2 EXP(n-1))) below iVal b) \/
       (neg(INT(2 EXP(n-1))) = iVal b)) /\
       ((iVal b) below (INT(2 EXP (n-1)))))",
 port[LET_DEF]
 THEN BETA_TAC
 THEN INDUCT_THEN (bus_Induct) ASSUME_TAC
 THEN GEN_TAC
 THEN port[Width]
 THEN port[num_CONV "1"]
 THENL 
 [ prt[LESS_0; SUB; COND_CLAUSES]
   THEN prt[iVal]
   THEN port[bv]
   THEN CONJ_TAC 
   THENL
   [ port[NEG_BELOW]
     THEN in_conv_tac num_CONV
     THEN prt[EXP; ADD_CLAUSES; MULT_CLAUSES]
     THEN in1_conv_tac num_CONV
     THEN COND_CASES_TAC
     THEN rt[LESS_0]
   ; ASSUME_TAC (SPEC "0" EXP_POS)
     THEN IMP_RES_THEN (CHOOSE_THEN port1) NOT_ZERO_SUC
     THEN rt[NEG_BELOW_POS_SUC]
   ]
 ; port[SUB_MONO_EQ]
   THEN port[SUB_0]
   THEN prt[iVal]
   THEN port[bv]
   THEN ASSUME_TAC (in_conv_rule BETA_CONV(porr[LET_DEF]val_0_bound))
   THEN CHOOSE_THEN (\th. SUBST_ALL_TAC th
		          THEN ASSUME_TAC th)
                   (SPEC "b:bool bus"
			 (INST_TYPE [":bool",":*"]
				    (Width_non_zero)))
   THEN RULE_ASSUM_TAC (rr[num_CONV "1"; SUB_MONO_EQ;SUB_0])	   
   THEN COND_CASES_TAC
   THEN CONJ_TAC
   THEN prt[MULT_CLAUSES; MINUS_ID]
   THENL
   [ port[MINUS_DEF]
     THEN port[COMM_PLUS]
     THEN port[PLUS_INCREASING]
   ; IMP_RES_THEN (CHOOSE_THEN (SUBST1_TAC o (rr[NEG_NEG_IS_IDENTITY])
                                           o (AP_TERM "neg"))
                  o (rr[NEG_DEF;POS_DEF]))
                  LESS_MINUS_LEMMA
     THEN port[NEG_SUC_BELOW_POS]
   ; ASSUME_TAC (SPEC "SUC n" EXP_POS)
     THEN IMP_RES_THEN (CHOOSE_THEN port1) NOT_ZERO_SUC
     THEN rt[NEG_SUC_BELOW_POS]
   ; port[SYM_RULE NUM_LESS_IS_INT_BELOW]
     THEN FIRST_ASSUM MATCH_ACCEPT_TAC
   ]
 ]);;

% ================================================================= %
% iVal_28_bound =                                                   %
% |- ((neg(INT(2 EXP 27))) below (iVal(Bits28 w28)) \/              %
%     (neg(INT(2 EXP 27)) = iVal(Bits28 w28))) /\                   %
%    (iVal(Bits28 w28)) below (INT(2 EXP 27))                       %
% ================================================================= %
let iVal_28_bound =
prr[PRE; SYM_RULE PRE_SUB1; num_CONV "28"]
(in_conv_rule BETA_CONV
	      (prr[LET_DEF; Width_Bits28]
	       (SPEC "Bits28 w28"  iVal_bound)));;

% ================================================================= %
let wordn_int_rep_exists = prove_thm
(`wordn_int_rep_exists`,
 "!n m. ((((neg(INT(2 EXP m))) below n) \/
          ((neg(INT(2 EXP m))) = n)) /\
        (n below (INT(2 EXP m)))) ==>
        ?b. (Width b = SUC m) /\ (iVal b = n)",
 INT_CASES_TAC
 THEN GEN_TAC
 THENL
 [ prt[SYM_RULE NUM_LESS_IS_INT_BELOW]
   THEN INDUCT_TAC
   THENL
   [ DISCH_THEN (ASSUME_TAC o (prr[EXP; num_CONV "1"]) o CONJUNCT2)
     THEN EXISTS_TAC "Wire F" THEN port[iVal; Width]
     THEN port[bv_thm] THEN port[TWO_ZEROS]
     THEN DISJ_CASES_THEN2
          (\th. SUBST1_TAC th THEN rt[])
          (CHOOSE_THEN SUBST_ALL_TAC)
     (SPEC "n1:num" num_CASES)
     THEN IMP_RES_TAC LESS_MONO_EQ
     THEN IMP_RES_TAC NOT_LESS_0
   ; DISCH_THEN (ASSUME_TAC o CONJUNCT2)
     THEN IMP_RES_THEN STRIP_ASSUME_TAC wordn_rep_exists
     THEN EXISTS_TAC "Bus F b"
     THEN prt[Width; iVal; bv_thm]
     THEN port[MULT_CLAUSES]
     THEN port[SYM_RULE Val]
     THEN poart[]
     THEN rt[MINUS_ID]
   ]
 ; port[NEG_BELOW; neg_11]
   THEN port[INT_ONE_ONE]
   THEN INDUCT_TAC
   THENL
   [ port[EXP]
     THEN port[LESS_1_IS_0]
     THEN DISCH_THEN ((DISJ_CASES_THEN2 (\th. SUBST1_TAC th
					      THEN EXISTS_TAC "Wire F")
					(\th. SUBST1_TAC (SYM th)
					      THEN EXISTS_TAC "Wire T"))
		      o CONJUNCT1)
     THEN port[iVal;Width]
     THEN rt[bv_thm]
   ; DISCH_THEN (ASSUME_TAC o (rr[SYM_RULE LESS_OR_EQ])
                            o SYM_RULE
			    o CONJUNCT1)
     THEN IMP_RES_THEN (STRIP_ASSUME_TAC o (rr[LESS_OR_EQ]))less_eq_sub_lemma
     THENL
     [ IMP_RES_THEN STRIP_ASSUME_TAC wordn_rep_exists
       THEN EXISTS_TAC "Bus T b"
       THEN port[iVal]
       THEN port[SYM_RULE Val; bv_thm; Width]
       THEN port[MULT_CLAUSES]
       THEN poart[]
       THEN rt[]
       THEN IMP_RES_THEN (port1 o SYM) NUM_SUB_IS_INT_MINUS
       THEN port[MINUS_DEF]
       THEN port[COMM_PLUS]
       THEN port[MINUS_DEF]
       THEN port[ASSOC_PLUS]
       THEN port[PLUS_INVERSE]
       THEN port[PLUS_ID]
       THEN REFL_TAC
     ; IMP_RES_TAC
       (SYM_RULE(porr[INST_TYPE[":num",":*"]EQ_SYM_EQ]
				(SPECL["p:num";"n:num";"p:num"]ADD_EQ_SUB)))
       THEN IMP_RES_THEN (SUBST_ALL_TAC o SYM) (SYM_RULE ADD_INV_0)
       THEN port[TWO_ZEROS]
       THEN EXISTS_TAC "Bus F (@b. (Width b = SUC m) /\ (Val b = 0))"
       THEN prt[iVal; bv_thm;MULT_CLAUSES; MINUS_ID; SYM_RULE Val; INT_ONE_ONE
	       ; Width; INV_SUC_EQ]
       THEN in_conv_tac SELECT_CONV
       THEN MATCH_ACCEPT_TAC exists_0_rep
     ]
   ]
 ]);;

% ================================================================= %
% This theorem proves that the definitions for the modulo arith     %
% operations return a value.                                        %
% ================================================================= %
let exists_norm28_rep = prove_thm
(`exists_norm28_rep`,
 "!i. ?b. (Width b = 28) /\ (iVal b = norm28 i)",
 GEN_TAC
 THEN in1_conv_tac num_CONV
 THEN MATCH_MP_TAC wordn_int_rep_exists
 THEN rt[norm28_bounds]
 );;

% ================================================================= %
let exists_word28_rep = prove_thm
(`exists_word28_rep`,
 "!i. ?w28. iVal(Bits28 w28) = norm28 i",
 GEN_TAC
 THEN STRIP_ASSUME_TAC (SPEC "i:integer" exists_norm28_rep)
 THEN EXISTS_TAC "Word28 b"
 THEN IMP_RES_TAC Width_Bits28_Word28
 THEN art[]
 );;

% ================================================================= %
let iVal_11 = prove_thm
(`iVal_11`,
 "!b b'. (Width b' = Width b) ==> ((iVal b = iVal b') = (b = b'))",
 INDUCT_THEN bus_Induct ASSUME_TAC
 THENL
 [ REPEAT GEN_TAC
   THEN wire_width_tac
   THEN port[Wire_11]
   THEN prt[iVal; val; ADD_CLAUSES]
   THEN rt[neg_11; INT_ONE_ONE; bv_11]
 ; REPEAT GEN_TAC
   THEN bus_width_tac
   THEN port[iVal]
   THEN port[SYM_RULE Val]
   THEN port[Bus_11]
   THEN BOOL_CASES_TAC "x:bool"
   THEN BOOL_CASES_TAC "b'':bool"
   THEN rt[bv_thm]
   THEN port[MULT_CLAUSES]
   THEN part[ADD_CLAUSES]
   THENL
   [ port[MINUS_DEF]
     THEN port[plus_RIGHT_CANCELLATION]
     THEN port[INT_ONE_ONE]
     THEN IMP_RES_THEN MATCH_ACCEPT_TAC Val_11
   ; port[MINUS_ID]
     THEN MATCH_MP_TAC (porr[CONJ_SYM; EQ_SYM_EQ] NEQ_NON_NEG_NEG)
     THEN port[NOT_NEG_INT; MATCH_MP LESS_MINUS_LEMMA Val_bound]
     THEN rt[]
   ; port[MINUS_ID]
     THEN FIRST_ASSUM
     (\th. (is_eq(concl th))
           & ("Width:(bool)bus->num" = fst(dest_comb(fst(dest_eq(concl th)))))
	   => port1 (SYM th) | NO_TAC)
     THEN MATCH_MP_TAC NEQ_NON_NEG_NEG
     THEN port[NOT_NEG_INT; MATCH_MP LESS_MINUS_LEMMA Val_bound]
     THEN rt[]
   ; prt[MINUS_ID; INT_ONE_ONE]
     THEN IMP_RES_THEN MATCH_ACCEPT_TAC Val_11
   ]   
 ]);;

% ================================================================= %
% iVal_Bits28_11 = |- (iVal(Bits28 x) = iVal(Bits28 y)) = (x = y)   %
% ================================================================= %
let iVal_Bits28_11 = save_thm
(`iVal_Bits28_11`,
 rr[Bits28_11]
   (prr[Width_Bits28]
       (SPECL ["Bits28 x"; "Bits28 y"] iVal_11))
 );;

% ***************************************************************** %
% Discharging the assumptions about DEC28                           %
% ***************************************************************** %
let DEC28_assum1 =
"!w28. (POS (iVal (Bits28 w28)))==>
        (PRE(pos_num_of(iVal(Bits28 w28))) =
           pos_num_of(iVal(Bits28((atom_bits o DEC28) w28))))"
and DEC28_assum2 =
"!w28.(POS (iVal (Bits28 w28)))==>
     ~(NEG (iVal (Bits28 ((atom_bits o DEC28) w28))))";;

% ================================================================= %
% Unfold the meaning of DEC28 to the level of integer operations.   %
% ================================================================= %
let lemma1 = prove
("iVal(Bits28(atom_bits(DEC28 w28))) =
  norm28((iVal(Bits28 w28)minus(INT 1)))",
 port[DEC28]
 THEN in1_conv_tac let_CONV
 THEN port[o_THM]
 THEN port[modulo_28_Dec]
 THEN port[bus32_num_fields_lemma_1]
 THEN in1_conv_tac SELECT_CONV
 THEN MATCH_ACCEPT_TAC exists_word28_rep
 );;

% ================================================================= %
% |- INT(SUC n) minus (INT 1) = (INT n)                             %
% ================================================================= %
let lemma2 = 
 (GEN_ALL
  o (porr[SUC_SUB1])
  o (porr[SYM_RULE(num_CONV "1")])
  o (MATCH_MP NUM_SUB_IS_INT_MINUS)
  o SPEC_ALL
  o (porr[SYM_RULE LESS_EQ_MONO]))
 ZERO_LESS_EQ;;

% ================================================================= %
% ================================================================= %
let lemma3 = TAC_PROOF
((["n < (2 EXP 27)"], "norm28 (INT n) = INT n"),
 port[norm28_lemma]
 THEN in1_conv_tac let_CONV
 THEN port[normalize]
 THEN IMP_RES_THEN
       (SUBST1_TAC
	o (MATCH_MP LESS_MOD)
	o (\th. MATCH_MP th (porr[SYM_RULE (num_CONV "28")]
				 (SPEC "27" EXP_INCREASING))))
       LESS_TRANS
 THEN art[]
 );;
 
% ================================================================= %
% |- ((neg(INT(2 EXP 27))) below (iVal(Bits28 w28)) \/              %
%     (neg(INT(2 EXP 27)) = iVal(Bits28 w28))) /\                   %
%    (iVal(Bits28 w28)) below (INT(2 EXP 27))                       %
% ================================================================= %
let lemma4 =
(CONJUNCT2
 o (porr[SUC_SUB1])
 o (SUBS[num_CONV "28"])
 o (in1_conv_rule let_CONV)
 o (porr[Width_Bits28])
 o (SPEC "Bits28 w28")
 ) iVal_bound;;

% ================================================================= %
% |- !w28.                                                          %
%     POS(iVal(Bits28 w28)) ==>                                     %
%     ~NEG(iVal(Bits28((atom_bits o DEC28)w28)))                    %
% ================================================================= %
let DEC28_thm2 = prove_thm
(`DEC28_thm2`,
 DEC28_assum2,
 port[o_THM]
 THEN port[lemma1]
 THEN GEN_TAC THEN STRIP_TAC
 THEN ASSUME_TAC lemma4
 THEN IMP_RES_THEN (CHOOSE_THEN SUBST_ALL_TAC) POS_DEF
 THEN port[lemma2]
 THEN RULE_ASSUM_TAC (rr [SYM_RULE NUM_LESS_IS_INT_BELOW])
 THEN IMP_RES_TAC
       (MATCH_MP(hd(IMP_CANON(SPECL ["n:num"; "SUC n"; "2 EXP 27"] LESS_TRANS)))
		(SPEC_ALL LESS_SUC_REFL))
 THEN port[lemma3]
 THEN MATCH_ACCEPT_TAC NOT_NEG_INT
 );;

% ================================================================= %
% |- !w28.                                                          %
%     POS(iVal(Bits28 w28)) ==>                                     %
%     (PRE(pos_num_of(iVal(Bits28 w28))) =                          %
%      pos_num_of(iVal(Bits28((atom_bits o DEC28)w28))))            %
% ================================================================= %
let DEC28_thm1 = prove_thm
(`DEC28_thm1`,
 DEC28_assum1,
 GEN_TAC THEN STRIP_TAC
 THEN port[o_THM]
 THEN port[lemma1]
 THEN ASSUME_TAC lemma4
 THEN IMP_RES_THEN (CHOOSE_THEN SUBST_ALL_TAC) POS_DEF
 THEN port[lemma2]
 THEN RULE_ASSUM_TAC (rr [SYM_RULE NUM_LESS_IS_INT_BELOW])
 THEN IMP_RES_TAC
       (MATCH_MP(hd(IMP_CANON(SPECL ["n:num"; "SUC n"; "2 EXP 27"] LESS_TRANS)))
		(SPEC_ALL LESS_SUC_REFL))
 THEN port[lemma3]
 THEN port[pos_num_of]
 THEN port[PRE]
 THEN REFL_TAC
 );;

timer false;;
print_theory `-`;;
