% SECD verification                                                 %
%                                                                   %
% FILE:        loop_proofs.ml                                       %
%                                                                   %
% DESCRIPTION:  Develops theorems about val, Val, and iVal, and     %
%               nth, that are used in solving the while loop        %
%               computation net effects at the mu-prog level.       %
%                                                                   %
% USES FILES:				                            %
%                                                                   %
% Brian Graham 01.02.90 +/-                                         %
%                                                                   %
% Modifications:                                                    %
% 06.08.91 - BtG - updated to HOL12                                 %
% 25.11.91 - BtG - updated to HOL2                                  %
% 05.01.93 - BtG - updated to HOL2.1 (SPEC_ALL after MATCH_MP)      %
% ================================================================= %
new_theory `loop_proofs`;;

map new_parent
[ `val_theorems`
; `top_SECD`
; `bus_theorems`
];;

loadf  `wordn`;;
map load_library
[ `integer`
; `unwind`
];;

% ================================================================= %
% Things needed for the following proofs...                         %
% ================================================================= %
loadt `bus_theorems`;;
load_definition `bus` `Width`;;
map (load_theorem `bus`)
[ `Wire_11`
; `Bus_11`
];;

map (load_theorem `more_arith`)
  [ `ADDR_GREATER`
  ; `ADDL_GREATER`
  ];;
load_definition `dp_types` `ZERO28`;;
map (load_theorem `dp_types`)
[ `Bits28_Word28`
; `Width_Bits28`
; `Bits28_11`
];;

map (load_definition `val_defs`)
    [ `bv`
    ; `val`
    ; `iVal`
];;
map (load_definition `top_SECD`)
[ `nth`
];;
map (load_definition `modulo_ops`)
[ `pos_num_of`
];;
map (load_theorem `modulo_ops`)
 [ `MINUS_ID`
 ; `LESS_MINUS_LEMMA`
 ; `nonNEG_POS_OR_ZERO`
 ; `NEQ_NON_NEG_NEG`
 ];;
map (load_theorem `val_theorems`)
[ `bv_thm`
; `bv_11`
];;

timer true;;
% ================================================================= %
% THEOREMS ABOUT val                                                %
% ================================================================= %

% ================================================================= %
% An equivalent definition for calculating val.  By repeated        %
% application of this equivalence at each step, we can get a        %
% definition where each bit is multiplied by the appropriate power  %
% of 2, rather than being summed and doubled at each step.  This    %
% definition is easier to compute the bound of the val function,    %
% while the original definition may be simpler for rewriting in     %
% some cases, since it avoids multiplication and EXP.               %
% ================================================================= %
let val_equiv_def = prove_thm
(`val_equiv_def`,
 "!b n . val n b = (n * (2 EXP (Width b))) + val 0 b",
 INDUCT_THEN bus_Induct ASSUME_TAC
 THEN port[val]
 THEN REPEAT GEN_TAC
 THENL
 [ port[Width]
   THEN prt[ADD_CLAUSES; EXP; MULT_CLAUSES]
   THEN port[ADD_ASSOC; MULT_SYM]
   THEN in_conv_tac num_CONV
   THEN prt[MULT_CLAUSES; ADD_CLAUSES]
   THEN REFL_TAC
 ;
   prt[ADD_CLAUSES]
   THEN poart[]
   THEN port[Width]
   THEN port[EXP]
   THEN port[ADD_ASSOC]
   THEN port[MULT_ASSOC]
   THEN port[RIGHT_ADD_DISTRIB]
   THEN SUBST1_TAC
        ((((porr[MULT_SYM]))
	  o (porr[MULT_CLAUSES])
	  o (SUBS [(SYM o num_CONV) "2"]))
	 (SPECL ["1"; "n:num"] (CONJUNCT2 MULT)))
   THEN REFL_TAC
 ]
 );;

% ================================================================= %
% A firm bound for the val function.                                %
% ================================================================= %
let val_bound = prove_thm
(`val_bound`,
 "!b. (val 0 b) < (2 EXP (Width b))",
 INDUCT_THEN bus_Induct ASSUME_TAC
 THEN REPEAT GEN_TAC
 THENL
 [ port[val]
   THEN prt[Width; ADD_CLAUSES; EXP; MULT_CLAUSES]
   THEN port[bv]
   THEN COND_CASES_TAC
   THEN re_conv_tac num_CONV
   THEN rt[LESS_MONO_EQ; LESS_0]
 ;
   port[val]
   THEN prt[Width; ADD_CLAUSES; EXP; MULT_CLAUSES]
   THEN port[bv]
   THEN COND_CASES_TAC
   THEN prt[ADD_CLAUSES; MULT_CLAUSES]
   THENL
   [ port[val_equiv_def]
     THEN in_conv_tac num_CONV
     THEN prt[MULT_CLAUSES; ADD_CLAUSES]
     THEN port[porr[ADD_SYM]LESS_MONO_ADD_EQ]
     THEN SUBST1_TAC (SYM (num_CONV "2"))
     THEN art[]
   ;
     in_conv_tac num_CONV
     THEN prt[MULT_CLAUSES]
     THEN port[porr[ADD_SYM]LESS_MONO_ADD_EQ]
     THEN SUBST1_TAC (SYM (num_CONV "2"))
     THEN IMP_RES_THEN (\th. port[th]) ADDR_GREATER
   ]
 ]);;   
     
% ================================================================= %
% The val of a bus with the high order bit 0 is less than           %
% the val of a bus with the high order bit 1.  This translates      %
% to having 0 and 1, respectively, as the first parameter of val.   %
% ================================================================= %
let val_0_less_1 = prove_thm
(`val_0_less_1`,
 "!b b'. (Width b' = Width b) ==> (val 0 b < val 1 b')",
 INDUCT_THEN bus_Induct ASSUME_TAC
 THEN REPEAT GEN_TAC
 THENL
 [ wire_width_tac
   THEN port [val]
   THEN port[bv]
   THEN REPEAT COND_CASES_TAC
   THEN in_conv_tac num_CONV
   THEN rt [ADD_CLAUSES; LESS_MONO_EQ; LESS_0; LESS_SUC_REFL]
 ;
   port[val_equiv_def]
   THEN bus_width_tac
   THEN prt[MULT_CLAUSES; ADD_CLAUSES]
   THEN port[MATCH_MP ADDR_GREATER (SPEC_ALL val_bound)]
 ]);;

% ================================================================= %
% THEOREMS ABOUT ONE-ONE'NESS                                       %
% ================================================================= %

% ================================================================= %
% The property of functions being one-one commutes when composed.   %
% one-one'ness                                                      %
% ================================================================= %
let ONE_ONE_COMM = prove_thm
(`ONE_ONE_COMM`,
 "!(f:**->***) (g:*->**).
   ((!x x':**.(f x = f x') = (x = x')) /\
    (!y y':*.(g y = g y') = (y = y'))) ==>
   (!y y':*.(((f o g) y) = ((f o g) y')) = (y = y'))",
 REPEAT GEN_TAC
 THEN port[o_DEF]
 THEN in_conv_tac BETA_CONV
 THEN DISCH_THEN (CONJUNCTS_THEN (\th. port[th]))
 THEN rt[]
 );;

% ================================================================= %
% pos_num_of is one-one only when the arguments are non-negative.   %
% ================================================================= %
let pos_num_of_11 = prove_thm
(`pos_num_of_11`,
 "((~NEG i) /\ (~NEG i')) ==>
  ((pos_num_of i = pos_num_of i') = (i = i'))",
 DISCH_THEN (CONJUNCTS_THEN
  ((CHOOSE_THEN SUBST1_TAC) o (porr[NON_NEG_INT_IS_NUM])))
 THEN port[pos_num_of; INT_ONE_ONE]
 THEN REFL_TAC
 );;

% ================================================================= %
% The following proof was supplied by Konrad Slind.                 %
% ================================================================= %
let neg_11 = prove_thm
(`neg_11`,
  "(neg(INT x) = neg(INT y)) = (x = y)",
  EQ_TAC 
  THEN STRIP_TAC
  THEN art[] 
  THEN RULE_ASSUM_TAC ((rr[NEG_NEG_IS_IDENTITY;INT_ONE_ONE])
			o (AP_TERM "neg")) 
  THEN art[]);;

% ================================================================= %
% The val function applied to:                                      %
%  0 and equal Width buses                                          %
% is one-one.                                                       %
% ================================================================= %
let val_0_11 = prove_thm
(`val_0_11`,
 "!b b':(bool)bus.(Width b' = Width b) ==>
  ((val 0 b = val 0 b') = (b = b'))",
 INDUCT_THEN bus_Induct ASSUME_TAC
 THEN REPEAT GEN_TAC
 THENL
 [ wire_width_tac
   THEN port[val]
   THEN prt[ADD_CLAUSES]
   THEN port [bv_11; Wire_11]
   THEN REFL_TAC
 ;
   bus_width_tac
   THEN port[val]
   THEN prt[ADD_CLAUSES]
   THEN port[val_equiv_def]
   THEN port[bv]
   THEN REPEAT COND_CASES_TAC
   THEN prt[MULT_CLAUSES; ADD_CLAUSES]
   THENL
   [ poart[]
     THEN port[porr[ADD_SYM]EQ_MONO_ADD_EQ]
     THEN poart[]
     THEN rt[Bus_11]
   ;
     rt[Bus_11]
     THEN SYM_TAC
     THEN RULE_ASSUM_TAC SYM_RULE
     THEN poart[]
     THEN rt[MATCH_MP LESS_NOT_EQ
                      (SPEC_ALL(MATCH_MP (ADDR_GREATER)(SPEC_ALL val_bound)))]
   ;
     poart[]
     THEN rt[Bus_11]
     THEN rt[MATCH_MP LESS_NOT_EQ
                      (SPEC_ALL(MATCH_MP (ADDR_GREATER)(SPEC_ALL val_bound)))]
   ;
     poart[]
     THEN rt[Bus_11]
   ]
 ]);;

% ================================================================= %
% This lemma is used to prove the cases in iVal_11 when leading     %
% bits differ.  It uses several of the above theorems.              %
%                                                                   %
% iVal_lemma =                                                      %
% |- ~(INT(val 0 bus') =                                            %
%     (INT(val 0 b)) minus (INT(2 EXP (Width b))))                  %
% ================================================================= %
let iVal_lemma =
  MATCH_MP NEQ_NON_NEG_NEG
           (CONJ
	    (rr[(CONV_RULE (LHS_CONV (ONCE_DEPTH_CONV SYM_CONV)))
		(porr[AND_CLAUSES]
		 (PRUNE_CONV "(?n. (n = val 0 bus')/\ T)"))]
		 (porr[INT_ONE_ONE]
		      (SPEC "INT (val 0 bus')" NON_NEG_INT_IS_NUM)))
	    (MATCH_MP LESS_MINUS_LEMMA
		      (SPEC "b:(bool)bus" val_bound)));;
  

% ================================================================= %
% iVal applied to equal width buses is one-one.                     %
% ================================================================= %
let iVal_11 = prove_thm
(`iVal_11`,
 "!b b':(bool)bus.(Width b' = Width b) ==>
  ((iVal b = iVal b') = (b = b'))",
 INDUCT_THEN bus_Induct ASSUME_TAC
 THEN REPEAT GEN_TAC
 THENL
 [ wire_width_tac
   THEN port[iVal]
   THEN port[neg_11; Wire_11]
   THEN port[bv_11]
   THEN REFL_TAC
 ;
   bus_width_tac
   THEN port[iVal]
   THEN poart[bv]
   THEN REPEAT COND_CASES_TAC
   THEN prt[MULT_CLAUSES; ADD_CLAUSES; MINUS_ID]
   THENL
   [ port[Bus_11]
     THEN rt[MINUS_DEF]
     THEN EQ_TAC
     THENL
     [ DISCH_THEN
       (\th. IMP_RES_THEN
	(\th1. SUBST1_TAC
	       (SUBS [th1]
		     (porr[INT_ONE_ONE]
		          (MATCH_MP PLUS_RIGHT_CANCELLATION th))))
	val_0_11)
       THEN REFL_TAC
      ;
        DISCH_THEN SUBST1_TAC
	THEN REFL_TAC
      ]
    ;
      rt[Bus_11]
      THEN MATCH_ACCEPT_TAC (SYM_RULE iVal_lemma)
    ;
      rt[Bus_11]
      THEN RULE_ASSUM_TAC SYM_RULE
      THEN poart[]
      THEN MATCH_ACCEPT_TAC iVal_lemma
    ;
      rt[Bus_11; INT_ONE_ONE]
      THEN IMP_RES_THEN (\th. is_eq(concl th) => (SUBST1_TAC th) | ALL_TAC) val_0_11 
      THEN REFL_TAC
    ]
 ]);;

% ================================================================= %
% proving unequal is possible from one-one'ness.                    %
%                                                                   %
% ONE_ONE_LEMMA =                                                   %
% |- !f. (!x y. (f x = f y) = (x = y)) ==>                          %
%        (!x y. ~(f x = f y) = ~(x = y))                            %
% ================================================================= %
let ONE_ONE_LEMMA = save_thm (`ONE_ONE_LEMMA`,
((GEN "f:*->**")
 o DISCH_ALL
 o (GENL ["x:*"; "y:*"])
 o (AP_TERM "$~")
 o SPEC_ALL
 o ASSUME)
 "!x y.((f:*->**) x = f y) = (x = y)");;

% ================================================================= %
% THEOREMS ABOUT ZERO28                                             %
% ================================================================= %

% ================================================================= %
% Simplification for all-F buses.                                   %
% ================================================================= %
let val_lemma = TAC_PROOF
(([], "(val 0 (Bus F b) = val 0 b) /\ (val 0 (Wire F) = 0)"),
  prt[val; ADD_CLAUSES; bv_thm]
  THEN CONJ_TAC THEN REFL_TAC);;

% ================================================================= %
% Abstracting from ZERO28 using Bits28, iVal, pos_num_of            %
% produces "0".                                                     %
% ================================================================= %
let ZERO28_IS_ZERO = prove_thm
(`ZERO28_IS_ZERO`,
 "pos_num_of (iVal (Bits28 ZERO28)) = 0",
 port[ZERO28]
 THEN in_conv_tac wordn_CONV
 THEN port[Bits28_Word28]
 THEN port[iVal]
 THEN port[bv_thm]
 THEN port[MULT_CLAUSES]
 THEN port[MINUS_ID]
 THEN prt[val_lemma]
 THEN port[pos_num_of]
 THEN REFL_TAC);;

% ================================================================= %
% prove the composition of functions in the diagram below is        %
% one-one.                                                          %
% ================================================================= %
let num_of_word28_11 = prove_thm
(`num_of_word28_11`,
 "!b b'.~NEG (iVal (Bits28 b)) /\ ~NEG (iVal (Bits28 b')) ==>
  ((pos_num_of(iVal (Bits28 b)) = pos_num_of(iVal(Bits28 b'))) =
   (b = b'))",
 REPEAT GEN_TAC
 THEN STRIP_TAC
 THEN IMP_RES_n_THEN 2 port1 pos_num_of_11
 THEN port
      [( (rr[Width_Bits28])
       o (SPECL ["Bits28 y"; "Bits28 y'"]))iVal_11]
 THEN port[Bits28_11]
 THEN REFL_TAC
 );;


% ================================================================= %
% The nonNEG condition is fulfilled by a leading 0 (F).             %
% ================================================================= %
let leading_F_nonNEG = prove_thm
(`leading_F_nonNEG`,
 "!b. ~NEG (iVal (Bus F b))",
 port[iVal]
 THEN port[bv_thm]
 THEN port[MULT_CLAUSES]
 THEN port[MINUS_ID]
 THEN port[NON_NEG_INT_IS_NUM]
 THEN GEN_TAC
 THEN EXISTS_TAC "val 0 b"
 THEN REFL_TAC
 );;

% ================================================================= %
% A particular instance.                                            %
% ================================================================= %
let ZERO28_nonNEG = prove_thm
(`ZERO28_nonNEG`,
 "~NEG(iVal(Bits28 ZERO28))",
 port[ZERO28]
 THEN in_conv_tac wordn_CONV
 THEN port[Bits28_Word28]
 THEN rt [leading_F_nonNEG]
 );;
% ================================================================= %
%         :word32             :word32
            |            ---->   |
  atom_bits |       DEC28        |
            V   ----             V
         :word28              :word28
            |                    |
     Bits28 |                    |
            V                    V
        :(bool)bus           :(bool)bus
            |                    |
       iVal |                    |
            V    modulo_28_Dec   V
         :integer ----------> :integer
            |                    |
 pos_num_of |                    |
            V       PRE          V
          :num  ------------>  :num
%                  
% ================================================================= %

% ================================================================= %
% THEOREMS ABOUT nth                                                %
% ================================================================= %

% ================================================================= %
% nth_lemma = |- !n fcn x. nth(SUC n)fcn x = nth n fcn(fcn x)       %
% ================================================================= %
let nth_lemma = prove_thm
(`nth_lemma`,
 "!(n:num) (fcn:* -> *) (x:*).
   nth (SUC n) fcn x = nth n fcn (fcn x)",
 INDUCT_TAC
 THEN REPEAT GEN_TAC
 THENL
 [ part[nth]
 ; port[nth]
   THEN poart[]
 ]
 THEN REFL_TAC);;

% ================================================================= %
% It takes n applications of "PRE" to get "0".                      %
% ================================================================= %
let nth_PRE_thm = prove_thm
(`nth_PRE_thm`,
 "!n. nth n PRE n = 0",
 INDUCT_TAC
 THENL
 [ port[nth]
   THEN REFL_TAC
 ; port [nth_lemma]
   THEN art[PRE]
 ]);;

% ================================================================= %
% Arithmetic lemma.                                                 %
% ================================================================= %
let LESS_SUC_IMP_LESS_PRE = prove_thm
(`LESS_SUC_IMP_LESS_PRE`,
 "!m n.(SUC n) < m ==> n < PRE m",
 INDUCT_TAC
 THENL
 [ rt[NOT_LESS_0]
 ; port[LESS_MONO_EQ; PRE] THEN rt[]
 ]);;

% ================================================================= %
% Using the above, we prove that less than m applications of        %
% PRE to m is above zero.                                           %
% ================================================================= %
let nth_PRE_GRT_0 = prove_thm
(`nth_PRE_GTR_0`,
 "!n m. n < m ==> 0 < (nth n PRE m)",
 INDUCT_TAC
 THENL
 [ rt[nth]
 ; GEN_TAC
   THEN port[nth_lemma]
   THEN DISCH_THEN
   (\th. ANTE_RES_THEN port1
                      (MATCH_MP LESS_SUC_IMP_LESS_PRE th))
 ]);;

% ================================================================= %
% If the num is 0, then the word28 value is ZERO28.                 %
% ================================================================= %
let ZERO28_MEANS_ZERO = prove_thm
(`ZERO28_MEANS_ZERO`,
 "(~(NEG (iVal (Bits28 (atom_bits w32)))))==>
   (((pos_num_of (iVal (Bits28 (atom_bits w32)))) = 0) =
    ((atom_bits w32) = ZERO28))",
 DISCH_THEN
 (\th. SUBST1_TAC (SYM_RULE ZERO28_IS_ZERO)
       THEN (port1 o SYM) (MATCH_MP num_of_word28_11
				    (CONJ th ZERO28_nonNEG)))
 THEN REFL_TAC);;

% ================================================================= %
% Slightly more general.                                            %
% ================================================================= %
let ZERO28_MEANS_ZERO' = prove_thm
(`ZERO28_MEANS_ZERO'`,
 "(~(NEG (iVal (Bits28 b))))==>
   (((pos_num_of (iVal (Bits28 b))) = 0) =
    (b = ZERO28))",
 DISCH_THEN
 (\th. SUBST1_TAC (SYM_RULE ZERO28_IS_ZERO)
       THEN (port1 o SYM) (MATCH_MP num_of_word28_11
				    (CONJ th ZERO28_nonNEG)))
 THEN REFL_TAC);;

% ================================================================= %
% Two assumptions about the DEC28 operation that will have to be    %
% proven from the low level implementation.  Their proof is         %
% deferred at present.                                              %
% ================================================================= %
let DEC28_assum1 =
"!w28. (POS (iVal (Bits28 w28)))==>
        (PRE(pos_num_of(iVal(Bits28 w28))) =
           pos_num_of(iVal(Bits28((atom_bits o DEC28) w28))))"
and DEC28_assum2 =
"!w28.(POS (iVal (Bits28 w28)))==>
     ~(NEG (iVal (Bits28 ((atom_bits o DEC28) w28))))";;

% ================================================================= %
% The theorem that n DEC28 to a bit 28 value corresponding to n     %
% gives a bit28 value corresponding to 0.                           %
% ================================================================= %
let nth_DEC28_thm = save_thm
(`nth_DEC28_thm`,
 TAC_PROOF
 (([ DEC28_assum1
   ; DEC28_assum2
   ],
   "!n w28.
    (~(NEG (iVal (Bits28 w28)))) ==>
    (n = (pos_num_of (iVal (Bits28 w28)))) ==>
    ((pos_num_of (iVal (Bits28 (nth n
                                   (atom_bits o DEC28)
                                   w28)))
     = 0) /\
    (~NEG (iVal (Bits28 (nth n
                             (atom_bits o DEC28)
                             w28)))))"),
  INDUCT_TAC
  THEN GEN_TAC
  THENL
  [ STRIP_TAC			% case: ZERO28 %
    THEN port[nth]
    THEN DISCH_THEN SUBST1_TAC
    THEN art[]
				% case: nonZERO28 %
  ; port[nth_lemma]
    THEN DISCH_THEN
    (\th. DISJ_CASES_THEN2
					% POS %
     (\th2. ANTE_RES_THEN
      (ANTE_RES_THEN
       (\th3. DISCH_THEN
	(\th4. ACCEPT_TAC
	 (MATCH_MP th3 (porr[MATCH_MP (ASSUME DEC28_assum1) th2]
		        (porr[PRE]
			 (AP_TERM "PRE" th4)))))))
      th2)
					% = INT 0 %
     (\th2. SUBST1_TAC th2
            THEN port[pos_num_of]
	    THEN rt[SYM_RULE
	             (MATCH_MP
		      (SPECL ["0"; "SUC n"] LESS_NOT_EQ)
		      (SPEC_ALL LESS_0))])

     (porr[nonNEG_POS_OR_ZERO] th))
 ]));;

% ================================================================= %
% loop_terminates_lemma =                                           %
% .. |- !w28.                                                       %
%        ~NEG(iVal(Bits28 w28)) ==>                                 %
%        (nth(pos_num_of(iVal(Bits28 w28)))(atom_bits o DEC28)w28 = %
%         ZERO28)                                                   %
%                                                                   %
% The 2 assumptions are DEC28_assum1 and DEC28_assum2.              %
% ================================================================= %
let loop_terminates_lemma = save_thm
(`loop_terminates_lemma`,
 let [l1;l2] =
 CONJUNCTS
 (UNDISCH
  (rr[]
   (SPECL ["pos_num_of(iVal(Bits28 w28))"; "w28:word28"]
	  nth_DEC28_thm)))
 in
 (GEN "w28:word28"
  (DISCH "~(NEG (iVal (Bits28 w28)))"
   (SUBS
    [MATCH_MP
     (SPEC "nth (pos_num_of(iVal(Bits28 w28)))(atom_bits o DEC28)w28"
           (GEN_ALL ZERO28_MEANS_ZERO'))
     l2]
    l1))));;

% ================================================================= %
% Essentially, LESS is MONO over PRE for non-zero values.           %
% ================================================================= %
let SUC_LESS_PRE = prove_thm
(`SUC_LESS_PRE`,
 "!n m. SUC n < m = n < PRE m",
 GEN_TAC
 THEN INDUCT_TAC
 THEN port[PRE]
 THEN port[NOT_LESS_0; LESS_MONO_EQ]
 THEN REFL_TAC);;

% ================================================================= %
% The complement of loop_terminates_lemma:                          %
% fewer than n DEC28's applied to w28 does not give a value         %
% equal to ZERO28.                                                  %
% ================================================================= %
let nth_DEC28_NOT_ZERO = save_thm
(`nth_DEC_NOT_ZERO`,
 TAC_PROOF
 (([DEC28_assum1;DEC28_assum2],
   "!n w28.                                                       
        ~NEG(iVal(Bits28 w28)) ==>
        (n < (pos_num_of(iVal(Bits28 w28)))) ==>
        (~(nth n(atom_bits o DEC28)w28 = ZERO28))"),
 INDUCT_TAC
 THEN GEN_TAC
 THENL
 [ port[nth]
   THEN STRIP_TAC
   THEN STRIP_TAC
   THEN DISCH_THEN
        ( IMP_RES_TAC
        o (MATCH_MP NOT_LESS_EQ)
        o SYM_RULE
        o (porr[ZERO28_IS_ZERO])
        o (in_conv_rule BETA_CONV)
        o (AP_TERM "\w.pos_num_of(iVal(Bits28 w))"))
 ; port[nonNEG_POS_OR_ZERO; nth_lemma]
   THEN DISCH_THEN
        (DISJ_CASES_THEN2
	 (\th3. ANTE_RES_THEN
	  (ANTE_RES_THEN
	   (\th. DISCH_THEN
	    (\th1. ACCEPT_TAC
	     (MATCH_MP th (porr[MATCH_MP (ASSUME DEC28_assum1) th3]
			       (porr[SUC_LESS_PRE] th1))))))
	  th3)
	 (\th2. SUBST1_TAC th2 THEN rt[pos_num_of; NOT_LESS_0]))
 ]));;

timer false;;
close_theory ();;
print_theory `-`;;
