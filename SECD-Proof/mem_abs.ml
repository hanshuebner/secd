% SECD verification                                                 %
%                                                                   %
% FILE:        mem_abs.ml                                           %
%                                                                   %
% DESCRIPTION: Defines an abstraction between the "real" memory     %
%              definition, and the abstract memories.               %
%                                                                   %
% USES FILES:  integer library, dp_types.th, abstract_mem_type.th   %
%                                                                   %
% Brian Graham 89.08.01                                             %
%                                                                   %
% Modifications:                                                    %
% 02.08.91 - BtG - updated to HOL12                                 %
% ================================================================= %
new_theory `mem_abs`;;

loadt `wordn`;;
load_library `integer`;;

map new_parent
 [ `rt_SYS`
 ; `abstract_mem_type`
 ; `rt_SYS`
 ; `constraints`
 ; `val_theorems`
 ];;

timer true;;

let ID_THM =
  GEN_ALL (LIST_BETA_CONV "(\f:*->** (x:*).f x) f x");;
% ================================================================= %
% In order to prove that the thing produced by this function when   %
% composed with a memory is an mf_sexp_mem, this function must be   %
% TOTAL.  The original definition with an arbitrary value returned  %
% for the unused record case prevented the simplification of:       %
%  (REP_mfsexp_mem(ABS_mfsexp_mem (Mem_Range_Abs o memory)))        %
% since REP_mfsexp_mem_ABS_mfsexp_mem =                             %
%  |- !r. IS_mfsexp_mem r = (REP_mfsexp_mem(ABS_mfsexp_mem r) = r)  %
% In the unused case, IS_mfsexp_mem (Mem_Range_Abs o memory)        %
% is not provable.                                                  %
%                                                                   %
% 2 possibilities occur:                                            %
% - constrain the memory image to never have the unused case, EVEN  %
%   for cells that are never used!!!                                %
% - alter the abstraction function so it is total. This could be    %
%   done by returning a (wrong?) cell in the unused case, or by     %
%   returning a value for which the IS_mfsexp_mem predicate could   %
%   be satisfied, such as:                                          %
%    @x.IS_mfsexp_mem (\c:word14.((mark_bit w),(field_bit w)), x)   %
%                                                                   %
% I prefer aesthetically the first option of the latter choice.     %
% This simply casts all unused cell types arbitrarily as one cell   %
% type.  In the actual proof, this will not matter since the actual %
% cells used will be constrained to be of specific types.           %
%                                                                   %
% This lessens the amount of constraint needed to prove the         %
% correctness.  We needn't be concerned with any cells that are     %
% never part of the computation.                                    %
%                                                                   %
% I have chosen to make them cons cells, since the test for atom    %
% cells considers only one bit, and thus                            %
%   "~is_atom cell = is_cons cell",                                 %
% which is just what we would like.                                 %
% ================================================================= %
let Mem_Range_Abs = new_definition
 (`Mem_Range_Abs`,
  "(Mem_Range_Abs:word32->((bool#bool)#((word14#word14)+atom))) w
    =
    ((mark_bit w),(field_bit w)),
    ((is_symbol w) => INR (Symb (Val  (Bits28 (atom_bits w))))     |
     (is_number w) => INR (Int  (iVal (Bits28 (atom_bits w))))     |
                      INL ((car_bits w), (cdr_bits w)))"
 );;

let mem_abs = new_definition 
  (`mem_abs`, 
   "mem_abs (M:word14->word32) = ABS_mfsexp_mem (Mem_Range_Abs o M)"
  );;

timer false;;
close_theory ();;

% ================================================================= %
% A few definitions/theorems needed for the proofs:                 %
% ================================================================= %
loadt `BINDER_EQ_TAC`;;
loadt `SELECT_UNIQUE`;;
loadt `RATOR_RAND_CONV`;;
loadt `COND_CASES_THEN`;;

map (load_theorem `bus`)
 [ `Bus_11`
 ; `Wire_11`
 ];;
map (load_definition `dp_types`)
 [ `RT_CONS`
 ; `RT_NUMBER`
 ; `RT_SYMBOL`
 ; `is_atom`
 ; `is_number`
 ; `is_symbol`
 ; `is_cons`
 ];;
map (load_theorem `dp_types`)
 [ `rec_types_DISTINCT`
 ; `records_distinct`
 ; `bus32_cons_fields_lemma_1`
 ; `bus32_num_fields_lemma_1`
 ; `bus32_symb_fields_lemma`
 ; `mf_of_garbage_bits`
 ; `Bits2_Word2`
 ; `Word2_11`
 ; `Word2_Cases`
 ; `atom_rec_equivalence`
 ];;

map (load_definition `abstract_mem_type`)
 [ `mfsexp_mem_ISO_DEF`
 ; `M_CAR`
 ; `M_Car`
 ; `M_Cdr`
 ; `M_Cons`
 ; `M_Atom`
 ; `M_int_of`
 ; `M_atom_of`
 ; `int_of_atom`
% ; `ABS_mfsexp_mem` %
 ; `IS_mfsexp_mem`
 ; `M_Rplaca`
 ; `M_store_int`
 ; `M_Dec`
 ; `M_Eq`
 ; `M_Leq`
 ; `M_Add`
 ; `M_Sub`
 ];;
map (load_theorem `abstract_mem_type`)
 [ `Int_11`
 ; `Symb_11`
 ; `NOT_Int_Symb`
 ];;
let REP_mfsexp_mem_ABS_mfsexp_mem = CONJUNCT2 mfsexp_mem_ISO_DEF;;

load_definition `rt_SYS` `Store14`;;
map (load_definition `rt_DP`)
 [ `ADD28`
 ; `SUB28`
 ; `DEC28`
 ];;
map (load_theorem `constraints`)
 [ `well_formed_free_list_lemma`
 ; `M_Cons_2_precond_lemma`
 ; `M_Cons_3_precond_lemma`
 ; `M_Cons_4_precond_lemma`
 ];;
map (load_definition `modulo_ops`)
[ `modulo_28_Add`
; `modulo_28_Sub`
; `modulo_28_Dec`
];;

map (load_theorem `val_theorems`)
[ `iVal_Bits28_11`
; `Val_Bits28_11`
; `exists_word28_rep`
];;

timer true;;
% ================================================================= %
% Now some useful theorems about the abstraction:                   %
% ================================================================= %
let Mem_Range_Abs_lemma = prove
("!memory. IS_mfsexp_mem(Mem_Range_Abs o memory)",
 GEN_TAC
 THEN port[IS_mfsexp_mem]
 THEN port[o_THM]
 THEN GEN_TAC
 THEN EXISTS_TAC "mark_bit(memory (cell:word14))"
 THEN EXISTS_TAC "field_bit (memory (cell:word14))"
 THEN port[definition `-` `Mem_Range_Abs`]
 THEN port[is_number; is_symbol; is_cons]
 THEN DISJ_CASES_THEN (DISJ_CASES_THEN SUBST1_TAC)
           (SPEC "rec_type_bits (memory (cell:word14))"
		 (porr(map SYM_RULE [RT_CONS; RT_NUMBER; RT_SYMBOL])
			   (porr[SYM (wordn_CONV "#01");SYM (wordn_CONV "#10")]
				     Word2_Cases)))
 THEN rt[rec_types_DISTINCT; PAIR_EQ]
 THENL
 [ DISJ2_TAC
   THEN EXISTS_TAC "Int(iVal(Bits28(atom_bits(memory (cell:word14)))))"
   THEN REFL_TAC
 ; DISJ2_TAC
   THEN EXISTS_TAC "Symb(Val(Bits28(atom_bits(memory (cell:word14)))))"
   THEN REFL_TAC
 ; DISJ1_TAC
   THEN port[RT_NUMBER; RT_SYMBOL]
   THEN in_conv_tac wordn_CONV
   THEN port[Word2_11]
   THEN rt[Bus_11; Wire_11]
   THEN EXISTS_TAC "car_bits(memory (cell:word14))"
   THEN EXISTS_TAC "cdr_bits(memory (cell:word14))"
   THEN REFL_TAC
 ; DISJ1_TAC
   THEN EXISTS_TAC "car_bits(memory (cell:word14))"
   THEN EXISTS_TAC "cdr_bits(memory (cell:word14))"
   THEN REFL_TAC
 ]);;

% ================================================================= %
% REP_ABS_Mem_Range_Abs =                                           %
% |- REP_mfsexp_mem(ABS_mfsexp_mem(Mem_Range_Abs o memory)) =       %
%    Mem_Range_Abs o memory                                         %
% ================================================================= %
let REP_ABS_Mem_Range_Abs = save_thm
(`REP_ABS_Mem_Range_Abs`,
 rr[Mem_Range_Abs_lemma]
   (SPEC "Mem_Range_Abs o (memory:word14->word32)"
         (INST_TYPE [":word14",":*"; ":atom",":**"]
		    REP_mfsexp_mem_ABS_mfsexp_mem))
 );;

% ================================================================= %
% Unfolding the Mem_Range_Abs function applied to a cons cell.      %
% ================================================================= %
let Mem_Range_Abs_cons_lemma = prove
("!a b:word14.
  Mem_Range_Abs(bus32_cons_append #00 RT_CONS a b) = (F,F),INL(a,b)",
 port[Mem_Range_Abs]
 THEN port[is_number; is_symbol;mf_of_garbage_bits]
 THEN port[bus32_cons_fields_lemma_1]
 THEN in_conv_tac wordn_CONV
 THEN port[rec_types_DISTINCT;Bits2_Word2]
 THEN rt[Hd_bus; Tl_bus; PAIR_EQ]
 );;

% ================================================================= %
% Unfolding the Mem_Range_Abs function applied to a number cell.    %
% ================================================================= %
let Mem_Range_Abs_number_lemma = prove
("!a:word28.
  Mem_Range_Abs(bus32_num_append a) = (F,F),INR(Int(iVal(Bits28 a)))",
 port[Mem_Range_Abs]
 THEN port[is_number; is_symbol; mf_of_garbage_bits]
 THEN port[bus32_num_fields_lemma_1]
 THEN in_conv_tac wordn_CONV
 THEN port[rec_types_DISTINCT;Bits2_Word2]
 THEN rt[Hd_bus; Tl_bus; PAIR_EQ]
 );;

% ================================================================= %
% We provide theorems to do a mapping from abstract memory          %
% operations on "mem_abs memory", to primitive operations on        %
% "memory", starting with :                                         %
% ================================================================= %
% M_Car & M_Cdr:                                                    %
% ================================================================= %
let car_cdr_mem_abs_lemma = prove_thm
(`car_cdr_mem_abs_lemma`,
 "is_cons(memory v) ==>
  !x. (M_Car(v,mem_abs memory, x) = car_bits (memory v)) /\
      (M_Cdr(v,mem_abs memory, x) = cdr_bits (memory v))",
 STRIP_TAC
 THEN port[M_Cdr; M_Car]
 THEN port[mem_abs]
 THEN port[REP_ABS_Mem_Range_Abs]
 THEN port[o_THM]
 THEN port[Mem_Range_Abs]
 THEN IMP_RES_THEN port1 records_distinct
 THEN rt[OUTL; OUTR]
 );;

% ================================================================= %
% M_atom_of (symbol):                                               %
% ================================================================= %
let atom_symbol_mem_abs_lemma = prove_thm
(`atom_symbol_mem_abs_lemma`,
 "is_symbol(memory v) ==>
  !x. M_atom_of(v,mem_abs memory, x) =
      Symb(Val(Bits28(atom_bits(memory v))))",
 port[M_atom_of]
 THEN port[mem_abs]
 THEN port[REP_ABS_Mem_Range_Abs]
 THEN port[o_THM]
 THEN port[Mem_Range_Abs]
 THEN port[SND]
 THEN DISCH_THEN port1
 THEN rt[OUTR]
 );;

% ================================================================= %
% M_int_of:                                                         %
% ================================================================= %
let number_mem_abs_lemma = prove_thm
(`number_mem_abs_lemma`,
 "is_number(memory v) ==>
  !x. M_int_of(v,mem_abs memory, x) = iVal(Bits28(atom_bits (memory v)))",
 STRIP_TAC
 THEN port[M_int_of]
 THEN port[M_atom_of]
 THEN port[mem_abs]
 THEN port[REP_ABS_Mem_Range_Abs]
 THEN port[o_THM]
 THEN port[Mem_Range_Abs]
 THEN IMP_RES_THEN port1 records_distinct
 THEN part[COND_CLAUSES]
 THEN rt[OUTR; int_of_atom]
 );;

% ================================================================= %
% Combine the 2 preceeding to handle the machine instruction case.  %
% ================================================================= %
let opcode_mem_abs_lemma = prove_thm
(`opcode_mem_abs_lemma`,
 "is_cons(memory v) ==>
  is_number(memory(car_bits(memory v))) ==>
  !x. M_int_of(M_CAR(v,mem_abs memory,x)) =
      iVal(Bits28(atom_bits(memory(car_bits(memory v)))))",
 port[M_CAR]
 THEN DISCH_THEN (port1 o (MATCH_MP car_cdr_mem_abs_lemma))
 THEN DISCH_THEN (port1 o (MATCH_MP number_mem_abs_lemma))
 THEN GEN_TAC
 THEN REFL_TAC
 );;

% ================================================================= %
% M_Atom:                                                           %
% ================================================================= %
let cons_NOT_M_Atom = prove
("is_cons(memory v) ==> !x. M_Atom(v,mem_abs memory,x) = F",
 MAP_EVERY port1
 [ M_Atom; mem_abs; REP_ABS_Mem_Range_Abs; o_THM; Mem_Range_Abs ]
 THEN STRIP_TAC THEN IMP_RES_THEN port1 records_distinct
 THEN GEN_TAC
 THEN prt[COND_CLAUSES]
 THEN MAP_EVERY port1 [ SND; ISR ]
 THEN REFL_TAC
 );;

let branch_lemma = prove
 ("!(f:*->**) a b c. f (a => b | c) = a => (f b) | (f c)",
  REPEAT GEN_TAC THEN BOOL_CASES_TAC "a:bool" THEN art[]);;
% ================================================================= %
% M_Add:                                                            %
% ================================================================= %
let M_Add_unfold_lemma = prove_thm
(`M_Add_unfold_lemma`,
 "(is_number(memory x)) /\
  (is_number(memory y)) /\
  (is_cons(memory free)) ==>
   (M_Add(x, y, mem_abs memory, free) =
      (free,
       mem_abs(Store14 free
                       (ADD28 ((atom_bits o memory)x) ((atom_bits o memory)y))
                       memory),
       cdr_bits(memory free)))",
 STRIP_TAC
 THEN port[M_Add;ADD28]
 THEN port[M_store_int]
 THEN IMP_RES_THEN port1 number_mem_abs_lemma
 THEN IMP_RES_THEN port1 cons_NOT_M_Atom
 THEN port[COND_CLAUSES]
 THEN port[LET_DEF]
 THEN prt[ID_THM]
 THEN port[UNCURRY_DEF]
 THEN BETA_TAC
 THEN prt[PAIR_EQ]
 THEN IMP_RES_THEN port1 car_cdr_mem_abs_lemma
 THEN rt[]
 THEN port[mem_abs]
 THEN SELECT_UNIQUE_TAC
 THENL
 [ port[REP_ABS_Mem_Range_Abs]
   THEN in1_conv_tac FUN_EQ_CONV
   THEN GEN_TAC
   THEN port[o_THM]
   THEN port[Store14]
   THEN BETA_TAC
   THEN COND_CASES_TAC
   THEN rt[COND_CLAUSES]
   THEN port[Mem_Range_Abs_number_lemma]
   THEN rt[PAIR_EQ]
   THEN REPEAT AP_TERM_TAC
   THEN prt[o_THM]
   THEN in1_conv_tac SELECT_CONV
   THEN port[modulo_28_Add]
   THEN MATCH_ACCEPT_TAC exists_word28_rep
 ; REPEAT GEN_TAC
   THEN DISCH_THEN
        (\th. port[porr [prove_rep_fn_one_one mfsexp_mem_ISO_DEF]
                        (SUBS[SYM(CONJUNCT2 th)](CONJUNCT1 th))])
   THEN REFL_TAC
 ]);;

% ================================================================= %
% M_Sub:                                                            %
% ================================================================= %
let M_Sub_unfold_lemma = prove_thm
(`M_Sub_unfold_lemma`,
 "(is_number(memory x)) /\
  (is_number(memory y)) /\
  (is_cons(memory free)) ==>
   (M_Sub(x, y, mem_abs memory, free) =
      (free,
       mem_abs(Store14 free
                       (SUB28 ((atom_bits o memory)x) ((atom_bits o memory)y))
                       memory),
       cdr_bits(memory free)))",
 STRIP_TAC
 THEN port[M_Sub;SUB28]
 THEN port[M_store_int]
 THEN IMP_RES_THEN port1 number_mem_abs_lemma
 THEN IMP_RES_THEN port1 cons_NOT_M_Atom
 THEN port[COND_CLAUSES]
 THEN port[LET_DEF]
 THEN prt[ID_THM]
 THEN port[UNCURRY_DEF]
 THEN BETA_TAC
 THEN prt[PAIR_EQ]
 THEN IMP_RES_THEN port1 car_cdr_mem_abs_lemma
 THEN rt[]
 THEN port[mem_abs]
 THEN SELECT_UNIQUE_TAC
 THENL
 [ port[REP_ABS_Mem_Range_Abs]
   THEN in1_conv_tac FUN_EQ_CONV
   THEN GEN_TAC
   THEN port[o_THM]
   THEN port[Store14]
   THEN BETA_TAC
   THEN COND_CASES_TAC
   THEN rt[COND_CLAUSES]
   THEN port[Mem_Range_Abs_number_lemma]
   THEN rt[PAIR_EQ]
   THEN REPEAT AP_TERM_TAC
   THEN prt[o_THM]
   THEN in1_conv_tac SELECT_CONV
   THEN port[modulo_28_Sub]
   THEN MATCH_ACCEPT_TAC exists_word28_rep
 ; REPEAT GEN_TAC
   THEN DISCH_THEN
        (\th. port[porr [prove_rep_fn_one_one mfsexp_mem_ISO_DEF]
                        (SUBS[SYM(CONJUNCT2 th)](CONJUNCT1 th))])
   THEN REFL_TAC
 ]);;

% ================================================================= %
% M_Dec:                                                            %
% ================================================================= %
let M_Dec_unfold_lemma = prove
("(is_number(memory x)) /\
  (is_cons(memory free)) ==>
   (M_Dec(x, mem_abs memory, free) =
      (free,
       mem_abs(Store14 free
                       (DEC28 ((atom_bits o memory)x))
                       memory),
       cdr_bits(memory free)))",
 STRIP_TAC
 THEN port[M_Dec;DEC28]
 THEN port[M_store_int]
 THEN IMP_RES_THEN port1 number_mem_abs_lemma
 THEN IMP_RES_THEN port1 cons_NOT_M_Atom
 THEN port[COND_CLAUSES]
 THEN port[LET_DEF]
 THEN prt[ID_THM]
 THEN port[UNCURRY_DEF]
 THEN BETA_TAC
 THEN prt[PAIR_EQ]
 THEN IMP_RES_THEN port1 car_cdr_mem_abs_lemma
 THEN rt[]
 THEN port[mem_abs]
 THEN SELECT_UNIQUE_TAC
 THENL
 [ port[REP_ABS_Mem_Range_Abs]
   THEN in1_conv_tac FUN_EQ_CONV
   THEN GEN_TAC
   THEN port[o_THM]
   THEN port[Store14]
   THEN BETA_TAC
   THEN COND_CASES_TAC
   THEN rt[COND_CLAUSES]
   THEN port[Mem_Range_Abs_number_lemma]
   THEN rt[PAIR_EQ]
   THEN REPEAT AP_TERM_TAC
   THEN prt[o_THM]
   THEN in1_conv_tac SELECT_CONV
   THEN port[modulo_28_Dec]
   THEN MATCH_ACCEPT_TAC exists_word28_rep
 ; REPEAT GEN_TAC
   THEN DISCH_THEN
        (\th. port[porr [prove_rep_fn_one_one mfsexp_mem_ISO_DEF]
                        (SUBS[SYM(CONJUNCT2 th)](CONJUNCT1 th))])
   THEN REFL_TAC
 ]);;

% ================================================================= %
% M_Atom:                                                           %
% ================================================================= %
let M_Atom_unfold_lemma = prove_thm
(`M_Atom_unfold_lemma`,
 "M_Atom(v,mem_abs memory, free) = is_atom(memory v)",
 port[M_Atom]
 THEN port[is_atom]
 THEN port[mem_abs]
 THEN port[REP_ABS_Mem_Range_Abs]
 THEN port[o_THM]
 THEN rt[Mem_Range_Abs]
 THEN COND_CASES_TAC
 THEN rt[ISR]
 THEN COND_CASES_TAC
 THEN rt[ISR]
 );;
 
% ================================================================= %
% M_Leq:                                                            %
% ================================================================= %
let M_Leq_unfold_lemma = prove_thm
(`M_Leq_unfold_lemma`,
 "(is_number(memory x)) /\
  (is_number(memory y)) ==>
  (M_Leq(x,y,mem_abs memory, free) =
   LEQ_prim (memory x) (memory y))",
 STRIP_TAC
 THEN port[M_Leq; definition `rt_DP` `LEQ_prim`]
 THEN prt[LET_DEF]
 THEN BETA_TAC
 THEN prt[o_THM]
 THEN IMP_RES_THEN port1 number_mem_abs_lemma
 THEN REFL_TAC
 );;
 
% ================================================================= %
% M_Eq:                                                             %
% ================================================================= %
let M_Eq_unfold_lemma = prove_thm
(`M_Eq_unfold_lemma`,
 "(!x:word14. garbage_bits(memory x) = #00) ==>
  ((is_atom(memory x)) \/ (is_atom(memory y))) ==>
      (M_Eq(x,y,mem_abs memory, free) = (memory x = memory y))",
 STRIP_TAC 
 THEN port[M_Eq]
 THEN port[LET_DEF]
 THEN BETA_TAC
 THEN port[M_Atom_unfold_lemma]
 THEN port[M_atom_of]
 THEN port[mem_abs]
 THEN port[REP_ABS_Mem_Range_Abs]
 THEN port[o_THM]
 THEN DISCH_THEN
      (\th. EQ_TAC
	    THENL
	    [ STRIP_ASSUME_TAC th THEN art[]
            ; STRIP_ASSUME_TAC th
	      THEN DISCH_THEN SUBST_ALL_TAC
	      THEN art[]		% solves one branch ... %
	    ])
 THEN COND_CASES_THEN (ASSUME_TAC o (rr[]))
 THENL
 [ rt[]
   THEN DISCH_THEN SUBST1_TAC
   THEN RES_TAC
 ; ALL_TAC
 ; rt[]
   THEN DISCH_THEN SUBST1_TAC
   THEN RES_TAC
 ; ALL_TAC
 ]
 THEN port[Mem_Range_Abs]
 THEN port[SND]
 THEN RULE_ASSUM_TAC(porr[is_atom])
 THEN EVERY_ASSUM (\th. is_disj (concl th) => STRIP_ASSUME_TAC th | ALL_TAC)
 THEN IMP_RES_THEN port1 records_distinct
 THEN art[ OUTR; Symb_11; Int_11; NOT_Int_Symb; SYM_RULE NOT_Int_Symb
	 ; iVal_Bits28_11; Val_Bits28_11]
 THEN RULE_ASSUM_TAC (rr[is_symbol; is_number])
 THEN STRIP_TAC
 THEN port[SYM_RULE atom_rec_equivalence]
 THEN art[]
 );;

% ================================================================= %
% M_Rplaca:                                                         %
% ================================================================= %
let Rplaca_unfold_lemma = prove_thm
(`Rplaca_unfold_lemma`,
 "!(a:word14) memory.
  is_cons (memory a) ==>
  !v free.
   M_Rplaca(a,v,mem_abs memory,free) = 
   (a,
    mem_abs(Store14 a
                    (bus32_cons_append #00 RT_CONS v (cdr_bits(memory a)))
                    memory),
    free)",
 REPEAT STRIP_TAC
 THEN port[M_Rplaca]
 THEN rt[PAIR_EQ]
 THEN port[Store14]
 THEN (CONV_TAC o RHS_CONV)(REWR_CONV mem_abs)
 THEN SELECT_UNIQUE_TAC
 THENL
 [ port[REP_ABS_Mem_Range_Abs]
   THEN in1_conv_tac FUN_EQ_CONV
   THEN GEN_TAC
   THEN port[o_THM]
   THEN BETA_TAC
   THEN COND_CASES_TAC
   THEN rt[COND_CLAUSES; o_THM]
   THENL
   [ port[Mem_Range_Abs_cons_lemma]
     THEN poart[]
     THEN IMP_RES_THEN port1 car_cdr_mem_abs_lemma
     THEN REFL_TAC
   ; port[mem_abs]
     THEN port[REP_ABS_Mem_Range_Abs]
     THEN port[o_THM]
     THEN REFL_TAC
   ]
 ; REPEAT GEN_TAC
   THEN DISCH_THEN
        (\th. port[porr [prove_rep_fn_one_one mfsexp_mem_ISO_DEF]
                        (SUBS[SYM(CONJUNCT2 th)](CONJUNCT1 th))])
   THEN REFL_TAC
 ]);;

% ================================================================= %
% M_Cons:                                                           %
% ================================================================= %
let cons_unfold_1_lemma = prove
("is_cons (memory free) ==>
  !v w.
   M_Cons(v,w,mem_abs memory,free) = 
   (free,
    mem_abs(Store14 free (bus32_cons_append #00 RT_CONS v w) memory),
    cdr_bits (memory free))",
 port[M_Cons]
 THEN DISCH_THEN (\th. (port1 (MATCH_MP cons_NOT_M_Atom th))THEN ASSUME_TAC th)
 THEN REPEAT GEN_TAC
 THEN MAP_EVERY port1 [COND_CLAUSES; LET_DEF; ID_THM; UNCURRY_DEF]
 THEN BETA_TAC
 THEN IMP_RES_THEN port1 car_cdr_mem_abs_lemma
 THEN rt[PAIR_EQ]
 THEN port[mem_abs]
 THEN SELECT_UNIQUE_TAC
 THENL
 [ port[REP_ABS_Mem_Range_Abs]
   THEN port[Store14]
   THEN in1_conv_tac FUN_EQ_CONV
   THEN GEN_TAC
   THEN port[o_THM]
   THEN BETA_TAC
   THEN COND_CASES_TAC
   THEN rt[COND_CLAUSES; o_THM]
   THEN port[Mem_Range_Abs_cons_lemma]
   THEN REFL_TAC
 ; REPEAT GEN_TAC
   THEN DISCH_THEN
        (\th. port[porr [prove_rep_fn_one_one mfsexp_mem_ISO_DEF]
                        (SUBS[SYM(CONJUNCT2 th)](CONJUNCT1 th))])
   THEN REFL_TAC
 ]);;

% ================================================================= %
% Using the previous theorem, we define the mapping from M_Cons     %
% on a memory to which a cons cell has already been written.        %
% ================================================================= %
let cons_unfold_2_lemma = prove
("(~(free = (cdr_bits(memory free))))       ==>
  is_cons (memory (cdr_bits (memory free))) ==>
  !v w z.
   M_Cons(v,w,
          mem_abs(Store14 free z memory),
	  cdr_bits(memory free)) = 
   (cdr_bits(memory free),
    mem_abs(Store14 (cdr_bits(memory free))
                    (bus32_cons_append #00 RT_CONS v w)
                    (Store14 free z memory)),
    cdr_bits (Store14 free z memory (cdr_bits (memory free))))",
 REPEAT STRIP_TAC
 THEN IMP_RES_THEN
      (IMP_RES_THEN (port1 o (MATCH_MP cons_unfold_1_lemma)
			   o SPEC_ALL))
      M_Cons_2_precond_lemma
 THEN REFL_TAC
 );;

let cons_unfold_3_lemma = prove
("~(free = cdr_bits(memory free))                    /\
  ~(free = cdr_bits(memory(cdr_bits(memory free))))  /\
  ~(cdr_bits(memory free) =
    cdr_bits(memory(cdr_bits(memory free))))         /\
  is_cons(memory(cdr_bits(memory(cdr_bits(memory free))))) 
  ==>
  (!v w z zz.
    M_Cons(v,w,
           mem_abs(Store14(cdr_bits(memory free))
                          z
                          (Store14 free zz memory)),
           (cdr_bits((Store14 free zz memory)
                      (cdr_bits(memory free))))) = 
    (cdr_bits((Store14 free zz memory)
               (cdr_bits(memory free))),
     mem_abs(Store14(cdr_bits((Store14 free zz memory)
                               (cdr_bits(memory free))))
                    (bus32_cons_append #00 RT_CONS v w) 
                    (Store14(cdr_bits(memory free))
                             z
                            (Store14 free zz memory))),
     cdr_bits((Store14(cdr_bits(memory free))
                      z
                      (Store14 free zz memory))
               (cdr_bits((Store14 free zz memory)
                          (cdr_bits(memory free)))))))",
 REPEAT STRIP_TAC
 THEN IMP_RES_n_THEN 4
                     (port1 o (MATCH_MP cons_unfold_1_lemma) o SPEC_ALL)
		     M_Cons_3_precond_lemma
 THEN REFL_TAC
 );;

let cons_unfold_4_lemma = prove
("~(free = cdr_bits(memory free))                    /\
  ~(free = cdr_bits(memory(cdr_bits(memory free))))  /\
  ~(free =
    cdr_bits(memory(cdr_bits(memory(cdr_bits(memory free))))))  /\
  ~(cdr_bits(memory free) =
    cdr_bits(memory(cdr_bits(memory free))))         /\
  ~(cdr_bits(memory free) =
    cdr_bits(memory(cdr_bits(memory(cdr_bits(memory free))))))  /\
  ~(cdr_bits(memory(cdr_bits(memory free))) =
    cdr_bits(memory(cdr_bits(memory(cdr_bits(memory free))))))  /\
  is_cons
  (memory(cdr_bits(memory(cdr_bits(memory(cdr_bits(memory free)))))))
  ==>
  (!v w z zz zzz.
    M_Cons(v,w,
           mem_abs(Store14(cdr_bits((Store14 free zzz memory)
                                     (cdr_bits(memory free))))
                          z
                          (Store14(cdr_bits(memory free))
                                  zz
                                  (Store14 free zzz memory))),
           (cdr_bits((Store14(cdr_bits(memory free))
                             zz
                             (Store14 free zzz memory))
                      (cdr_bits((Store14 free zzz memory)
                                 (cdr_bits(memory free))))))) = 
    (cdr_bits((Store14(cdr_bits(memory free))
                      zz 
                      (Store14 free zzz memory))
               (cdr_bits((Store14 free zzz memory)
                          (cdr_bits(memory free))))),
     mem_abs(Store14(cdr_bits((Store14(cdr_bits(memory free))
                                       zz
                                       (Store14 free zzz memory))
                               (cdr_bits((Store14 free zzz memory)
                                          (cdr_bits(memory free))))))
                    (bus32_cons_append #00 RT_CONS v w) 
                    (Store14(cdr_bits((Store14 free zzz memory)
                                       (cdr_bits(memory free))))
                            z
                            (Store14(cdr_bits(memory free))
                                    zz
                                    (Store14 free zzz memory)))),
     cdr_bits((Store14(cdr_bits((Store14 free zzz memory)
                                 (cdr_bits(memory free))))
                      z
                      (Store14(cdr_bits(memory free))
                              zz
                              (Store14 free zzz memory)))
               (cdr_bits((Store14(cdr_bits(memory free))
                                 zz
                                 (Store14 free zzz memory))
                          (cdr_bits((Store14 free zzz memory)
                                     (cdr_bits(memory free)))))))))",
 REPEAT STRIP_TAC
 THEN IMP_RES_n_THEN 7
                     (port1 o (MATCH_MP cons_unfold_1_lemma) o SPEC_ALL)
		     M_Cons_4_precond_lemma
 THEN REFL_TAC
 );;

% ================================================================= %
% While the 4 cons_unfold_*_lemma's have the MINIMAL set of         %
% preconditions necessary for the proof of the result, we can relax %
% preconditions, so we OVERconstrain.  This is possible since the   %
% constraints used on the problem are the same, no matter how many  %
% memory writes occur in a sequence.  By reducing them all to the   %
% same SIMPLER precondition, we reduce the proof overhead later.    %
%                                                                   %
% A proof function is designed to handle all 4 theorems.  Typical:  %
%                                                                   %
% M_Cons_unfold_1_thm =                                             %
% |- reserved_words_constraint mpc memory /\                        %
%    well_formed_free_list memory mpc free s e c d ==>              %
%    (!t.                                                           %
%      (state_abs(mpc t) = top_of_cycle) ==>                        %
%      (!v w.                                                       %
%        M_Cons(v,w,mem_abs(memory t),free t) =                     %
%        free t,                                                    %
%        mem_abs                                                    %
%        (Store14(free t)                                           %
%                (bus32_cons_append #00 RT_CONS v w)                %
%                (memory t)),                                       %
%        cdr_bits(memory t(free t))))                               %
%                                                                   %
% M_Cons_unfold_4_thm =                                             %
% |- reserved_words_constraint mpc memory /\                        %
%    well_formed_free_list memory mpc free s e c d ==>              %
%    (!t.                                                           %
%      (state_abs(mpc t) = top_of_cycle) ==>                        %
%      (!v w z zz zzz.                                              %
%        let mem1 = Store14(free t)zzz(memory t) in                 %
%        let mem2 = Store14(cdr_bits(memory t(free t)))zz mem1 in   %
%        let mem3 = Store14                                         %
%          (cdr_bits(mem1(cdr_bits(memory t(free t)))))             %
%          z mem2 in                                                %
%        let mem4 = Store14                                         %
%           (cdr_bits(mem2(cdr_bits(mem1(cdr_bits(memory t(free t)  %
% 						       ))))))       %
%           (bus32_cons_append #00 RT_CONS v w) mem3 in             %
%       (M_Cons                                                     %
%           (v,w,mem_abs mem3,                                      %
%            cdr_bits(mem2(cdr_bits(mem1(cdr_bits(memory t(free t)  %
% 						       )))))) =     %
%           cdr_bits(mem2(cdr_bits(mem1(cdr_bits(memory t(free t)   %
% 						      ))))),        %
%           mem_abs mem4,                                           %
%           cdr_bits                                                %
%           (mem3                                                   %
%            (cdr_bits(mem2(cdr_bits(mem1(cdr_bits(memory t(free t) %
% 							)))))))     %
% ================================================================= %
let asm1 = "reserved_words_constraint mpc memory /\
            well_formed_free_list memory mpc free s e c d"
and asm2 = "state_abs(mpc (t:num)) = top_of_cycle";;

let well_formed_thm = 
(UNDISCH o (SPEC "t:num")
	 o (MP well_formed_free_list_lemma)
	 o ASSUME)
 asm1;;

let M_Cons_proof_fcn = 
 ((DISCH asm1)
  o (GEN "t:num")
  o (DISCH asm2)
  o (rr[well_formed_thm])
  o (SPECL["(memory:num->word14->word32) t";"(free:num->word14) t"])
  o (GENL ["memory:word14->word32";"free:word14"]));;

let M_Cons_unfold_1_thm =
    save_thm(`M_Cons_unfold_1_thm`,
	     M_Cons_proof_fcn cons_unfold_1_lemma);;
let M_Cons_unfold_2_thm =
    save_thm(`M_Cons_unfold_2_thm`,
	     M_Cons_proof_fcn cons_unfold_2_lemma);;
let M_Cons_unfold_3_thm =
    save_thm(`M_Cons_unfold_3_thm`,
	     M_Cons_proof_fcn cons_unfold_3_lemma);;
let M_Cons_unfold_4_thm =
    save_thm(`M_Cons_unfold_4_thm`,
	     M_Cons_proof_fcn cons_unfold_4_lemma);;

% ================================================================= %
% Still to be done: a similar series of proofs for storing          %
% numbers and symbols?????                                          %
% ================================================================= %

timer false;;
print_theory `-`;;
