% SECD verification                                                 %
%                                                                   %
% FILE:        dp_types.ml                                          %
%                                                                   %
% DESCRIPTION:  Declares the wordn types used by the datapath.      %
%               Also defines field selectors, and various data      %
%               type related constants and functions.               %
%                                                                   %
% USES FILES:   wordn and integer libraries                         %
%                                                                   %
% Brian Graham 88.04.21                                             %
%                                                                   %
% Modifications:                                                    %
% 15.04.91 - BtG - updated to HOL12                                 %
% 19.11.91 - BtG - updated to HOL2                                  %
% ================================================================= %
new_theory `dp_types`;;

loadt `wordn`;;
load_library `integer`;;
load_library `unwind`;;		% for: EXISTS_AND_CONV %
map loadt [ `CONJUNCTS_TAC`
          ; `SPLIT_CONJUNCTS`	% for: CONJ_EQ %
          ];;
map (load_definition `bus`)
[ `Concat`
; `Width`
; `Hd_bus`
; `Tl_bus`
];;
map (load_theorem `bus`)
[ `bus_axiom`
; `Wire_11`
; `Bus_11`
];;

timer true;;
% ================================================================= %
map (declare_wordn_type true)
     [ 2;  % garbage bits and type bits of record %
       14; % pointer size %
       28; % number size %
       32  % record size %
     ];;

timer false;;
map (load_theorem `-`)
[ `Word32`
; `Word32_Induct`
; `Word28_Induct`
; `Word14_Induct`
; `Word2_Induct`
; `Word32_11`
; `Word28_11`
; `Word14_11`
; `Word2_11`
; `Word32_Onto`
; `Word28_Onto`
; `Word14_Onto`
; `Word2_Onto`
; `Bits32_Word32`
; `Bits28_Word28`
; `Bits14_Word14`
; `Bits2_Word2`
];;
timer true;;

let NIL_addr  = new_definition
                (`NIL_addr`,   "NIL_addr  = #00000000000000")
and NUM_addr  = new_definition
                (`NUM_addr`,   "NUM_addr  = #11111111111111")
and T_addr    = new_definition
                (`T_addr`,     "T_addr    = #00000000000001")
and F_addr    = new_definition
                (`F_addr`,     "F_addr    = #00000000000010");;

let ZEROS14   = new_definition
                (`ZEROS14`,    "ZEROS14   = #00000000000000")
and ZERO28    = new_definition
                (`ZERO28`,     "ZERO28    = #0000000000000000000000000000");;

let RT_SYMBOL = new_definition
                (`RT_SYMBOL`,  "RT_SYMBOL = #10")
and RT_NUMBER = new_definition
                (`RT_NUMBER`,  "RT_NUMBER = #11")
and RT_CONS   = new_definition
               (`RT_CONS`,     "RT_CONS   = #00");;

% ================ sub-field extractor functions ================ %
% SEG and V are no longer defined in the system.  further, the    %
% definition of EL is reversed from the previous built-in defn.   %
% EL 0 l = hd l  instead of the last element.                     %
% thus, EL_CONV does weird things, and cannot be used.            %
% =============================================================== %
let w32 = "Word32 (Bus b32 (Bus b31 (Bus b30 (Bus b29 (Bus b28
                  (Bus b27 (Bus b26 (Bus b25 (Bus b24 (Bus b23
                  (Bus b22 (Bus b21 (Bus b20 (Bus b19 (Bus b18
                  (Bus b17 (Bus b16 (Bus b15 (Bus b14 (Bus b13
                  (Bus b12 (Bus b11 (Bus b10 (Bus b9  (Bus b8 
                  (Bus b7  (Bus b6  (Bus b5  (Bus b4  (Bus b3 
                  (Bus b2  (Wire (b1:bool)
                  ))))))))))))))))))))))))))))))))";;

let garbage_bits = new_recursive_definition false Word32
   `garbage_bits`
   "garbage_bits ^w32 = Word2 (Bus b32 (Wire b31))";;

let mark_bit = new_recursive_definition false Word32
   `mark_bit`
   "mark_bit ^w32 = (b32:bool)";;

let field_bit = new_recursive_definition false Word32
   `field_bit`
   "field_bit ^w32 = (b31:bool)";;

let rec_type_bits = new_recursive_definition false Word32
   `rec_type_bits`
   "rec_type_bits ^w32 = Word2 (Bus b30 (Wire b29))";;

let car_bits = new_recursive_definition false Word32
   `car_bits`
   "car_bits ^w32 =
    Word14 (Bus b28 (Bus b27 (Bus b26 (Bus b25 (Bus b24 (Bus b23
           (Bus b22 (Bus b21 (Bus b20 (Bus b19 (Bus b18 (Bus b17 
           (Bus b16 (Wire b15))))))))))))))";;

let cdr_bits = new_recursive_definition false Word32
   `cdr_bits`
   "cdr_bits ^w32 =
    Word14 (Bus b14 (Bus b13 (Bus b12 (Bus b11 (Bus b10 (Bus b9 
           (Bus b8  (Bus b7  (Bus b6  (Bus b5  (Bus b4  (Bus b3
           (Bus b2  (Wire b1))))))))))))))";;

let atom_bits = new_recursive_definition false Word32
   `atom_bits`
   "atom_bits ^w32 = 
    Word28 (Bus b28 (Bus b27 (Bus b26 (Bus b25 (Bus b24 (Bus b23
           (Bus b22 (Bus b21 (Bus b20 (Bus b19 (Bus b18 (Bus b17
           (Bus b16 (Bus b15 (Bus b14 (Bus b13 (Bus b12 (Bus b11
           (Bus b10 (Bus b9  (Bus b8  (Bus b7  (Bus b6  (Bus b5
           (Bus b4  (Bus b3  (Bus b2  (Wire b1)
                            )))))))))))))))))))))))))))";;

% ================ recognizer functions ========================= %
%    note that these operate only on the record type field        %
% Revised 89.09.07 - they now work on ":word32" arguments.        %
% =============================================================== %
let is_symbol = new_definition
  (`is_symbol`,
   "!x:word32. is_symbol x = (rec_type_bits x = RT_SYMBOL)"
  );;

let is_number = new_definition
  (`is_number`,
   "!x:word32. is_number x = (rec_type_bits x = RT_NUMBER)"
  );;

let is_cons = new_definition
  (`is_cons`,
   "!x:word32. is_cons x = (rec_type_bits x = RT_CONS)"
  );;

let is_atom = new_definition
  (`is_atom`,
   "!x:word32. is_atom x = (is_symbol x \/ is_number x)"
  );;

% ================= constructor function ======================== %
% Note the default always sets the gc bits to #00.                %
% =============================================================== %
let bus32_cons_append = new_definition
  (`bus32_cons_append`,
   "! (a:word2) (b:word2)(c:word14)(d:word14).
    bus32_cons_append a b c d =
        Word32 (Concat (Bits2 a)
                       (Concat (Bits2 b)
                               (Concat (Bits14 c) (Bits14 d))))"
  );;

let bus32_num_append = new_definition
  (`bus32_num_append`,
   "! (a:word28).
    bus32_num_append a =
        Word32 (Concat (Bits2 #00)
                       (Concat (Bits2 RT_NUMBER)
                               (Bits28 a)))"
  );;

let bus32_symb_append = new_definition
  (`bus32_symb_append`,
   "! (a:word28).
    bus32_symb_append a =
        Word32 (Concat (Bits2 #00)
                       (Concat (Bits2 RT_SYMBOL)
                               (Bits28 a)))"
  );;

let gc_bus32_append = new_definition
  (`gc_bus32_append`,
   "! (a:bool) (b:bool)(c:word32).
    gc_bus32_append a b c =
        Word32 (Bus a (Bus b (Tl_bus (Tl_bus (Bits32 c)))))"
  );;

close_theory ();;

let Word2_Cases = save_thm
(`Word2_Cases`,
 prove_wordn_const_cases Word2_Induct);;

let rec_types_DISTINCT = prove_thm
(`rec_types_DISTINCT`,
 "(~(RT_CONS   = RT_NUMBER)) /\
  (~(RT_CONS   = RT_SYMBOL)) /\
  (~(RT_NUMBER = RT_SYMBOL)) /\
  (~(RT_CONS   = #01))       /\
  (~(RT_NUMBER = #01))       /\
  (~(RT_SYMBOL = #01))",
 port[RT_NUMBER; RT_CONS; RT_SYMBOL]
 THEN in_conv_tac wordn_CONV
 THEN port[Word2_11]
 THEN prt[Bus_11; Wire_11]
 THEN rt[]);;

let mf_of_garbage_bits = prove_thm
(`mf_of_garbage_bits`,
 "!w32. (mark_bit w32 = Hd_bus(Bits2(garbage_bits w32))) /\
        (field_bit w32 = Hd_bus(Tl_bus(Bits2(garbage_bits w32))))",
 INDUCT_THEN Word32_Induct ASSUME_TAC
 THEN REPEAT GEN_TAC THEN port[mark_bit; field_bit; garbage_bits]
 THEN port[Bits2_Word2]
 THEN rt[Hd_bus; Tl_bus]
 );;

let records_distinct = prove_thm
(`records_distinct`,
 "(is_cons x ==> ~(is_number x)) /\
  (is_cons x ==> ~(is_symbol x)) /\
  (is_number x ==> ~(is_cons x)) /\
  (is_number x ==> ~(is_symbol x)) /\
  (is_symbol x ==> ~(is_cons x)) /\
  (is_symbol x ==> ~(is_number x))",
 port[is_cons; is_number; is_symbol]
 THEN REPEAT CONJ_TAC
 THEN DISCH_THEN SUBST1_TAC
 THEN rt[rec_types_DISTINCT; SYM_RULE rec_types_DISTINCT]
 );;


% ================= useful lemma ??????? ======================== %
let bus32_cons_append_lemma = prove_thm
  (`bus32_cons_append_lemma`,
   "bus32_cons_append (Word2 (Bus b32 (Wire b31)))
                      (Word2 (Bus b30 (Wire b29)))
                      (Word14 (Bus b28 (Bus b27 (Bus b26 (Bus b25
                              (Bus b24 (Bus b23 (Bus b22 (Bus b21
                              (Bus b20 (Bus b19 (Bus b18 (Bus b17
                              (Bus b16 (Wire b15)))))))))))))))
                      (Word14 (Bus b14 (Bus b13 (Bus b12 (Bus b11
                              (Bus b10 (Bus b9  (Bus b8  (Bus b7
                              (Bus b6  (Bus b5  (Bus b4  (Bus b3
                              (Bus b2  (Wire (b1:bool)))))))))))))))) =
        Word32    (Bus b32 (Bus b31 (Bus b30 (Bus b29 (Bus b28
                  (Bus b27 (Bus b26 (Bus b25 (Bus b24 (Bus b23
                  (Bus b22 (Bus b21 (Bus b20 (Bus b19 (Bus b18
                  (Bus b17 (Bus b16 (Bus b15 (Bus b14 (Bus b13
                  (Bus b12 (Bus b11 (Bus b10 (Bus b9  (Bus b8
                  (Bus b7  (Bus b6  (Bus b5  (Bus b4  (Bus b3
                  (Bus b2  (Wire (b1:bool) ))))))))))))))))))))))))))))))))
    ",
   prt [Bits14_Word14; Bits2_Word2; bus32_cons_append; Concat]
   THEN REFL_TAC
   );;


% ================================================================= %
% A theorem to show that the fields of a bus32_cons_append object   %
% are equal to the function arguments.                              %
%                                                                   %
% The proofs are particularly inelegant, but they work...           %
%                                                                   %
% Similar theorems will be needed for num and gc appended records.  %
% ================================================================= %
let bus32_cons_fields_lemma = prove_thm
(`bus32_cons_fields_lemma`,
 "!a w x y.
    (garbage_bits a = y) /\
    (rec_type_bits a = RT_CONS) /\
    (car_bits a = w) /\
    (cdr_bits a = x) =
    (a = bus32_cons_append y RT_CONS w x)",
 REPEAT GEN_TAC
 THEN port[RT_CONS]
 THEN in1_conv_tac wordn_CONV
 THEN (REPEAT_TCL CHOOSE_THEN)
      (\th.port[th])
      (SPEC "w:word14" Word14_Onto)
 THEN (REPEAT_TCL CHOOSE_THEN)
      (\th.port[th])
      (SPEC "x:word14" Word14_Onto)
 THEN (REPEAT_TCL CHOOSE_THEN)
      (\th.port[th])
      (SPEC "y:word2" Word2_Onto)
 THEN (REPEAT_TCL CHOOSE_THEN)
      (\th.port[th])
      (SPEC "a:word32" Word32_Onto)
 THEN port[bus32_cons_append_lemma]
 THEN port [garbage_bits; rec_type_bits; car_bits; cdr_bits]
 THEN port[Word2_11; Word14_11; Word32_11]
 THEN prt[Bus_11; Wire_11]
 THEN CONJUNCTS_TAC
 );;

% ================================================================= %
% bus32_cons_fields_lemma_1 =                                       %
% |- (garbage_bits(bus32_cons_append y RT_CONS w x) = y) /\         %
%    (rec_type_bits(bus32_cons_append y RT_CONS w x) = RT_CONS) /\  %
%    (car_bits(bus32_cons_append y RT_CONS w x) = w) /\             %
%    (cdr_bits(bus32_cons_append y RT_CONS w x) = x)                %
% ================================================================= %
let bus32_cons_fields_lemma_1 = save_thm
(`bus32_cons_fields_lemma_1`,
  rr[]
    (SPECL [ "bus32_cons_append y RT_CONS w x"
	   ; "w:word14"
           ; "x:word14"
           ; "y:word2"   ]
           bus32_cons_fields_lemma
    )
);;

% ================================================================= %
% addr_to_num_lemma =                                               %
% |- !y z. ?x. (cdr_bits x = y) /\ (car_bits x = z)                 %
% ================================================================= %
let addr_to_num_lemma = TAC_PROOF
(([], "!y z.?x. (cdr_bits x = y) /\ (car_bits x = z)"),
 REPEAT GEN_TAC
 THEN EXISTS_TAC "bus32_cons_append #00 RT_CONS z y"
 THEN port[bus32_cons_fields_lemma_1]
 THEN rt[]);;

% ================================================================= %
% addr_to_num_inst =                                                %
% |- !y z XXX.                                                      %
%    (?x. (cdr_bits x = y) /\ (car_bits x = z) /\ XXX) = XXX        %
% ================================================================= %
let addr_to_num_inst = prove_thm
(`addr_to_num_inst`,
 "!y z.(?x. (cdr_bits x = y) /\ (car_bits x = z) /\ XXX) = XXX",
 REPEAT GEN_TAC
 THEN port[CONJ_ASSOC]
 THEN in1_conv_tac EXISTS_AND_CONV
 THEN port[addr_to_num_lemma]
 THEN rt[]);;

% ================================================================= %
% bus_append_lemma =                                                %
% |- (garbage_bits a = y) /\                                        %
%    (rec_type_bits a = RT_CONS) /\                                 %
%    (car_bits a = w) /\                                            %
%    (cdr_bits a = x) /\                                            %
%    XXX =                                                          %
%    (a = bus32_cons_append y RT_CONS w x) /\ XXX                   %
% ================================================================= %
let bus_append_lemma = save_thm
(`bus_append_lemma`,
  prr[SYM_RULE CONJ_ASSOC]
     (CONJ_EQ (SPEC_ALL bus32_cons_fields_lemma) (REFL "XXX:bool")));;

% ================================================================= %
% The same sort of thing for a number record.                       %
% ================================================================= %
let bus32_num_fields_lemma = prove_thm
(`bus32_num_fields_lemma`,
 "!a w.
    (garbage_bits a = #00) /\
    (rec_type_bits a = RT_NUMBER) /\
    (atom_bits a = w) =
    (a = bus32_num_append w)",
 REPEAT GEN_TAC
 THEN port [bus32_num_append]
 THEN port [RT_NUMBER]
 THEN in1_conv_tac wordn_CONV
 THEN (REPEAT_TCL CHOOSE_THEN)
      (\th.port[th])
      (SPEC "w:word28" Word28_Onto)
 THEN (REPEAT_TCL CHOOSE_THEN)
      (\th.port[th])
      (SPEC "a:word32" Word32_Onto)
 THEN port [garbage_bits; rec_type_bits; atom_bits]
 THEN prt [Bits2_Word2; Bits28_Word28]
 THEN prt[Concat]
 THEN port[Word2_11; Word28_11; Word32_11]
 THEN prt[Bus_11; Wire_11]
 THEN CONJUNCTS_TAC
 );;

% ================================================================= %
% bus32_num_fields_lemma_1 =                                        %
% |- (garbage_bits(bus32_num_append w) = #00) /\                    %
%    (rec_type_bits(bus32_num_append w) = RT_NUMBER) /\             %
%    (atom_bits(bus32_num_append w) = w)                            %
% ================================================================= %
let bus32_num_fields_lemma_1 = save_thm
(`bus32_num_fields_lemma_1`,
 rr[](SPECL ["bus32_num_append w"; "w:word28"] bus32_num_fields_lemma));;

% ================================================================= %
% The same sort of thing for a symbol record.                       %
% ================================================================= %
let bus32_symb_fields_lemma = TAC_PROOF
(([], "!a z.(garbage_bits a = #00) /\
    (rec_type_bits a = RT_SYMBOL) /\
    (atom_bits a = z) =
    (a = bus32_symb_append z)"),
 REPEAT GEN_TAC
 THEN (REPEAT_TCL CHOOSE_THEN)
      (\th.port[th])
      (SPEC "z:word28" Word28_Onto)
 THEN (REPEAT_TCL CHOOSE_THEN)
      (\th.port[th])
      (SPEC "a:word32" Word32_Onto)
 THEN port[bus32_symb_append]
 THEN port[RT_SYMBOL]
 THEN in1_conv_tac wordn_CONV
 THEN port[garbage_bits; rec_type_bits; atom_bits]
 THEN prt[Bits28_Word28; Bits2_Word2]
 THEN prt[Concat]
 THEN port[Word2_11; Word28_11; Word32_11]
 THEN prt[Bus_11; Wire_11]
 THEN CONJUNCTS_TAC
 );;

let bus32_symb_fields_lemma = save_thm
(`bus32_symb_fields_lemma`,
 GEN "z:word28"
 (rr[]
    (SPECL ["bus32_symb_append z"; "z:word28"]
	   bus32_symb_fields_lemma)));;
% ================================================================= %
% The following 2 theorems are used in eliminating the              %
% existentially quantified "bus" when unwinding the imp.            %
% They are really data-type sort of theorems, so are included here. %
% ================================================================= %
let car_bits_thm = prove_thm
(`car_bits_thm`,
 "!y. ?x. car_bits x = y",
 GEN_TAC
 THEN EXISTS_TAC  
      "bus32_cons_append (Word2 (Bus F(Wire F)))                   
                        (Word2 (Bus F(Wire F))) y y"
 THEN (REPEAT_TCL CHOOSE_THEN)
       (\th.prt[th; car_bits; Bits14_Word14; bus32_cons_append_lemma])
       (SPEC "y:word14" Word14_Onto)
 THEN REFL_TAC
 );;

let cdr_bits_thm = prove_thm
 (`cdr_bits_thm`,
  "!y.?x. cdr_bits x = y",
  GEN_TAC
  THEN EXISTS_TAC
       "Word32(Bus F(Bus F(Bus F(Bus F(Bus F(Bus F(Bus F(Bus F
               (Bus F(Bus F(Bus F(Bus F(Bus F(Bus F(Bus F(Bus F
                (Bus F(Bus F(Bits14 y)))))))))))))))))))"
  THEN (REPEAT_TCL CHOOSE_THEN)
       (\th.prt[cdr_bits;Bits14_Word14; th])
       (SPEC "y:word14" Word14_Onto)
  THEN REFL_TAC
  );;

let atom_rec_equivalence = prove_thm
(`atom_rec_equivalence`,
 "!x y.(garbage_bits x = garbage_bits y) /\
       (rec_type_bits x = rec_type_bits y) /\
       (atom_bits x = atom_bits y) =
       (x = y)",
 INDUCT_THEN Word32_Induct ASSUME_TAC
 THEN GEN_TAC THEN GEN_TAC THEN GEN_TAC THEN GEN_TAC
 THEN GEN_TAC THEN GEN_TAC THEN GEN_TAC THEN GEN_TAC
 THEN GEN_TAC THEN GEN_TAC THEN GEN_TAC THEN GEN_TAC
 THEN GEN_TAC THEN GEN_TAC THEN GEN_TAC THEN GEN_TAC
 THEN GEN_TAC THEN GEN_TAC THEN GEN_TAC THEN GEN_TAC
 THEN GEN_TAC THEN GEN_TAC THEN GEN_TAC THEN GEN_TAC
 THEN GEN_TAC THEN GEN_TAC THEN GEN_TAC THEN GEN_TAC
 THEN GEN_TAC THEN GEN_TAC THEN GEN_TAC THEN GEN_TAC
 THEN INDUCT_THEN Word32_Induct ASSUME_TAC
 THEN REPEAT GEN_TAC
 THEN prt [garbage_bits; rec_type_bits; atom_bits]
 THEN prt [Word32_11; Word28_11; Word2_11]
 THEN prt[Wire_11; Bus_11]
 THEN EQ_TAC
 THEN STRIP_TAC
 THEN art[]
 );;

timer false;;
print_theory `-`;;
