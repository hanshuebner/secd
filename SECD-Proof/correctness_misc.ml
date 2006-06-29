% SECD verification                                                 %
%                                                                   %
% FILE:         correctness_misc.ml                                 %
%                                                                   %
% DESCRIPTION:  This proves some miscellaneous repetitive           %
%               things needed in the correctness proofs.            %
%                                                                   %
% USES FILES:   mem_abs.th                                          %
%                                                                   %
% Brian Graham 90.05.10                                             %
%                                                                   %
% Modifications:                                                    %
% 06.08.91 - BtG - updated to HOL2                                  %
% ================================================================= %
new_theory `correctness_misc`;;

loadf `wordn`;;
new_parent `mem_abs`;;
% ================================================================= %
let mtime = ":num";;

let msig = ":^mtime->bool"
and w9_mvec = ":^mtime->word9"
and w14_mvec = ":^mtime->word14"
and w27_mvec = ":^mtime->word27"
and w32_mvec = ":^mtime->word32";;

let mem14_32 = ":word14->word32";;
let m14_32_mvec = ":^mtime->^mem14_32";;
let M = ":(word14,atom)mfsexp_mem";;
let M_mvec = ":^mtime->^M";;
% ================================================================= %
map (load_definition `constraints`) 
[ `all_cdr_path`
; `path`
; `nonintersecting`
];;
map (load_theorem `constraints`)
[ `Store14_1_lemma`
; `Store14_2_lemma`
; `Store14_3_lemma`
; `Store14_4_lemma`
; `NIL_not_cons`
];;

timer true;;
% ================================================================= %
%%

let atom_opcode_lemma = prove
("(atom_bits w32 =
    Word28(Bus b28(Bus b27(Bus b26(Bus b25(Bus b24(Bus b23(Bus b22
          (Bus b21(Bus b20(Bus b19(Bus b18(Bus b17(Bus b16(Bus b15
          (Bus b14(Bus b13(Bus b12(Bus b11(Bus b10(Bus b9 (Bus b8 
          (Bus b7 (Bus b6 (Bus b5 (Bus b4 (Bus b3 (Bus b2 (Wire b1
          ))))))))))))))))))))))))))))) ==>
   (opcode_bits w32 =
    Word9(Bus b9 (Bus b8 (Bus b7 (Bus b6 (Bus b5 (Bus b4 (Bus b3
          (Bus b2 (Wire b1))))))))))",
 DISCH_THEN
 (\th.
  (SUBST1_TAC 
   o (porr[theorem `constraints` `EQ_atom_IMP_EQ_opcode`])
   o (porr[definition `rt_SECD` `opcode_bits`])
   o (porr[theorem `dp_types` `Bits28_Word28`])
   o (in_conv_rule BETA_CONV)
   o (AP_TERM "\w28. opcode_bits(Word32(Bus F(Bus F
                (Bus T(Bus T(Bits28 w28))))))"))
  th)
 THEN REFL_TAC);; 

map (\(t9, t28, name).
     (prove_thm
      (name,
       "!w32. (atom_bits w32 = ^t28) ==>
              (opcode_bits w32 = ^t9)",
       GEN_TAC THEN in1_conv_tac wordn_CONV
               THEN MATCH_ACCEPT_TAC atom_opcode_lemma)))
  [ "#000000001","#0000000000000000000000000001", `LD_opcode_lemma`
  ; "#000000010","#0000000000000000000000000010", `LDC_opcode_lemma`
  ; "#000000011","#0000000000000000000000000011", `LDF_opcode_lemma` 
  ; "#000000100","#0000000000000000000000000100", `AP_opcode_lemma`
  ; "#000000101","#0000000000000000000000000101", `RTN_opcode_lemma`
  ; "#000000110","#0000000000000000000000000110", `DUM_opcode_lemma`
  ; "#000000111","#0000000000000000000000000111", `RAP_opcode_lemma`
  ; "#000001000","#0000000000000000000000001000", `SEL_opcode_lemma`
  ; "#000001001","#0000000000000000000000001001", `JOIN_opcode_lemma`
  ; "#000001010","#0000000000000000000000001010", `CAR_opcode_lemma`
  ; "#000001011","#0000000000000000000000001011", `CDR_opcode_lemma`
  ; "#000001100","#0000000000000000000000001100", `ATOM_opcode_lemma`
  ; "#000001101","#0000000000000000000000001101", `CONS_opcode_lemma`
  ; "#000001110","#0000000000000000000000001110", `EQ_opcode_lemma`
  ; "#000001111","#0000000000000000000000001111", `ADD_opcode_lemma`
  ; "#000010000","#0000000000000000000000010000", `SUB_opcode_lemma`
% ; "#000010001","#0000000000000000000000010001", `MUL_opcode_lemma` %
% ; "#000010010","#0000000000000000000000010010", `DIV_opcode_lemma` %
% ; "#000010011","#0000000000000000000000010011", `REM_opcode_lemma` %
  ; "#000010100","#0000000000000000000000010100", `LEQ_opcode_lemma`
  ; "#000010101","#0000000000000000000000010101", `STOP_opcode_lemma`
  ];;

% ================================================================= %
% Quicker rewriting of LET bindings:                                %
% ================================================================= %
let LET_THM = prove_thm
(`LET_THM`,
 "LET (f:*->**) (x:*) = f x",
 port[LET_DEF]
 THEN BETA_TAC
 THEN REFL_TAC);;

% ================================================================= %
% The first 4 cons cells in the free list are all not in the path   %
% from a nonintersecting datastructure in the ORIGINAL memory.      %
% ================================================================= %
let nonintersecting_free_1_lemma = prove
("(is_cons(mem free)) /\
  (mem NIL_addr = bus32_symb_append #0000000000000000000000000000) /\
  (nonintersecting mem free v) ==>
  !p. ~(free = path mem v p)",
 port[nonintersecting]
 THEN DISCH_THEN
 ((\[th1;th2;th3].
   GEN_TAC
   THEN ((MATCH_ACCEPT_TAC
	  o SYM_RULE
 	  o (\th4.MATCH_MP th4(MATCH_MP(MATCH_MP NIL_not_cons th2)th1))
	  o (rr[path;all_cdr_path])
	  o (SPECL ["p:(bool)list";"[]:bool list"]))
	 th3))
  o CONJUNCTS)
 );;

let nonintersecting_free_2_lemma = prove
("(is_cons(mem free)) /\
  (is_cons(mem(cdr_bits(mem free)))) /\
  (mem NIL_addr = bus32_symb_append #0000000000000000000000000000) /\
  (nonintersecting mem free v) ==>
  !p. ~(cdr_bits(mem free) = path mem v p)",
 port[nonintersecting]
 THEN DISCH_THEN
 ((\[th1;th2;th3;th4].
   GEN_TAC
   THEN ((MATCH_ACCEPT_TAC
	  o SYM_RULE
 	  o (\th5.MATCH_MP th5(MATCH_MP(SPEC_ALL(MATCH_MP NIL_not_cons th3))th2))
	  o (rr[path;all_cdr_path;th1])
	  o (SPECL ["p:(bool)list";"[T]"]))th4)
	   )
  o CONJUNCTS)
 );;

let nonintersecting_free_3_lemma = prove
("(is_cons(mem free)) /\
  (is_cons(mem(cdr_bits(mem free)))) /\
  (is_cons(mem(cdr_bits(mem(cdr_bits(mem free)))))) /\
  (mem NIL_addr = bus32_symb_append #0000000000000000000000000000) /\
  (nonintersecting mem free v) ==>
  !p. ~(cdr_bits(mem(cdr_bits(mem free))) = path mem v p)",
 port[nonintersecting]
 THEN DISCH_THEN
 ((\[th1;th2;th3;th4;th5].
   GEN_TAC
   THEN ((MATCH_ACCEPT_TAC
	  o SYM_RULE
 	  o (\th6.MATCH_MP th6(MATCH_MP(SPEC_ALL(MATCH_MP NIL_not_cons th4))th3))
	  o (rr[path;all_cdr_path;th1;th2])
	  o (SPECL ["p:(bool)list";"[T;T]"]))th5)
	   )
  o CONJUNCTS)
 );;
%%
let nonintersecting_free_4_lemma = prove
("(is_cons(mem free)) /\
  (is_cons(mem(cdr_bits(mem free)))) /\
  (is_cons(mem(cdr_bits(mem(cdr_bits(mem free)))))) /\
  (is_cons(mem(cdr_bits(mem(cdr_bits(mem(cdr_bits(mem free)))))))) /\
  (mem NIL_addr = bus32_symb_append #0000000000000000000000000000) /\
  (nonintersecting mem free v) ==>
  !p. ~(cdr_bits(mem(cdr_bits(mem(cdr_bits(mem free))))) =
        path mem v p)",
 port[nonintersecting]
 THEN DISCH_THEN
 ((\[th1;th2;th3;th4;th5;th6].
   GEN_TAC
   THEN ((MATCH_ACCEPT_TAC
	  o SYM_RULE
 	  o (\th7.MATCH_MP th7(MATCH_MP(SPEC_ALL(MATCH_MP NIL_not_cons th5))th4))
	  o (rr[path;all_cdr_path;th1;th2;th3])
	  o (SPECL ["p:(bool)list";"[T;T;T]"]))th6)
	   )
  o CONJUNCTS)
 );;

% ================================================================= %
% Just making variable names match, for substitution ....           %
% ================================================================= %
let Store14_1_lemma =
 SPEC "mem:word14->word32"
      (GEN "memory:word14->word32" Store14_1_lemma);;

%%
% ================================================================= %
% If a cell is nonintersecting with the free list, then so are      %
% both its car and cdr.                                             %
% ================================================================= %
let nonintersecting_car_cdr_lemma = prove
("nonintersecting mem free v ==>
  is_cons (mem v)            ==>
  nonintersecting mem free (cdr_bits(mem v)) /\
  nonintersecting mem free (car_bits(mem v))",
 port[nonintersecting]
 THEN DISCH_THEN (\th1. 
      DISCH_THEN \th2.
             CONJ_TAC
             THEN REPEAT GEN_TAC
	     THENL
	     [ ASSUME_TAC (rr[th2;path](SPEC "CONS T l1" th1))
             ; ASSUME_TAC (rr[th2;path](SPEC "CONS F l1" th1))]
     THEN REPEAT STRIP_TAC
     THEN RES_TAC)
 );;

%< 
% ================================================================= %
% The desired set of theorems to relate cells over updates to       %
% memory.  ie. all cells in data structure paths are unchanged      %
% by memory updates under the normal set of constraints on the free %
% list.                                                             %
%                                                                   %
% Note that the formulation uses let bindings in order to make      %
% the regularity of the pattern be obvious.                         %
% ================================================================= %
 "(is_cons(mem free)) /\
  (mem NIL_addr = bus32_symb_append #0000000000000000000000000000)==>
  !p v.
  (nonintersecting mem free v) ==>
  !cell1.
   let mem1 = (Store14 free cell1 mem) in
    path mem1 v p = path mem v p"

 "(is_cons(mem free)) /\
  (is_cons(mem(cdr_bits(mem free)))) /\
  (mem NIL_addr = bus32_symb_append #0000000000000000000000000000)==>
  !p v.
  (nonintersecting mem free v) ==>
  !cell1 cell2.
   let mem1 = Store14 free cell1 mem in
   let mem2 = Store14 (cdr_bits(mem free)) cell2 mem1 in
    path mem2 v p = path mem v p"

 "(is_cons(mem free)) /\
  (is_cons(mem(cdr_bits(mem free)))) /\
  (is_cons(mem(cdr_bits(mem(cdr_bits(mem free)))))) /\
  (~(free = cdr_bits(mem free))) /\
  (mem NIL_addr = bus32_symb_append #0000000000000000000000000000)==>
  !p v.
  (nonintersecting mem free v) ==>
  !cell1 cell2 cell3.
   let mem1 = Store14 free cell1 mem in
   let mem2 = Store14 (cdr_bits(mem free)) cell2 mem1 in
   let mem3 =
       Store14 (cdr_bits(mem1(cdr_bits(mem free)))) cell3 mem2 in
    path mem3 v p = path mem v p"

 "(is_cons(mem free)) /\
  (is_cons(mem(cdr_bits(mem free)))) /\
  (is_cons(mem(cdr_bits(mem(cdr_bits(mem free)))))) /\
  (is_cons(mem(cdr_bits(mem(cdr_bits(mem(cdr_bits(mem free)))))))) /\
  (~(free = cdr_bits(mem free))) /\
  (~(free = cdr_bits(mem(cdr_bits(mem free))))) /\
  (~(cdr_bits(mem free) = cdr_bits(mem(cdr_bits(mem free))))) /\
  (mem NIL_addr = bus32_symb_append #0000000000000000000000000000)==>
  !p v.
  (nonintersecting mem free v) ==>
  !cell1 cell2 cell3.
   let mem1 = Store14 free cell1 mem in
   let mem2 = Store14 (cdr_bits(mem free)) cell2 mem1 in
   let mem3 =
           Store14 (cdr_bits(mem1(cdr_bits(mem free)))) cell3 mem2 in
   let mem4 =
           Store14 (cdr_bits(mem2(cdr_bits(mem1(cdr_bits(mem free))))))
                   cell4 mem3 in
    path mem4 v p = path mem v p"
>%
%%
% ================================================================= %
% If free list is nonempty and linear,                              %
% and NIL reserved word is in place,                                %
% then if free list and v are nonintersecting,                      %
%      then the new memory at any location referenced by a path in  %
%           the OLD memory is the same as the old memory location   %
%           at the path through the old memory.                     %
%                                                                   %
% Hopefully, this is the strongest result that will be needed for   %
% the proof of correspondence of each instruction execution and     %
% specification.                                  90.09.07 - BtG    %
%                                                                   %
% Notice that the memory in the path on the lhs of the equality     %
% is the original memory.  To apply when an updated memory is       %
% in the path, this must first be simplified, generally by using    %
% Store14_path_*_thm's, before applying one of the following        %
% theorems.                                                         %
%                                                                   %
% Note: this excludes the cells themselves from the equality!       %
%                                                                   %
% The let form of specifying updated memories is included for       %
% documentation purposes, as it is simpler to read....  The         %
% theorems were originally proved in this form, and later changed   %
% to the form given here.  The final form was obtained by rewriting %
% the "let" forms using the HOL system, so are likely correct...!   %
% ================================================================= %
let Store14_oldpath_1_lemma = prove
("(is_cons(mem free)) /\
  (mem NIL_addr = bus32_symb_append #0000000000000000000000000000)==>
  !v.
  (nonintersecting mem free v) ==>
   (!p cell1.
     Store14 free cell1 mem(path mem v p) =
                        mem(path mem v p))",
%
    let mem1 = (Store14 free cell1 mem) in
       mem1(path mem v p) = mem(path mem v p) 
%
 REPEAT STRIP_TAC
 THEN IMP_RES_n_THEN 3
      (ASSUME_TAC o (SPEC "p:bool list"))
      nonintersecting_free_1_lemma
 THEN IMP_RES_THEN (MATCH_ACCEPT_TAC o SYM_RULE)
                   (SPEC "mem:^mem14_32"
			 (GEN "memory:^mem14_32" Store14_1_lemma))
 );;

%%
let Store14_oldpath_2_lemma = prove
("(is_cons(mem free)) /\
  (is_cons(mem(cdr_bits(mem free)))) /\
  (mem NIL_addr = bus32_symb_append #0000000000000000000000000000)==>
  !v.
  (nonintersecting mem free v) ==>
   (!p cell1 cell2.
     Store14
     (cdr_bits(mem free))
     cell2
     (Store14 free cell1 mem)
     (path mem v p) =
     mem(path mem v p))",
%
   let mem1 = Store14 free cell1 mem in
   let mem2 = Store14 (cdr_bits(mem free)) cell2 mem1 in
    mem2(path mem v p) = mem(path mem v p)
%
 REPEAT STRIP_TAC 
 THEN IMP_RES_n_THEN 4
      (ASSUME_TAC o (SPEC "p:bool list"))
      nonintersecting_free_2_lemma
 THEN IMP_RES_n_THEN 3
      (ASSUME_TAC o (SPEC "p:bool list"))
      nonintersecting_free_1_lemma
 THEN IMP_RES_n_THEN 2
      (MATCH_ACCEPT_TAC o SYM_RULE)
      (hd(IMP_CANON (SPEC "mem:^mem14_32"
			  (GEN "memory:^mem14_32"Store14_2_lemma))))
 );;

let Store14_oldpath_3_lemma = prove
("(is_cons(mem free)) /\
  (is_cons(mem(cdr_bits(mem free)))) /\
  (is_cons(mem(cdr_bits(mem(cdr_bits(mem free)))))) /\
  (~(free = cdr_bits(mem free))) /\
  (mem NIL_addr = bus32_symb_append #0000000000000000000000000000)==>
  !v.
  (nonintersecting mem free v) ==>
  (!p cell1 cell2 cell3.
     Store14
     (cdr_bits(Store14 free cell1 mem(cdr_bits(mem free))))
     cell3
     (Store14(cdr_bits(mem free))cell2(Store14 free cell1 mem))
     (path mem v p) =
     mem(path mem v p))",
%
  !cell1 cell2 cell3.
   let mem1 = Store14 free cell1 mem in
   let mem2 = Store14 (cdr_bits(mem free)) cell2 mem1 in
   let mem3 =
       Store14 (cdr_bits(mem1(cdr_bits(mem free)))) cell3 mem2 in
    mem3(path mem v p) = mem(path mem v p)
%
 REPEAT STRIP_TAC 
 THEN IMP_RES_n_THEN 5
      (ASSUME_TAC o (SPEC "p:bool list"))
      nonintersecting_free_3_lemma
 THEN IMP_RES_n_THEN 4
      (ASSUME_TAC o (SPEC "p:bool list"))
      nonintersecting_free_2_lemma
 THEN IMP_RES_n_THEN 3
      (ASSUME_TAC o (SPEC "p:bool list"))
      nonintersecting_free_1_lemma
 THEN IMP_RES_n_THEN 4
      (MATCH_ACCEPT_TAC o SYM_RULE)
      (hd(IMP_CANON (SPEC "mem:^mem14_32"
			  (GEN "memory:^mem14_32"Store14_3_lemma))))
 );;
%%
let Store14_oldpath_4_lemma = prove
("(is_cons(mem free)) /\
  (is_cons(mem(cdr_bits(mem free)))) /\
  (is_cons(mem(cdr_bits(mem(cdr_bits(mem free)))))) /\
  (is_cons(mem(cdr_bits(mem(cdr_bits(mem(cdr_bits(mem free)))))))) /\
  (~(free = cdr_bits(mem free))) /\
  (~(free = cdr_bits(mem(cdr_bits(mem free))))) /\
  (~(cdr_bits(mem free) = cdr_bits(mem(cdr_bits(mem free))))) /\
  (mem NIL_addr = bus32_symb_append #0000000000000000000000000000)==>
  !v.
  (nonintersecting mem free v) ==>
   (!p cell1 cell2 cell3 cell4.
     Store14
     (cdr_bits
      (Store14
       (cdr_bits(mem free))
       cell2
       (Store14 free cell1 mem)
       (cdr_bits(Store14 free cell1 mem(cdr_bits(mem free))))))
     cell4
     (Store14
      (cdr_bits(Store14 free cell1 mem(cdr_bits(mem free))))
      cell3
      (Store14(cdr_bits(mem free))cell2(Store14 free cell1 mem)))
     (path mem v p) =
     mem(path mem v p))",
%
   let mem1 = Store14 free cell1 mem in
   let mem2 = Store14 (cdr_bits(mem free)) cell2 mem1 in
   let mem3 =
           Store14 (cdr_bits(mem1(cdr_bits(mem free)))) cell3 mem2 in
   let mem4 =
           Store14 (cdr_bits(mem2(cdr_bits(mem1(cdr_bits(mem free))))))
                   cell4 mem3 in
    mem4(path mem v p) = mem(path mem v p)
%
 REPEAT STRIP_TAC 
 THEN IMP_RES_n_THEN 6
      (ASSUME_TAC o (SPEC "p:bool list"))
      nonintersecting_free_4_lemma
 THEN IMP_RES_n_THEN 5
      (ASSUME_TAC o (SPEC "p:bool list"))
      nonintersecting_free_3_lemma
 THEN IMP_RES_n_THEN 4
      (ASSUME_TAC o (SPEC "p:bool list"))
      nonintersecting_free_2_lemma
 THEN IMP_RES_n_THEN 3
      (ASSUME_TAC o (SPEC "p:bool list"))
      nonintersecting_free_1_lemma
 THEN IMP_RES_n_THEN 7
      (MATCH_ACCEPT_TAC o SYM_RULE)
      (hd(IMP_CANON (SPEC "mem:^mem14_32"
			  (GEN "memory:^mem14_32" Store14_4_lemma))))
 );;

%%
% ================================================================= %
% If free list is nonempty and linear,                              %
% and NIL reserved word is in place,                                %
% then if free list and v are nonintersecting,                      %
%      then any path through the new memory is the same as          %
%           the same path through the old memory.                   %
%                                                                   %
% Note: this excludes the memory locations from the equality!       %
%                                                                   %
% This complex looking proof proceeds as follows:                   %
% - Strip lhs of implication.                                       %
% - Induct on "p", specializing "v" of ind. assum. to an expression %
%   that evaluates to the same cell as the inductive goal case,     %
%   AFTER generalizing all variables in goal.                       %
% - Rewrite with path: solves base case.                            %
% - Strip off nonintersecting assumption, GENeralize "cell",        %
%   RESOLVE nonintersecting_free_1_lemma with asm list              %
%   and this asm., then SPECialize to the null list, getting the    %
%   result that "~(free = v)", which is MP'ed with                  %
%   Store14_1_lemma, and the result:                                %
%   "Store14 free cell mem v = mem v", used to rewrite the goal.    %
%   The nonintersecting asm. is also MP'ed with                     %
%   nonintersection_car_cdr_lemma and result added to asm. list.    %
% - Do a COND_CASES on "is_cons(mem v)".  The "F" branch is         %
%   trivial: "v = v".  The "T" branch must show that paths starting %
%   from both the car and cdr of "v" are unchanged by the "Store14".%
% - Substitute the "T" assumption in the ind. assum. and also       %
%   resolve with the asm from nonintersecting_car_cdr_lemma.        %
% - Do the COND_CASES on the head of the path list ("h"),           %
%   substituting into the ind. assum.                               %
% - Simplify the ind. assum. and goal.                              %
% - RESOLVE the appropriate case of nonintersecting_car_cdr_lemma   %
% with the ind. assum., and match it to the goal, for both branches.%
%                                                                   %
% #nonintersecting_car_cdr_lemma;;                                  %
% |- nonintersecting mem free v ==>                                 %
%    is_cons(mem v) ==>                                             %
%    nonintersecting mem free(cdr_bits(mem v)) /\                   %
%    nonintersecting mem free(car_bits(mem v))                      %
%                                                                   %
% #nonintersecting_free_1_lemma;;                                   %
% |- is_cons(mem free) /\                                           %
%    (mem NIL_addr = bus32_symb_append                              %
% 	#0000000000000000000000000000) /\                           %
%    nonintersecting mem free v ==>                                 %
%    (!p. ~(free = path mem v p))                                   %
%                                                                   %
% #Store14_1_lemma;;                                                %
% |- !x. ~(free = x) ==> (!z. mem x = Store14 free z mem x)         %
%                                                                   %
% Run time: 25.2s                                                   %
% Garbage collection time: 42.3s                                    %
% Intermediate theorems generated: 2527                             %
% ================================================================= %
let Store14_path_1_lemma = 
((DISCH_ALL o GEN_ALL
	    o (DISCH "nonintersecting mem free v")
	    o GEN_ALL
	    o UNDISCH
	    o SPEC_ALL
	    o UNDISCH)
 (prove
   ("(is_cons(mem free)) /\
     (mem NIL_addr = bus32_symb_append #0000000000000000000000000000)==>
     !p v.
     (nonintersecting mem free v) ==>
     !cell1. 
      path (Store14 free cell1 mem) v p = path mem v p",
%
    let mem1 = (Store14 free cell1 mem) in
       path mem1 v p = path mem v p
%
 STRIP_TAC
 THEN INDUCT_THEN list_INDUCT
 (\th. REPEAT GEN_TAC
       THEN ASSUME_TAC (SPEC "(is_cons (mem v))
         => h => cdr_bits(mem(v:word14))
               | car_bits(mem(v:word14))
          | v" th))
 THEN rt[path]
 THEN DISCH_THEN
      (\th. GEN_TAC
            THEN IMP_RES_n_THEN 2
	     (port1 o SYM_RULE
		    o (MATCH_MP Store14_1_lemma)
		    o (porr[path])
		    o (SPEC "[]:bool list")
		    o (C MATCH_MP th))
	    nonintersecting_free_1_lemma
	    THEN ASSUME_TAC
	         (MATCH_MP nonintersecting_car_cdr_lemma th))
 THEN DISJ_CASES_THEN (\th. ANTE_RES_THEN STRIP_ASSUME_TAC
		                          (EQT_ELIM th? th)
		            THEN SUBST_ALL_TAC th)
                      (SPEC "is_cons(mem (v:word14))" BOOL_CASES_AX)
 THEN prt[COND_CLAUSES;REFL_CLAUSE]
 THEN DISJ_CASES_THEN SUBST_ALL_TAC (SPEC "h:bool" BOOL_CASES_AX)
 THEN port[COND_CLAUSES]
 THEN RULE_ASSUM_TAC (prr[COND_CLAUSES;IMP_CLAUSES])
 THEN RES_THEN MATCH_ACCEPT_TAC
 )));;
%%
% ================================================================= %
% Theorems used:                                                    %
% - nonintersecting_free_2_lemma                                    %
% - nonintersecting_free_1_lemma                                    %
% - Store14_2_lemma                                                 %
% - nonintersecting_car_cdr_lemma                                   %
%                                                                   %
% Run time: 39.0s                                                   %
% Garbage collection time: 70.9s                                    %
% Intermediate theorems generated: 4121                             %
% ================================================================= %
let Store14_path_2_lemma = 
((DISCH_ALL o GEN_ALL
	    o (DISCH "nonintersecting mem free v")
	    o GEN_ALL
	    o UNDISCH
	    o SPEC_ALL
	    o UNDISCH)
 (prove
   ("(is_cons(mem free)) /\
     (is_cons(mem(cdr_bits(mem free)))) /\
     (mem NIL_addr = bus32_symb_append #0000000000000000000000000000)==>
     !p v.
     (nonintersecting mem free v) ==>
     !cell1 cell2.
      path(Store14(cdr_bits(mem free))cell2(Store14 free cell1 mem))v p
      = path mem v p",
%
   let mem1 = Store14 free cell1 mem in
   let mem2 = Store14 (cdr_bits(mem free)) cell2 mem1 in
    path mem2 v p = path mem v p
%
 STRIP_TAC
 THEN INDUCT_THEN list_INDUCT
 (\th. REPEAT GEN_TAC
       THEN ASSUME_TAC (SPEC "(is_cons (mem v))
         => h => cdr_bits(mem(v:word14))
               | car_bits(mem(v:word14))
          | v" th))
 THEN rt[path]			% blows away base case %
 THEN STRIP_TAC			% nonintersecting ... %
 THEN REPEAT GEN_TAC		% cell1, cell2 %
 THEN IMP_RES_n_THEN 4
      (ASSUME_TAC o (rr[path]) o (SPEC "[]:bool list"))
      (hd(IMP_CANON nonintersecting_free_2_lemma))
 THEN IMP_RES_n_THEN 3
      (ASSUME_TAC o (rr[path]) o (SPEC "[]:bool list"))
      (hd(IMP_CANON nonintersecting_free_1_lemma))
 THEN IMP_RES_n_THEN 2 (port1 o SYM_RULE)
                       (hd(IMP_CANON Store14_2_lemma))
 THEN MAP_EVERY IMP_RES_TAC (IMP_CANON nonintersecting_car_cdr_lemma)
 THEN DISJ_CASES_THEN
      (\th. ANTE_RES_THEN STRIP_ASSUME_TAC (EQT_ELIM th? th)
           THEN SUBST_ALL_TAC th)
      (SPEC "is_cons(mem (v:word14))" BOOL_CASES_AX)
 THEN prt[COND_CLAUSES;REFL_CLAUSE]
 THEN DISJ_CASES_THEN SUBST_ALL_TAC (SPEC "h:bool" BOOL_CASES_AX)
 THEN port[COND_CLAUSES]
 THEN RULE_ASSUM_TAC (prr[COND_CLAUSES;IMP_CLAUSES])
 THEN RES_THEN MATCH_ACCEPT_TAC
 )));;

%%
% ================================================================= %
% Theorems used:                                                    %
% - nonintersecting_free_3_lemma                                    %
% - nonintersecting_free_2_lemma                                    %
% - nonintersecting_free_1_lemma                                    %
% - Store14_3_lemma                                                 %
% - nonintersecting_car_cdr_lemma                                   %
%                                                                   %
% Run time: 62.4s                                                   %
% Garbage collection time: 107.0s                                   %
% Intermediate theorems generated: 6843                             %
% ================================================================= %
let Store14_path_3_lemma = 
((DISCH_ALL o GEN_ALL
	    o (DISCH "nonintersecting mem free v")
	    o GEN_ALL
	    o UNDISCH
	    o SPEC_ALL
	    o UNDISCH)
 (prove
   ("(is_cons(mem free)) /\
     (is_cons(mem(cdr_bits(mem free)))) /\
     (is_cons(mem(cdr_bits(mem(cdr_bits(mem free)))))) /\
     (~(free = cdr_bits(mem free))) /\
     (mem NIL_addr = bus32_symb_append #0000000000000000000000000000)==>
     !p v.
     (nonintersecting mem free v) ==>
     !cell1 cell2 cell3.
      path
      (Store14
       (cdr_bits(Store14 free cell1 mem(cdr_bits(mem free))))
       cell3
       (Store14(cdr_bits(mem free))cell2(Store14 free cell1 mem)))
      v 
      p =
      path mem v p",
%
  !cell1 cell2 cell3.
   let mem1 = Store14 free cell1 mem in
   let mem2 = Store14 (cdr_bits(mem free)) cell2 mem1 in
   let mem3 =
       Store14 (cdr_bits(mem1(cdr_bits(mem free)))) cell3 mem2 in
    path mem3 v p = path mem v p
%
 STRIP_TAC
 THEN INDUCT_THEN list_INDUCT
 (\th. REPEAT GEN_TAC
       THEN ASSUME_TAC (SPEC "(is_cons (mem v))
         => h => cdr_bits(mem(v:word14))
               | car_bits(mem(v:word14))
          | v" th))
 THEN rt[path]			% blows away base case %
 THEN STRIP_TAC			% nonintersecting ... %
 THEN REPEAT GEN_TAC		% cell1, cell2 %
 THEN IMP_RES_n_THEN 5
      (ASSUME_TAC o (rr[path]) o (SPEC "[]:bool list"))
      (hd(IMP_CANON nonintersecting_free_3_lemma))
 THEN IMP_RES_n_THEN 4
      (ASSUME_TAC o (rr[path]) o (SPEC "[]:bool list"))
      (hd(IMP_CANON nonintersecting_free_2_lemma))
 THEN IMP_RES_n_THEN 3
      (ASSUME_TAC o (rr[path]) o (SPEC "[]:bool list"))
      (hd(IMP_CANON nonintersecting_free_1_lemma))
 THEN IMP_RES_n_THEN 4
      (port1 o SYM_RULE)
      (hd(IMP_CANON Store14_3_lemma))
 THEN MAP_EVERY IMP_RES_TAC (IMP_CANON nonintersecting_car_cdr_lemma)
 THEN DISJ_CASES_THEN
      (\th. ANTE_RES_THEN STRIP_ASSUME_TAC (EQT_ELIM th? th)
           THEN SUBST_ALL_TAC th)
      (SPEC "is_cons(mem (v:word14))" BOOL_CASES_AX)
 THEN prt[COND_CLAUSES;REFL_CLAUSE]
 THEN DISJ_CASES_THEN SUBST_ALL_TAC (SPEC "h:bool" BOOL_CASES_AX)
 THEN port[COND_CLAUSES]
 THEN RULE_ASSUM_TAC (prr[COND_CLAUSES;IMP_CLAUSES])
 THEN RES_THEN MATCH_ACCEPT_TAC
 )));;

%%
% ================================================================= %
% Theorems used:                                                    %
% - nonintersecting_free_4_lemma                                    %
% - nonintersecting_free_3_lemma                                    %
% - nonintersecting_free_2_lemma                                    %
% - nonintersecting_free_1_lemma                                    %
% - Store14_4_lemma                                                 %
% - nonintersecting_car_cdr_lemma                                   %
%                                                                   %
% It would be useful to move the "!p." inwards, within the          %
% nonintersecting precondition.  This could be placed on the        %
% assumption list, and "p" specialized as needed, to save repeated  %
% resolution to obtain the same intermediate results.               %
%                                                                   %
% Run time: 129.9s                                                  %
% Garbage collection time: 224.2s                                   %
% Intermediate theorems generated: 15208                            %
% ================================================================= %
let Store14_path_4_lemma = 
((DISCH_ALL o GEN_ALL
	    o (DISCH "nonintersecting mem free v")
	    o GEN_ALL
	    o UNDISCH
	    o SPEC_ALL
	    o UNDISCH)
 (prove
   ("(is_cons(mem free)) /\
     (is_cons(mem(cdr_bits(mem free)))) /\
     (is_cons(mem(cdr_bits(mem(cdr_bits(mem free)))))) /\
     (is_cons(mem(cdr_bits(mem(cdr_bits(mem(cdr_bits(mem free)))))))) /\
     (~(free = cdr_bits(mem free))) /\
     (~(free = cdr_bits(mem(cdr_bits(mem free))))) /\
     (~(cdr_bits(mem free) = cdr_bits(mem(cdr_bits(mem free))))) /\
     (mem NIL_addr = bus32_symb_append #0000000000000000000000000000)==>
     !p v.
     (nonintersecting mem free v) ==>
     !cell1 cell2 cell3.
      path
      (Store14
       (cdr_bits
        (Store14
         (cdr_bits(mem free))
         cell2
         (Store14 free cell1 mem)
         (cdr_bits(Store14 free cell1 mem(cdr_bits(mem free))))))
       cell4
       (Store14
        (cdr_bits(Store14 free cell1 mem(cdr_bits(mem free))))
        cell3
        (Store14(cdr_bits(mem free))cell2(Store14 free cell1 mem))))
      v 
      p =
      path mem v p",
%
   let mem1 = Store14 free cell1 mem in
   let mem2 = Store14 (cdr_bits(mem free)) cell2 mem1 in
   let mem3 =
           Store14 (cdr_bits(mem1(cdr_bits(mem free)))) cell3 mem2 in
   let mem4 =
           Store14 (cdr_bits(mem2(cdr_bits(mem1(cdr_bits(mem free))))))
                   cell4 mem3 in
    path mem4 v p = path mem v p
%
 STRIP_TAC
 THEN INDUCT_THEN list_INDUCT
 (\th. REPEAT GEN_TAC
       THEN ASSUME_TAC (SPEC "(is_cons (mem v))
         => h => cdr_bits(mem(v:word14))
               | car_bits(mem(v:word14))
          | v" th))
 THEN rt[path]			% blows away base case %
 THEN STRIP_TAC			% nonintersecting ... %
 THEN REPEAT GEN_TAC		% cell1, cell2 %
 THEN IMP_RES_n_THEN 6
      (ASSUME_TAC o (rr[path]) o (SPEC "[]:bool list"))
      (hd(IMP_CANON nonintersecting_free_4_lemma))
 THEN IMP_RES_n_THEN 5
      (ASSUME_TAC o (rr[path]) o (SPEC "[]:bool list"))
      (hd(IMP_CANON nonintersecting_free_3_lemma))
 THEN IMP_RES_n_THEN 4
      (ASSUME_TAC o (rr[path]) o (SPEC "[]:bool list"))
      (hd(IMP_CANON nonintersecting_free_2_lemma))
 THEN IMP_RES_n_THEN 3
      (ASSUME_TAC o (rr[path]) o (SPEC "[]:bool list"))
      (hd(IMP_CANON nonintersecting_free_1_lemma))
 THEN IMP_RES_n_THEN 7
      (port1 o SYM_RULE)
      (hd(IMP_CANON Store14_4_lemma))
 THEN MAP_EVERY IMP_RES_TAC (IMP_CANON nonintersecting_car_cdr_lemma)
 THEN DISJ_CASES_THEN
      (\th. ANTE_RES_THEN STRIP_ASSUME_TAC (EQT_ELIM th? th)
           THEN SUBST_ALL_TAC th)
      (SPEC "is_cons(mem (v:word14))" BOOL_CASES_AX)
 THEN prt[COND_CLAUSES;REFL_CLAUSE]
 THEN DISJ_CASES_THEN SUBST_ALL_TAC (SPEC "h:bool" BOOL_CASES_AX)
 THEN port[COND_CLAUSES]
 THEN RULE_ASSUM_TAC (prr[COND_CLAUSES;IMP_CLAUSES])
 THEN RES_THEN MATCH_ACCEPT_TAC
 )));;

% ================================================================= %
% If free list is nonempty,                                         %
% and NIL reserved word is in place,                                %
% then if free list and v are nonintersecting,                      %
%      then the new memory at any location referenced by a path in  %
%           the NEW memory is the same as the old memory location   %
%           at the path through the old memory.                     %
% NOT required outside this theory file.                            %
% ================================================================= %
let Store14_newpath_1_lemma = prove
("(is_cons(mem free)) /\
  (mem NIL_addr = bus32_symb_append #0000000000000000000000000000)==>
  !v.
  (nonintersecting mem free v) ==>
   (!p cell1.
     Store14 free cell1 mem(path(Store14 free cell1 mem)v p) =
     mem(path mem v p))",
%
   let mem1 = (Store14 free cell1 mem) in
    mem1(path mem1 v p) = mem (path mem v p) 
%
 REPEAT STRIP_TAC
 THEN IMP_RES_n_THEN 3 port1            (hd(IMP_CANON Store14_path_1_lemma))
 THEN IMP_RES_n_THEN 3 MATCH_ACCEPT_TAC (hd(IMP_CANON Store14_oldpath_1_lemma))
 );;


let Store14_newpath_2_lemma = prove
("(is_cons(mem free)) /\
  (is_cons(mem(cdr_bits(mem free)))) /\
  (mem NIL_addr = bus32_symb_append #0000000000000000000000000000)==>
  !v.
  (nonintersecting mem free v) ==>
   (!p cell1 cell2.
     Store14
     (cdr_bits(mem free))
     cell2
     (Store14 free cell1 mem)
     (path(Store14(cdr_bits(mem free))cell2(Store14 free cell1 mem))v p) =
     mem(path mem v p))",
%
   let mem1 = Store14 free cell1 mem in
   let mem2 = Store14 (cdr_bits(mem free)) cell2 mem1 in
    mem2(path mem2 v p) = mem(path mem v p)"
%
 REPEAT STRIP_TAC
 THEN IMP_RES_n_THEN 4 port1            (hd(IMP_CANON Store14_path_2_lemma))
 THEN IMP_RES_n_THEN 4 MATCH_ACCEPT_TAC (hd(IMP_CANON Store14_oldpath_2_lemma))
 );;


let Store14_newpath_3_lemma = prove
("(is_cons(mem free)) /\
  (is_cons(mem(cdr_bits(mem free)))) /\
  (is_cons(mem(cdr_bits(mem(cdr_bits(mem free)))))) /\
  (~(free = cdr_bits(mem free))) /\
  (mem NIL_addr = bus32_symb_append #0000000000000000000000000000)==>
  !v.
  (nonintersecting mem free v) ==>
   (!p cell1 cell2 cell3.
     Store14
     (cdr_bits(Store14 free cell1 mem(cdr_bits(mem free))))
     cell3
     (Store14(cdr_bits(mem free))cell2(Store14 free cell1 mem))
     (path
      (Store14
       (cdr_bits(Store14 free cell1 mem(cdr_bits(mem free))))
       cell3
       (Store14(cdr_bits(mem free))cell2(Store14 free cell1 mem)))
      v 
      p) =
     mem(path mem v p))",
%
   let mem1 = Store14 free cell1 mem in
   let mem2 = Store14 (cdr_bits(mem free)) cell2 mem1 in
   let mem3 =
       Store14 (cdr_bits(mem1(cdr_bits(mem free)))) cell3 mem2 in
    mem3(path mem3 v p) = mem(path mem v p)
%
 REPEAT STRIP_TAC
 THEN IMP_RES_n_THEN 6 port1            (hd(IMP_CANON Store14_path_3_lemma))
 THEN IMP_RES_n_THEN 6 MATCH_ACCEPT_TAC (hd(IMP_CANON Store14_oldpath_3_lemma))
 );;

let Store14_newpath_4_lemma = prove
("(is_cons(mem free)) /\
  (is_cons(mem(cdr_bits(mem free)))) /\
  (is_cons(mem(cdr_bits(mem(cdr_bits(mem free)))))) /\
  (is_cons(mem(cdr_bits(mem(cdr_bits(mem(cdr_bits(mem free)))))))) /\
  (~(free = cdr_bits(mem free))) /\
  (~(free = cdr_bits(mem(cdr_bits(mem free))))) /\
  (~(cdr_bits(mem free) = cdr_bits(mem(cdr_bits(mem free))))) /\
  (mem NIL_addr = bus32_symb_append #0000000000000000000000000000)==>
  !v.
  (nonintersecting mem free v) ==>
   (!p cell1 cell2 cell3 cell4.
     Store14
     (cdr_bits
      (Store14
       (cdr_bits(mem free))
       cell2
       (Store14 free cell1 mem)
       (cdr_bits(Store14 free cell1 mem(cdr_bits(mem free))))))
     cell4
     (Store14
      (cdr_bits(Store14 free cell1 mem(cdr_bits(mem free))))
      cell3
      (Store14(cdr_bits(mem free))cell2(Store14 free cell1 mem)))
     (path
      (Store14
       (cdr_bits
        (Store14
         (cdr_bits(mem free))
         cell2
         (Store14 free cell1 mem)
         (cdr_bits(Store14 free cell1 mem(cdr_bits(mem free))))))
       cell4
       (Store14
        (cdr_bits(Store14 free cell1 mem(cdr_bits(mem free))))
        cell3
        (Store14(cdr_bits(mem free))cell2(Store14 free cell1 mem))))
      v 
      p) =
     mem(path mem v p))",
%
   let mem1 = Store14 free cell1 mem in
   let mem2 = Store14 (cdr_bits(mem free)) cell2 mem1 in
   let mem3 =
           Store14 (cdr_bits(mem1(cdr_bits(mem free)))) cell3 mem2 in
   let mem4 =
           Store14 (cdr_bits(mem2(cdr_bits(mem1(cdr_bits(mem free))))))
                   cell4 mem3 in
    mem4(path mem4 v p) = mem(path mem v p)
%
 REPEAT STRIP_TAC
 THEN IMP_RES_n_THEN 9 port1            (hd(IMP_CANON Store14_path_4_lemma))
 THEN IMP_RES_n_THEN 9 MATCH_ACCEPT_TAC (hd(IMP_CANON Store14_oldpath_4_lemma))
 );;

%%
% ================================================================= %
% Special purpose theorem for later proofs.                         %
% ================================================================= %
let AP_is_cons_lemma = prove
("is_cons x ==> (y = x) ==> is_cons y",
 REPEAT STRIP_TAC THEN art[]);;

% ================================================================= %
% If the free list is nonempty and linear                           %
% and NIL reserved word is in place                                 %
% then 1-4 memory updates do not alter the memory at a              %
%      nonintersecting cell                                         %
%                                                                   %
% Proof Strategy:                                                   %
% - strip off all assumptions                                       %
% - eliminate the let bindings                                      %
% - resolve with Store14_newpath_*_lemma:                           %
%   th = !p cell ... . mem*(path mem* v p) = mem(path mem v p)      %
% - Specializing to the null path, and applying "is_cons", derive:  %
%   is_cons(mem v) ==> is_cons(mem* v)                              %
% - resolve with the assumption "is_cons(mem v)" to get:            %
%   th1 = is_cons(mem* v)                                           %
% - Specialize th to paths "[F]" and "[T]" (car and cdr), and       %
%   rewrite with path, and th1, to get:                             %
%   th2 = !cell ... . (mem*(car_bits(mem* v)) =                     %
% 		     mem(is_cons(mem v)=>car_bits(mem v)|v))        %
%   th3 = !cell ... . (mem*(cdr_bits(mem* v)) =                     %
%                      mem(is_cons(mem v)=>cdr_bits(mem v)|v))      %
% - rewrite with th2, th3, and the assumption:                      %
%   is_cons(mem v)                                                  %
% ================================================================= %
let Store14_root_1_lemma = TAC_PROOF
(([],
 "is_cons(mem free) /\
  (mem NIL_addr = bus32_symb_append #0000000000000000000000000000) ==>
  (!v.
   nonintersecting mem free v ==>
   (!cell1.
   let mem1 = Store14 free cell1 mem in
       (mem1 v = mem v)))"),
 REPEAT STRIP_TAC
 THEN prt[LET_THM] THEN BETA_TAC
 THEN IMP_RES_n_THEN 3
      (MATCH_ACCEPT_TAC o (rr[path]) o (SPECL ["cell1:word32"; "[]:bool list"]))
      (hd(IMP_CANON Store14_newpath_1_lemma))
      );;

let Store14_root_2_lemma = TAC_PROOF
(([],
 "is_cons(mem free) /\
  is_cons(mem(cdr_bits(mem free))) /\
  (mem NIL_addr = bus32_symb_append #0000000000000000000000000000) ==>
  (!v.
   nonintersecting mem free v ==>
   (!cell1 cell2.
   let mem1 = Store14 free cell1 mem in
   let mem2 = Store14 (cdr_bits(mem free)) cell2 mem1 in
       (mem2 v = mem v)))"),
 REPEAT STRIP_TAC
 THEN prt[LET_THM] THEN BETA_TAC
 THEN IMP_RES_n_THEN 4
      (MATCH_ACCEPT_TAC o (rr[path])
			o (SPECL ["cell2:word32"; "cell1:word32";"[]:bool list"]))
      (hd(IMP_CANON Store14_newpath_2_lemma))
      );;

let Store14_root_3_lemma = TAC_PROOF
(([],
 "is_cons(mem free) /\
  is_cons(mem(cdr_bits(mem free))) /\
  is_cons(mem(cdr_bits(mem(cdr_bits(mem free))))) /\
  ~(free = cdr_bits(mem free)) /\
  (mem NIL_addr = bus32_symb_append #0000000000000000000000000000) ==>
  (!v.
   nonintersecting mem free v ==>
   (!cell1 cell2 cell3.
   let mem1 = Store14 free cell1 mem in
   let mem2 = Store14 (cdr_bits(mem free)) cell2 mem1 in
   let mem3 =
           Store14 (cdr_bits(mem1(cdr_bits(mem free)))) cell3 mem2 in
       (mem3 v = mem v)))"),
 REPEAT STRIP_TAC
 THEN prt[LET_THM] THEN BETA_TAC
 THEN IMP_RES_n_THEN 6
      (MATCH_ACCEPT_TAC o (rr[path])
			o (SPECL ["cell1:word32"; "cell3:word32"
				 ; "cell2:word32";"[]:bool list"]))
      (hd(IMP_CANON Store14_newpath_3_lemma))
      );;

let Store14_root_4_lemma = TAC_PROOF
(([],
 "is_cons(mem free) /\
  is_cons(mem(cdr_bits(mem free))) /\
  is_cons(mem(cdr_bits(mem(cdr_bits(mem free))))) /\
  is_cons(mem(cdr_bits(mem(cdr_bits(mem(cdr_bits(mem free))))))) /\
  ~(free = cdr_bits(mem free)) /\
  ~(free = cdr_bits(mem(cdr_bits(mem free)))) /\
  ~(cdr_bits(mem free) = cdr_bits(mem(cdr_bits(mem free)))) /\
  (mem NIL_addr = bus32_symb_append #0000000000000000000000000000) ==>
  (!v.
   nonintersecting mem free v ==>
   (!cell1 cell2 cell3 cell4.
   let mem1 = Store14 free cell1 mem in
   let mem2 = Store14 (cdr_bits(mem free)) cell2 mem1 in
   let mem3 =
           Store14 (cdr_bits(mem1(cdr_bits(mem free)))) cell3 mem2 in
   let mem4 =
           Store14 (cdr_bits(mem2(cdr_bits(mem1(cdr_bits(mem free))))))
                   cell4 mem3 in
        (mem4 v = mem v)))"),
 REPEAT STRIP_TAC
 THEN prt[LET_THM] THEN BETA_TAC
 THEN IMP_RES_n_THEN 9
      (MATCH_ACCEPT_TAC o (rr[path])
			o (SPECL ["cell2:word32"; "cell1:word32"; "cell4:word32"
				 ; "cell3:word32";"[]:bool list"]))
      (hd(IMP_CANON Store14_newpath_4_lemma))
      );;

% ================================================================= %
% If the free list is nonempty and linear                           %
% and NIL reserved word is in place                                 %
% then if a nonintersecting cell is a cons cell,                    %
%      then 1-4 memory updates do not alter the memory at           %
%           its car and cdr addresses                               %
%                                                                   %
% Proof Strategy:                                                   %
% - strip off all assumptions                                       %
% - eliminate the let bindings                                      %
% - resolve with Store14_newpath_*_lemma:                           %
%   th = !p cell ... . mem*(path mem* v p) = mem(path mem v p)      %
% - Specializing to the null path, and applying "is_cons", derive:  %
%   is_cons(mem v) ==> is_cons(mem* v)                              %
% - resolve with the assumption "is_cons(mem v)" to get:            %
%   th1 = is_cons(mem* v)                                           %
% - Specialize th to paths "[F]" and "[T]" (car and cdr), and       %
%   rewrite with path, and th1, to get:                             %
%   th2 = !cell ... . (mem*(car_bits(mem* v)) =                     %
% 		     mem(is_cons(mem v)=>car_bits(mem v)|v))        %
%   th3 = !cell ... . (mem*(cdr_bits(mem* v)) =                     %
%                      mem(is_cons(mem v)=>cdr_bits(mem v)|v))      %
% - rewrite with th2, th3, and the assumption:                      %
%   is_cons(mem v)                                                  %
% ================================================================= %
let Store14_car_cdr_1_lemma = TAC_PROOF
(([],
 "is_cons(mem free) /\
  (mem NIL_addr = bus32_symb_append #0000000000000000000000000000) ==>
  (!v.
   is_cons(mem v) /\
   nonintersecting mem free v ==>
   (!cell1.
   let mem1 = Store14 free cell1 mem in
   ((mem1(cdr_bits(mem1 v)) = mem(cdr_bits(mem v))) /\
    (mem1(car_bits(mem1 v)) = mem(car_bits(mem  v))))))"),
 REPEAT STRIP_TAC
 THEN prt[LET_THM] THEN BETA_TAC
 THEN IMP_RES_n_THEN 3
      ((\th. IMP_RES_THEN
            ((\th1. 
		let th2 = ((rr[th1;path]) o (SPEC "[F]")) th
		in
		let th3 = ((rr[th1;path]) o (SPEC "[T]")) th
		in
		art[th2;th3]
		) o GEN_ALL)
	      ((snd o EQ_IMP_RULE
		    o (AP_TERM "is_cons")
		    o SPEC_ALL
		    o (rr[path])
		    o (SPEC "[]:bool list")) th))
       o (SPEC "cell1:word32"))
      (hd(IMP_CANON Store14_newpath_1_lemma))
      );;

let Store14_car_cdr_2_lemma = TAC_PROOF
(([],
 "is_cons(mem free) /\
  is_cons(mem(cdr_bits(mem free))) /\
  (mem NIL_addr = bus32_symb_append #0000000000000000000000000000) ==>
  (!v.
   is_cons(mem v) /\
   nonintersecting mem free v ==>
   (!cell1 cell2.
   let mem1 = Store14 free cell1 mem in
   let mem2 = Store14 (cdr_bits(mem free)) cell2 mem1 in
       ((mem2(cdr_bits(mem2 v)) = mem(cdr_bits(mem  v))) /\
        (mem2(car_bits(mem2 v)) = mem(car_bits(mem  v))))))"),
 REPEAT STRIP_TAC
 THEN prt[LET_THM] THEN BETA_TAC
 THEN IMP_RES_n_THEN 4
      ((\th. IMP_RES_THEN
            ((\th1. 
		 let th2 = ((rr[th1;path]) o (SPEC "[F]")) th
		 in
		 let th3 = ((rr[th1;path]) o (SPEC "[T]")) th
		 in
		 art[th2;th3]
		 ) o GEN_ALL)
	       ((snd o EQ_IMP_RULE
		     o (AP_TERM "is_cons")
		     o SPEC_ALL
		     o (rr[path])
		     o (SPEC "[]:bool list")) th))
       o (SPECL ["cell2:word32"; "cell1:word32"]))
      (hd(IMP_CANON Store14_newpath_2_lemma))
      );;

let Store14_car_cdr_3_lemma = TAC_PROOF
(([],
 "is_cons(mem free) /\
  is_cons(mem(cdr_bits(mem free))) /\
  is_cons(mem(cdr_bits(mem(cdr_bits(mem free))))) /\
  ~(free = cdr_bits(mem free)) /\
  (mem NIL_addr = bus32_symb_append #0000000000000000000000000000) ==>
  (!v.
   is_cons(mem v) /\
   nonintersecting mem free v ==>
   (!cell1 cell2 cell3.
   let mem1 = Store14 free cell1 mem in
   let mem2 = Store14 (cdr_bits(mem free)) cell2 mem1 in
   let mem3 =
           Store14 (cdr_bits(mem1(cdr_bits(mem free)))) cell3 mem2 in
       ((mem3(cdr_bits(mem3 v)) = mem(cdr_bits(mem  v))) /\
        (mem3(car_bits(mem3 v)) = mem(car_bits(mem  v))))))"),
 REPEAT STRIP_TAC
 THEN prt[LET_THM] THEN BETA_TAC
 THEN IMP_RES_n_THEN 6
      ((\th. IMP_RES_THEN
	    ((\th1. 
	      let th2 = ((rr[th1;path]) o (SPEC "[F]")) th
	      in
	      let th3 = ((rr[th1;path]) o (SPEC "[T]")) th
	      in
	      art[th2;th3]
	      ) o GEN_ALL)
	      ((snd o EQ_IMP_RULE
		    o (AP_TERM "is_cons")
		    o SPEC_ALL
		    o (rr[path])
		    o (SPEC "[]:bool list")) th))
       o (SPECL ["cell3:word32"; "cell2:word32"; "cell1:word32"]))
       (hd(IMP_CANON Store14_newpath_3_lemma))
	  );;

let Store14_car_cdr_4_lemma = TAC_PROOF
(([],
 "is_cons(mem free) /\
  is_cons(mem(cdr_bits(mem free))) /\
  is_cons(mem(cdr_bits(mem(cdr_bits(mem free))))) /\
  is_cons(mem(cdr_bits(mem(cdr_bits(mem(cdr_bits(mem free))))))) /\
  ~(free = cdr_bits(mem free)) /\
  ~(free = cdr_bits(mem(cdr_bits(mem free)))) /\
  ~(cdr_bits(mem free) = cdr_bits(mem(cdr_bits(mem free)))) /\
  (mem NIL_addr = bus32_symb_append #0000000000000000000000000000) ==>
  (!v.
   is_cons(mem v) /\
   nonintersecting mem free v ==>
   (!cell1 cell2 cell3 cell4.
   let mem1 = Store14 free cell1 mem in
   let mem2 = Store14 (cdr_bits(mem free)) cell2 mem1 in
   let mem3 =
           Store14 (cdr_bits(mem1(cdr_bits(mem free)))) cell3 mem2 in
   let mem4 =
           Store14 (cdr_bits(mem2(cdr_bits(mem1(cdr_bits(mem free))))))
                   cell4 mem3 in
       ((mem4(cdr_bits(mem4 v)) = mem(cdr_bits(mem  v))) /\
        (mem4(car_bits(mem4 v)) = mem(car_bits(mem  v))))))"),
 REPEAT STRIP_TAC
 THEN prt[LET_THM] THEN BETA_TAC
 THEN IMP_RES_n_THEN 9
      ((\th. IMP_RES_THEN
            ((\th1. 
		 let th2 = ((rr[th1;path]) o (SPEC "[F]")) th
	         in
		 let th3 = ((rr[th1;path]) o (SPEC "[T]")) th
	         in
		 art[th2;th3]
		 ) o GEN_ALL)
		 ((snd o EQ_IMP_RULE
		       o (AP_TERM "is_cons")
		       o SPEC_ALL
		       o (rr[path])
		       o (SPEC "[]:bool list")) th))
	o (SPECL ["cell2:word32"; "cell1:word32"; "cell4:word32"; "cell3:word32"]))
       (hd(IMP_CANON Store14_newpath_4_lemma))
	  );;

% ================================================================= %

% ================================================================= %
let Store14_cadr_cddr_1_lemma = TAC_PROOF
(([],
 "is_cons(mem free) /\
  (mem NIL_addr = bus32_symb_append #0000000000000000000000000000) ==>
  (!v.
   is_cons(mem v) /\
   is_cons(mem(cdr_bits(mem v))) /\
   nonintersecting mem free v ==>
   (!cell1.
   let mem1 = Store14 free cell1 mem in
       ((mem1(cdr_bits(mem1(cdr_bits(mem1 v)))) =
         mem (cdr_bits(mem (cdr_bits(mem  v))))) /\
        (mem1(car_bits(mem1(cdr_bits(mem1 v)))) =
         mem (car_bits(mem (cdr_bits(mem  v))))))))"),
 REPEAT STRIP_TAC
 THEN prt[LET_THM] THEN BETA_TAC
 THEN (ASSUME_TAC
       o (in_conv_rule BETA_CONV)
       o (rr[LET_THM])
       o UNDISCH_ALL
       o hd
       o IMP_CANON)
      Store14_root_1_lemma
 THEN (MAP_EVERY
       (ASSUME_TAC o UNDISCH_ALL)
       o IMP_CANON
       o (in_conv_rule BETA_CONV)
       o (rr[LET_THM]))
      Store14_car_cdr_1_lemma
 THEN IMP_RES_n_THEN 2 ASSUME_TAC AP_is_cons_lemma
 THEN poart[]
 THEN IMP_RES_n_THEN 3
	((\th. ASSUM_LIST
	 (\thl. (port1 o (rr (path.thl)) o (SPEC "[T;T]")) th
	   THEN (port1 o (rr (path.thl)) o (SPEC "[T;F]")) th))
	 o (SPEC "cell1:word32"))
       (hd(IMP_CANON Store14_oldpath_1_lemma))
 THEN rt[]);;

let Store14_cadr_cddr_2_lemma = TAC_PROOF
(([],
 "is_cons(mem free) /\
  is_cons(mem(cdr_bits(mem free))) /\
  (mem NIL_addr = bus32_symb_append #0000000000000000000000000000) ==>
  (!v.
   is_cons(mem v) /\
   is_cons(mem(cdr_bits(mem v))) /\
   nonintersecting mem free v ==>
   (!cell1 cell2.
   let mem1 = Store14 free cell1 mem in
   let mem2 = Store14 (cdr_bits(mem free)) cell2 mem1 in
       ((mem2(cdr_bits(mem2(cdr_bits(mem2 v)))) =
         mem (cdr_bits(mem (cdr_bits(mem  v))))) /\
        (mem2(car_bits(mem2(cdr_bits(mem2 v)))) =
         mem (car_bits(mem (cdr_bits(mem  v))))))))"),
 REPEAT STRIP_TAC
 THEN prt[LET_THM] THEN BETA_TAC
 THEN (ASSUME_TAC
       o (in_conv_rule BETA_CONV)
       o (rr[LET_THM])
       o UNDISCH_ALL
       o hd
       o IMP_CANON)
      Store14_root_2_lemma
 THEN (MAP_EVERY
       (ASSUME_TAC o UNDISCH_ALL)
       o IMP_CANON
       o (in_conv_rule BETA_CONV)
       o (rr[LET_THM]))
      Store14_car_cdr_2_lemma
 THEN IMP_RES_n_THEN 2 ASSUME_TAC AP_is_cons_lemma
 THEN poart[]
 THEN IMP_RES_n_THEN 4
      ((\th. ASSUM_LIST
	  (\thl. (port1 o (rr (path.thl)) o (SPEC "[T;T]")) th
	    THEN (port1 o (rr (path.thl)) o (SPEC "[T;F]")) th))
       o (SPECL ["cell2:word32"; "cell1:word32"]))
      (hd(IMP_CANON Store14_oldpath_2_lemma))
 THEN rt[]);;

let Store14_cadr_cddr_3_lemma = TAC_PROOF
(([],
 "is_cons(mem free) /\
  is_cons(mem(cdr_bits(mem free))) /\
  is_cons(mem(cdr_bits(mem(cdr_bits(mem free))))) /\
  ~(free = cdr_bits(mem free)) /\
  (mem NIL_addr = bus32_symb_append #0000000000000000000000000000) ==>
  (!v.
   is_cons(mem v) /\
   is_cons(mem(cdr_bits(mem v))) /\
   nonintersecting mem free v ==>
   (!cell1 cell2 cell3.
   let mem1 = Store14 free cell1 mem in
   let mem2 = Store14 (cdr_bits(mem free)) cell2 mem1 in
   let mem3 =
           Store14 (cdr_bits(mem1(cdr_bits(mem free)))) cell3 mem2 in
       ((mem3(cdr_bits(mem3(cdr_bits(mem3 v)))) =
         mem (cdr_bits(mem (cdr_bits(mem  v))))) /\
        (mem3(car_bits(mem3(cdr_bits(mem3 v)))) =
         mem (car_bits(mem (cdr_bits(mem  v))))))))"),
 REPEAT STRIP_TAC
 THEN prt[LET_THM] THEN BETA_TAC
 THEN (ASSUME_TAC
       o (in_conv_rule BETA_CONV)
       o (rr[LET_THM])
       o UNDISCH_ALL
       o hd
       o IMP_CANON)
      Store14_root_3_lemma
 THEN (MAP_EVERY
       (ASSUME_TAC o UNDISCH_ALL)
       o IMP_CANON
       o (in_conv_rule BETA_CONV)
       o (rr[LET_THM]))
      Store14_car_cdr_3_lemma
 THEN IMP_RES_n_THEN 2 ASSUME_TAC AP_is_cons_lemma
 THEN poart[]
 THEN IMP_RES_n_THEN 6
      ((\th. ASSUM_LIST
	     (\thl. (port1 o (rr (path.thl)) o (SPEC "[T;T]")) th
	      THEN (port1 o (rr (path.thl)) o (SPEC "[T;F]")) th))
       o (SPECL ["cell1:word32";"cell2:word32";"cell3:word32"]))
      (hd(IMP_CANON Store14_oldpath_3_lemma))
 THEN rt[]
  );;

let Store14_cadr_cddr_4_lemma = TAC_PROOF
(([],
 "is_cons(mem free) /\
  is_cons(mem(cdr_bits(mem free))) /\
  is_cons(mem(cdr_bits(mem(cdr_bits(mem free))))) /\
  is_cons(mem(cdr_bits(mem(cdr_bits(mem(cdr_bits(mem free))))))) /\
  ~(free = cdr_bits(mem free)) /\
  ~(free = cdr_bits(mem(cdr_bits(mem free)))) /\
  ~(cdr_bits(mem free) = cdr_bits(mem(cdr_bits(mem free)))) /\
  (mem NIL_addr = bus32_symb_append #0000000000000000000000000000) ==>
  (!v.
   is_cons(mem v) /\
   is_cons(mem(cdr_bits(mem v))) /\
   nonintersecting mem free v ==>
   (!cell1 cell2 cell3 cell4.
   let mem1 = Store14 free cell1 mem in
   let mem2 = Store14 (cdr_bits(mem free)) cell2 mem1 in
   let mem3 =
           Store14 (cdr_bits(mem1(cdr_bits(mem free)))) cell3 mem2 in
   let mem4 =
           Store14 (cdr_bits(mem2(cdr_bits(mem1(cdr_bits(mem free))))))
                   cell4 mem3 in
       ((mem4(cdr_bits(mem4(cdr_bits(mem4 v)))) =
         mem (cdr_bits(mem (cdr_bits(mem  v))))) /\
        (mem4(car_bits(mem4(cdr_bits(mem4 v)))) =
         mem (car_bits(mem (cdr_bits(mem  v))))))))"),
 REPEAT STRIP_TAC
 THEN prt[LET_THM] THEN BETA_TAC
 THEN (ASSUME_TAC
       o (in_conv_rule BETA_CONV)
       o (rr[LET_THM])
       o UNDISCH_ALL
       o hd
       o IMP_CANON)
      Store14_root_4_lemma
 THEN (MAP_EVERY
       (ASSUME_TAC o UNDISCH_ALL)
       o IMP_CANON
       o (in_conv_rule BETA_CONV)
       o (rr[LET_THM]))
      Store14_car_cdr_4_lemma
 THEN IMP_RES_n_THEN 2 ASSUME_TAC AP_is_cons_lemma
 THEN poart[]
 THEN IMP_RES_n_THEN 9
      ((\th. ASSUM_LIST
            (\thl. (port1 o (rr (path.thl)) o (SPEC "[T;T]")) th
	      THEN (port1 o (rr (path.thl)) o (SPEC "[T;F]")) th))
       o (SPECL ["cell1:word32";"cell2:word32";"cell3:word32";"cell4:word32"]))
      (hd(IMP_CANON Store14_oldpath_4_lemma))
 THEN rt[]
  );;

% ================================================================= %

% ================================================================= %
let Store14_caar_cdar_1_lemma = TAC_PROOF
(([],
 "is_cons(mem free) /\
  (mem NIL_addr = bus32_symb_append #0000000000000000000000000000) ==>
  (!v.
   is_cons(mem v) /\
   is_cons(mem(car_bits(mem v))) /\
   nonintersecting mem free v ==>
   (!cell1.
   let mem1 = Store14 free cell1 mem in
       ((mem1(cdr_bits(mem1(car_bits(mem1 v)))) =
         mem (cdr_bits(mem (car_bits(mem  v))))) /\
        (mem1(car_bits(mem1(car_bits(mem1 v)))) =
         mem (car_bits(mem (car_bits(mem  v))))))))"),
 REPEAT STRIP_TAC
 THEN prt[LET_THM] THEN BETA_TAC
 THEN (ASSUME_TAC
       o (in_conv_rule BETA_CONV)
       o (rr[LET_THM])
       o UNDISCH_ALL
       o hd
       o IMP_CANON)
      Store14_root_1_lemma
 THEN (MAP_EVERY
       (ASSUME_TAC o UNDISCH_ALL)
       o IMP_CANON
       o (in_conv_rule BETA_CONV)
       o (rr[LET_THM]))
      Store14_car_cdr_1_lemma
 THEN IMP_RES_THEN IMP_RES_TAC AP_is_cons_lemma
 THEN poart[]
 THEN IMP_RES_n_THEN 3
      ((\th. ASSUM_LIST
	 (\thl. (port1 o (rr (path.thl)) o (SPEC "[F;T]")) th
	   THEN (port1 o (rr (path.thl)) o (SPEC "[F;F]")) th))
       o (SPEC "cell1:word32"))
      (hd(IMP_CANON Store14_oldpath_1_lemma))
 THEN rt[]);;

let Store14_caar_cdar_2_lemma = TAC_PROOF
(([],
 "is_cons(mem free) /\
  is_cons(mem(cdr_bits(mem free))) /\
  (mem NIL_addr = bus32_symb_append #0000000000000000000000000000) ==>
  (!v.
   is_cons(mem v) /\
   is_cons(mem(car_bits(mem v))) /\
   nonintersecting mem free v ==>
   (!cell1 cell2.
   let mem1 = Store14 free cell1 mem in
   let mem2 = Store14 (cdr_bits(mem free)) cell2 mem1 in
       ((mem2(cdr_bits(mem2(car_bits(mem2 v)))) =
         mem (cdr_bits(mem (car_bits(mem  v))))) /\
        (mem2(car_bits(mem2(car_bits(mem2 v)))) =
         mem (car_bits(mem (car_bits(mem  v))))))))"),
 REPEAT STRIP_TAC
 THEN prt[LET_THM] THEN BETA_TAC
 THEN (ASSUME_TAC
       o (in_conv_rule BETA_CONV)
       o (rr[LET_THM])
       o UNDISCH_ALL
       o hd
       o IMP_CANON)
      Store14_root_2_lemma
 THEN (MAP_EVERY
       (ASSUME_TAC o UNDISCH_ALL)
       o IMP_CANON
       o (in_conv_rule BETA_CONV)
       o (rr[LET_THM]))
      Store14_car_cdr_2_lemma
 THEN IMP_RES_THEN IMP_RES_TAC AP_is_cons_lemma
 THEN poart[]
 THEN IMP_RES_n_THEN 4
      ((\th. ASSUM_LIST
	  (\thl. (port1 o (rr (path.thl)) o (SPEC "[F;T]")) th
	    THEN (port1 o (rr (path.thl)) o (SPEC "[F;F]")) th))
       o (SPECL ["cell1:word32";"cell2:word32"]))
      (hd(IMP_CANON Store14_oldpath_2_lemma))
 THEN rt[]);;

let Store14_caar_cdar_3_lemma = TAC_PROOF
(([],
 "is_cons(mem free) /\
  is_cons(mem(cdr_bits(mem free))) /\
  is_cons(mem(cdr_bits(mem(cdr_bits(mem free))))) /\
  ~(free = cdr_bits(mem free)) /\
  (mem NIL_addr = bus32_symb_append #0000000000000000000000000000) ==>
  (!v.
   is_cons(mem v) /\
   is_cons(mem(car_bits(mem v))) /\
   nonintersecting mem free v ==>
   (!cell1 cell2 cell3.
   let mem1 = Store14 free cell1 mem in
   let mem2 = Store14 (cdr_bits(mem free)) cell2 mem1 in
   let mem3 =
           Store14 (cdr_bits(mem1(cdr_bits(mem free)))) cell3 mem2 in
       ((mem3(cdr_bits(mem3(car_bits(mem3 v)))) =
         mem (cdr_bits(mem (car_bits(mem  v))))) /\
        (mem3(car_bits(mem3(car_bits(mem3 v)))) =
         mem (car_bits(mem (car_bits(mem  v))))))))"),
 REPEAT STRIP_TAC
 THEN prt[LET_THM] THEN BETA_TAC
 THEN (ASSUME_TAC
       o (in_conv_rule BETA_CONV)
       o (rr[LET_THM])
       o UNDISCH_ALL
       o hd
       o IMP_CANON)
      Store14_root_3_lemma
 THEN (MAP_EVERY
       (ASSUME_TAC o UNDISCH_ALL)
       o IMP_CANON
       o (in_conv_rule BETA_CONV)
       o (rr[LET_THM]))
      Store14_car_cdr_3_lemma
 THEN IMP_RES_THEN IMP_RES_TAC AP_is_cons_lemma
 THEN poart[]
 THEN IMP_RES_n_THEN 6
      ((\th. ASSUM_LIST
	    (\thl. (port1 o (rr (path.thl)) o (SPEC "[F;T]")) th
	     THEN (port1 o (rr (path.thl)) o (SPEC "[F;F]")) th))
       o (SPECL ["cell1:word32";"cell2:word32";"cell3:word32"]))
      (hd(IMP_CANON Store14_oldpath_3_lemma))
 THEN rt[]
  );;

let Store14_caar_cdar_4_lemma = TAC_PROOF
(([],
 "is_cons(mem free) /\
  is_cons(mem(cdr_bits(mem free))) /\
  is_cons(mem(cdr_bits(mem(cdr_bits(mem free))))) /\
  is_cons(mem(cdr_bits(mem(cdr_bits(mem(cdr_bits(mem free))))))) /\
  ~(free = cdr_bits(mem free)) /\
  ~(free = cdr_bits(mem(cdr_bits(mem free)))) /\
  ~(cdr_bits(mem free) = cdr_bits(mem(cdr_bits(mem free)))) /\
  (mem NIL_addr = bus32_symb_append #0000000000000000000000000000) ==>
  (!v.
   is_cons(mem v) /\
   is_cons(mem(car_bits(mem v))) /\
   nonintersecting mem free v ==>
   (!cell1 cell2 cell3 cell4.
   let mem1 = Store14 free cell1 mem in
   let mem2 = Store14 (cdr_bits(mem free)) cell2 mem1 in
   let mem3 =
           Store14 (cdr_bits(mem1(cdr_bits(mem free)))) cell3 mem2 in
   let mem4 =
           Store14 (cdr_bits(mem2(cdr_bits(mem1(cdr_bits(mem free))))))
                   cell4 mem3 in
       ((mem4(cdr_bits(mem4(car_bits(mem4 v)))) =
         mem (cdr_bits(mem (car_bits(mem  v))))) /\
        (mem4(car_bits(mem4(car_bits(mem4 v)))) =
         mem (car_bits(mem (car_bits(mem  v))))))))"),
 REPEAT STRIP_TAC
 THEN prt[LET_THM] THEN BETA_TAC
 THEN (ASSUME_TAC
       o (in_conv_rule BETA_CONV)
       o (rr[LET_THM])
       o UNDISCH_ALL
       o hd
       o IMP_CANON)
      Store14_root_4_lemma
 THEN (MAP_EVERY
       (ASSUME_TAC o UNDISCH_ALL)
       o IMP_CANON
       o (in_conv_rule BETA_CONV)
       o (rr[LET_THM]))
      Store14_car_cdr_4_lemma
 THEN IMP_RES_THEN IMP_RES_TAC AP_is_cons_lemma
 THEN poart[]
 THEN IMP_RES_n_THEN 9
      ((\th. ASSUM_LIST
           (\thl. (port1 o (rr (path.thl)) o (SPEC "[F;T]")) th
	     THEN (port1 o (rr (path.thl)) o (SPEC "[F;F]")) th))
      o (SPECL ["cell1:word32";"cell2:word32";"cell3:word32";"cell4:word32"]))
      (hd(IMP_CANON Store14_oldpath_4_lemma))
 THEN rt[]
  );;

timer false;;
% ================================================================= %
% Save the theorems, after first eliminating the let bindings.      %
%                                                                   %
% Of the last 8 theorems saved, only                                %
% 	Store14_cadr_cddr_1_lemma                                   %
% 	Store14_caar_cdar_3_lemma                                   %
% are used in the proof later.  They are retained for consistency.  %
% ================================================================= %
map (\name,thm.
     save_thm(name,
	      ((in_conv_rule BETA_CONV)
	       o (rr[LET_THM]))
	       thm))
 [ `Store14_root_1_lemma`,Store14_root_1_lemma
 ; `Store14_root_2_lemma`,Store14_root_2_lemma
 ; `Store14_root_3_lemma`,Store14_root_3_lemma
 ; `Store14_root_4_lemma`,Store14_root_4_lemma
 ; `Store14_car_cdr_1_lemma`,Store14_car_cdr_1_lemma
 ; `Store14_car_cdr_2_lemma`,Store14_car_cdr_2_lemma
 ; `Store14_car_cdr_3_lemma`,Store14_car_cdr_3_lemma
 ; `Store14_car_cdr_4_lemma`,Store14_car_cdr_4_lemma
 ; `Store14_cadr_cddr_1_lemma`,Store14_cadr_cddr_1_lemma
 ; `Store14_cadr_cddr_2_lemma`,Store14_cadr_cddr_2_lemma
 ; `Store14_cadr_cddr_3_lemma`,Store14_cadr_cddr_3_lemma
 ; `Store14_cadr_cddr_4_lemma`,Store14_cadr_cddr_4_lemma
 ; `Store14_caar_cdar_1_lemma`,Store14_caar_cdar_1_lemma
 ; `Store14_caar_cdar_2_lemma`,Store14_caar_cdar_2_lemma
 ; `Store14_caar_cdar_3_lemma`,Store14_caar_cdar_3_lemma
 ; `Store14_caar_cdar_4_lemma`,Store14_caar_cdar_4_lemma
 ];;

close_theory ();;
print_theory `-`;;
