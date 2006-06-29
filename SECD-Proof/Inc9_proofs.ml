% SECD verification                                                 %
%                                                                   %
% FILE:        Inc9_proofs.ml                                       %
%                                                                   %
% DESCRIPTION: Proves a complete set of theorems about the Inc9     %
%              function applied to any relevant mpc value.          %
%                                                                   %
% USES FILES:  cu_types.th                                          %
%                                                                   %
% Brian Graham 89.09.01                                             %
%                                                                   %
% Modifications:                                                    %
% ================================================================= %
new_theory `Inc9_proofs`;;

loadf `wordn`;;

new_parent `cu_types`;;

let Inc9        = definition `cu_types` `Inc9`
and inc         = definition `cu_types` `inc`
and Bits9_Word9 = theorem    `cu_types` `Bits9_Word9`;;

% ================================================================= %
let ID_THM = GEN_ALL (RIGHT_BETA (REFL "(\f:*.f)x"));;

timer true;;
% ================================================================= %
% We prove 9 lemmas, one for each extent that the carry propagates. %
% This will vastly speed up the proof of the 400 lemmas, since      %
% we will need only do a wordn_CONV and a rewrite with the correct  %
% lemma.                                                            %
% ================================================================= %
let lemma_00 = prove
  ("Inc9 (Word9 (Bus b9 (Bus b8 (Bus b7 (Bus b6 (Bus b5
                (Bus b4 (Bus b3 (Bus b2 (Wire F)))))))))) =
          Word9 (Bus b9 (Bus b8 (Bus b7 (Bus b6 (Bus b5
                (Bus b4 (Bus b3 (Bus b2 (Wire T)))))))))",
   prt[Inc9; o_THM; theorem `cu_types` `Bits9_Word9`; inc]
   THEN prt [LET_DEF]
   THEN re_conv_tac ETA_CONV
   THEN rt [ID_THM]
   THEN re_conv_tac (REWR_CONV UNCURRY_DEF ORELSEC BETA_CONV)
   THEN rt[]
  );;

let lemma_01 = prove
  ("Inc9 (Word9 (Bus b9 (Bus b8 (Bus b7 (Bus b6 (Bus b5
                (Bus b4 (Bus b3 (Bus F (Wire T)))))))))) =
          Word9 (Bus b9 (Bus b8 (Bus b7 (Bus b6 (Bus b5
                (Bus b4 (Bus b3 (Bus T (Wire F)))))))))",
   prt[Inc9; o_THM; theorem `cu_types` `Bits9_Word9`; inc]
   THEN prt [LET_DEF]
   THEN re_conv_tac ETA_CONV
   THEN rt [ID_THM]
   THEN re_conv_tac (REWR_CONV UNCURRY_DEF ORELSEC BETA_CONV)
   THEN rt[]
  );;

let lemma_02 = prove
  ("Inc9 (Word9 (Bus b9 (Bus b8 (Bus b7 (Bus b6 (Bus b5
                (Bus b4 (Bus F  (Bus T (Wire T)))))))))) =
          Word9 (Bus b9 (Bus b8 (Bus b7 (Bus b6 (Bus b5
                (Bus b4 (Bus T (Bus F (Wire F)))))))))",
   prt[Inc9; o_THM; theorem `cu_types` `Bits9_Word9`; inc]
   THEN prt [LET_DEF]
   THEN re_conv_tac ETA_CONV
   THEN rt [ID_THM]
   THEN re_conv_tac (REWR_CONV UNCURRY_DEF ORELSEC BETA_CONV)
   THEN rt[]
  );;

let lemma_03 = prove
  ("Inc9 (Word9 (Bus b9 (Bus b8 (Bus b7 (Bus b6 (Bus b5
                (Bus F (Bus T  (Bus T (Wire T)))))))))) =
          Word9 (Bus b9 (Bus b8 (Bus b7 (Bus b6 (Bus b5
                (Bus T (Bus F (Bus F (Wire F)))))))))",
   prt[Inc9; o_THM; theorem `cu_types` `Bits9_Word9`; inc]
   THEN prt [LET_DEF]
   THEN re_conv_tac ETA_CONV
   THEN rt [ID_THM]
   THEN re_conv_tac (REWR_CONV UNCURRY_DEF ORELSEC BETA_CONV)
   THEN rt[]
  );;

let lemma_04 = prove
  ("Inc9 (Word9 (Bus b9 (Bus b8 (Bus b7 (Bus b6 (Bus F
                (Bus T (Bus T  (Bus T (Wire T)))))))))) =
          Word9 (Bus b9 (Bus b8 (Bus b7 (Bus b6 (Bus T
                (Bus F (Bus F (Bus F (Wire F)))))))))",
   prt[Inc9; o_THM; theorem `cu_types` `Bits9_Word9`; inc]
   THEN prt [LET_DEF]
   THEN re_conv_tac ETA_CONV
   THEN rt [ID_THM]
   THEN re_conv_tac (REWR_CONV UNCURRY_DEF ORELSEC BETA_CONV)
   THEN rt[]
  );;

let lemma_05 = prove
  ("Inc9 (Word9 (Bus b9 (Bus b8 (Bus b7 (Bus F (Bus T
                (Bus T (Bus T  (Bus T (Wire T)))))))))) =
          Word9 (Bus b9 (Bus b8 (Bus b7 (Bus T (Bus F
                (Bus F (Bus F (Bus F (Wire F)))))))))",
   prt[Inc9; o_THM; theorem `cu_types` `Bits9_Word9`; inc]
   THEN prt [LET_DEF]
   THEN re_conv_tac ETA_CONV
   THEN rt [ID_THM]
   THEN re_conv_tac (REWR_CONV UNCURRY_DEF ORELSEC BETA_CONV)
   THEN rt[]
  );;

let lemma_06 = prove
  ("Inc9 (Word9 (Bus b9 (Bus b8 (Bus F (Bus T (Bus T
                (Bus T (Bus T  (Bus T (Wire T)))))))))) =
          Word9 (Bus b9 (Bus b8 (Bus T (Bus F (Bus F
                (Bus F (Bus F (Bus F (Wire F)))))))))",
   prt[Inc9; o_THM; theorem `cu_types` `Bits9_Word9`; inc]
   THEN prt [LET_DEF]
   THEN re_conv_tac ETA_CONV
   THEN rt [ID_THM]
   THEN re_conv_tac (REWR_CONV UNCURRY_DEF ORELSEC BETA_CONV)
   THEN rt[]
  );;

let lemma_07 = prove
  ("Inc9 (Word9 (Bus b9 (Bus F (Bus T (Bus T (Bus T
                (Bus T (Bus T  (Bus T (Wire T)))))))))) =
          Word9 (Bus b9 (Bus T (Bus F (Bus F (Bus F
                (Bus F (Bus F (Bus F (Wire F)))))))))",
   prt[Inc9; o_THM; theorem `cu_types` `Bits9_Word9`; inc]
   THEN prt [LET_DEF]
   THEN re_conv_tac ETA_CONV
   THEN rt [ID_THM]
   THEN re_conv_tac (REWR_CONV UNCURRY_DEF ORELSEC BETA_CONV)
   THEN rt[]
  );;

let lemma_08 = prove
  ("Inc9 (Word9 (Bus F (Bus T (Bus T (Bus T (Bus T
                (Bus T (Bus T  (Bus T (Wire T)))))))))) =
          Word9 (Bus T (Bus F (Bus F (Bus F (Bus F
                (Bus F (Bus F (Bus F (Wire F)))))))))",
   prt[Inc9; o_THM; theorem `cu_types` `Bits9_Word9`; inc]
   THEN prt [LET_DEF]
   THEN re_conv_tac ETA_CONV
   THEN rt [ID_THM]
   THEN re_conv_tac (REWR_CONV UNCURRY_DEF ORELSEC BETA_CONV)
   THEN rt[]
  );;

let rem (x,y) = x - y * (x / y);;

letrec mk_bit_list (num, size) res =
   (size = 0) => res | (mk_bit_list ((num/2), (size-1)) 
                          (((string_of_int o rem) (num,2)) . res));;

let mk_word9_from_num n =
    mk_const (implode (`#` . (mk_bit_list (n,9) ([]:(string)list))),
              ":word9");;

letrec num_carries num  =
   (rem (num,2) = 0) => 0 | 1 + (num_carries (num/2));;

let lemma_list =
[ lemma_00 ; lemma_01 ; lemma_02 ; lemma_03 ; lemma_04
; lemma_05 ; lemma_06 ; lemma_07 ; lemma_08
];;

let prove_inc_thms stop =
 letref count = 0
 in
 if (stop < count)
 then ()
 loop
  (let base = mk_word9_from_num count
   and next = mk_word9_from_num (count + 1)
   and lemm = el (1 + (num_carries count)) lemma_list
   in
   ( prove_thm (concat `Inc9_lem_` (string_of_int count),
                "Inc9 ^base = ^next",
                in_conv_tac wordn_CONV
                THEN rt[lemm]
               )
   ; count := count+1
   ));;

prove_inc_thms 400;;

timer false;;
close_theory();;
print_theory `-`;;
