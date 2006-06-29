%                                                                   %
% FILE: CU_wordn_proofs.ml                                          %
%                                                                   %
% DESCRIPTION: This proves some equalities and inequalities of      %
%              wordn constants.                                     %
%                                                                   %
% USES FILES:  cu_types.th                                          %
%                                                                   %
% Brian Graham 89.09.14                                             %
%                                                                   %
% Modifications:                                                    %
%                                                                   %
% ================================================================= %
new_theory `CU_wordn_proofs`;;

loadf `wordn`;;

new_parent `cu_types`;;

let word4_EQ_CONV = wordn_EQ_CONV (theorem `cu_types` `Word4_11`);;
let word5_EQ_CONV = wordn_EQ_CONV (theorem `cu_types` `Word5_11`);;

timer true;;
% ================================================================= %
% First, some theorems about the ineq/equality of wordn values      %
% ================================================================= %
letrec mk_word4_thms l n =
(0 < n) =>
 (let h' = el n l
  in
  let t' = filter (\t.not (t = h')) l
  in
  let tml = map (\t."(^h' = ^t)") t'
  in
  save_thm (`word_`^((implode o tl o explode o fst o dest_const)h'),
		  (LIST_CONJ
		   ((EQT_INTRO(REFL h')).(map word4_EQ_CONV tml))));
  mk_word4_thms l (n-1))
                  |
  TRUTH;;

letrec mk_word5_thms l n =
(0 < n) =>
 (let h' = el n l
  in
  let t' = filter (\t.not (t = h')) l
  in
  let tml = map (\t."(^h' = ^t)") t'
  in
  save_thm (`word_`^((implode o tl o explode o fst o dest_const)h'),
		  (LIST_CONJ
		   ((EQT_INTRO(REFL h')).(map word5_EQ_CONV tml))));
  mk_word5_thms l (n-1))
                  |
  TRUTH;;

let l4 =
["#0000";
 "#0001";
 "#0010";
 "#0011";
 "#0100";
 "#0101";
 "#0110";
 "#0111";
 "#1000";
 "#1001";
 "#1010";
 "#1011";
 "#1100"]
and l5 =
["#00000";
 "#00001";
 "#00010";
 "#00011";
 "#00100";
 "#00101";
 "#00110";
 "#00111";
 "#01000";
 "#01001";
 "#01010";
 "#01011";
 "#01100";
 "#01101";
 "#01110";
 "#01111";
 "#10000";
 "#10001";
 "#10010";
 "#10011";
 "#10100";
 "#10101";
 "#10110";
 "#10111"];;
 
%------------------------------------------------------------%
% This may benefit from changing the recursion, so memory is %
% not exhausted as quickly.                                  %
%------------------------------------------------------------%
mk_word4_thms l4 (length l4); mk_word5_thms l5 (length l5);;

timer false;;
close_theory ();;
print_theory `-`;;
