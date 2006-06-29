% SECD verification                                                 %
%                                                                   %
% FILE:         microcode.ml                                        %
%                                                                   %
% DESCRIPTION: This file reads the intermediate form of the         %
%              secd microcode and defines the ROM device function.  %
%                                                                   %
% USES FILES:  cu_types                                             %
%                                                                   %
% Brian Graham 06.11.90                                             %
%                                                                   %
% Modifications:                                                    %
% 15.11.90 - BtG - Completed revision so that the constant          %
%                  ROM_fun is introduced using new_specification,   %
%                  and is a partially defined function.  As a       %
%                  result, mk_thm is no longer used in this file.   %
% 16.04.91 - BtG - updated to HOL12                                 %
% 27.08.91 - BtG - fixed to run under AKCL-loop replaced recursion. %
% ================================================================= %
new_theory `microcode`;;

% ================================================================= %
% Thanks to jvt: this should compile the files building the large   %
% data structures, so they should run much faster.  27.08.91.       %
% ================================================================= %
set_flag (`compile_on_the_fly`, true);;

loadt `wordn`;;
new_parent `cu_types`;;
% ================================================================= %
% load some i/o routines ...                                        %
% note that we will only read integers in this theory, so           %
% that applying int_of_string to whatever is read will not          %
% blow up.                                                          %
% ================================================================= %
loadt `io`;;

let ratom = int_of_string o read_atom;;

timer true;;
% ================================================================= %
% Processing routines for the input:                                %
% **********************************                                %
% ================================================================= %

% ================================================================= %
% Convert a num to a boolean list (1's and 0's).                    %
%                                                                   %
% Functions:                                                        %
%   mk_bit_list (num,size) res                                      %
%       returns a list of strings of 1's and 0's,                   %
%       of length size.                                             %
%   example : #mk_bit_list (3,4)[];;                                %
%             [`0`; `0`; `1`; `1`] : string list                    %
%                                                                   %
%   mk_bit_list_list pairl                                          %
%       returns a list of all the string representations of         %
%       the number,size pairs, appended into one list.              %
%       Note that only CONS is used, not append.                    %
%       Also, the list keeps the same order.                        %
%   example : mk_bit_list_list [3,3;2,3];;                          %
%             [`0`; `1`; `1`; `0`; `1`; `0`] : string list          %
% ================================================================= %
let rem2 x = x-(2*(x/2));;

letrec mk_bit_list (num, size) res =
   (size = 0) => res |
                 (mk_bit_list ((num/2), (size-1)) 
                   (((string_of_int o rem2) num) . res));;

letrec mk_bit_list_list pairl =
   (pairl = []) => [] |
                  mk_bit_list (hd pairl)
                   (mk_bit_list_list (tl pairl));;
% ================================================================= %
% Two functions for creating constants.                             %
% These 2 functions return the appropriate wordn object, from       %
% a pair or list of pairs.                                          %
% ================================================================= %
let mk_word9_from_num n =
	mk_const
           (implode (`#` . (mk_bit_list (n,9) ([]:(string)list))),
           ":word9");;

let mk_word27_from_list l =
	mk_const (implode (`#` . (mk_bit_list_list l)), ":word27");;
		  
% ================================================================= %
% Process one address: read in the microcode intermediate           %
% form, and convert it to a pair: (address, code):word9#word27.     %
% ================================================================= %
let mk_micro_instr in_file =
  let addr = ratom in_file
  and status = ratom in_file
  and read = ratom in_file
  and write = ratom in_file
  and alu = ratom in_file
  and test = ratom in_file
  and A = ratom in_file
 in
 let field_list = [A,9; test,4; alu,4; write,5; read,5]
 in
 (mk_word9_from_num addr, mk_word27_from_list field_list) ;;

let make_instr_list limit in_file llst =
  letref count,accum = limit,[]
  in
  if (count = 0)
  then rev accum
  loop (count := count-1; accum := ((mk_micro_instr in_file).accum));;
% ================================================================= %
% Open up the file and get the raw data...                          %
%                                                                   %
% We start with a list of word9#word27 constants, so these          %
% should only be created once.                                      %
% ================================================================= %
let in_file = open_file `in` `intermediate`;;

let instr_list = make_instr_list (ratom in_file) in_file [];;

close_file in_file;;
% ================================================================= %
letrec exp n m =
  (m=0) => 1
         | n * (exp n (m-1));;

% ================================================================= %
% Build the required data structures first                          %
%                                                                   %
% micro_f is the microcode property of a function "f"               %
% ================================================================= %
let micro_f = list_mk_conj (map (\(a,b). "(f:word9->word27)^a = ^b") instr_list);;

% ================================================================= %
% Build a decision tree for the instructions set, using arbitrary   %
% values on unused branches.                                        %
% ================================================================= %
letrec fill_tree n limit l =
  ((n = 0)
   => (snd(hd l),(tl l))
    | let full_half = exp 2 (n-1)
      in
      (full_half < limit)
      => (let (rtree,ll) = fill_tree (n-1) full_half l
         in
	 let (ltree,lll) = fill_tree (n-1) (limit-full_half) ll
	 in
	 ("^(mk_v n) => ^ltree | ^rtree",lll))
       | let tr,ll = (fill_tree (n-1) limit l)
         in
         ("^(mk_v n) => (@w27.F)| ^tr", ll))
where
 mk_v n = mk_var(`b`^(string_of_int n),":bool")
;;

let mtree = fst (fill_tree 9 (length instr_list) instr_list);;

% ================================================================= %
% Define a function as the decision tree.                           %
%                                                                   %
% This definition is introduced simply to reduce the term size in   %
% the theorems which evaluate the decision tree at specific         %
% addresses.  It is unnecessary otherwise.                          %
% ================================================================= %
let w9 = "Word9 (Bus b9 (Bus b8 (Bus b7 (Bus b6  (Bus b5
                (Bus b4 (Bus b3 (Bus b2 (Wire (b1:bool)
                )))))))))";;

let partial_mfunc = new_recursive_definition
    false
    (theorem `cu_types` `Word9`)
    `partial_mfunc`
    "partial_mfunc ^w9 = ^mtree";;

% ================================================================= %
% Prove the result of evaluating "partial_mfunc" applied to all 399 %
% microcode addresses.                                              %
% ================================================================= %
let bools_of_wordn a =
 map (\x. (x = `0`) => "F" | "T")
     ((tl o explode o fst o dest_const) a);;

let micro_proof_fcn (a,v) = TAC_PROOF
(([],mk_eq(mk_comb("partial_mfunc",a), v)),
 SUBST1_TAC(wordn_CONV a)
 THEN SUBST1_TAC (SPECL (bools_of_wordn a) partial_mfunc)
 THEN prt[COND_CLAUSES]
 THEN REFL_TAC);;

% for some unknown reason, the following is marginally less efficient...
let micro_proof_fcn'' (a,v) =
 ( (prr[COND_CLAUSES])
 o (SUBS [SYM(wordn_CONV a)])
 o (SPECL (bools_of_wordn a)))partial_mfunc;;
%

let partial_mfunc_proof_fcn l =
  letref inlist,outlist = l,[]
  in
  if (inlist=[])
  then rev outlist
  loop
  ( tty_write(`proving partial_mfunc_`^
	      (implode(tl(explode(fst(dest_const(fst(hd inlist)))))))^`
`);
	 outlist := (micro_proof_fcn (hd inlist)).outlist ;
	 inlist := tl inlist
       );;

let thmlist = partial_mfunc_proof_fcn instr_list;;
%
puffin.cl.cam.ac.uk  Spark IPC with 16meg:

Run time: 2408.7s
Garbage collection time: 1025.4s
Intermediate theorems generated: 32718

gj.cpsc.ucalgary.ca  Spark2 with 48meg  27.08.91:

Run time: 532.4s
Intermediate theorems generated: 24339
%

% ================================================================= %
% Use the previous theorems to prove the existance of a function    %
% as described by micro_f.                                          %
% Use the existence theorem to define a new constant with the       %
% property given by micro_f.                                        %
% ================================================================= %
let exists_thm = TAC_PROOF
(([],"?f:word9->word27. ^micro_f"),
 EXISTS_TAC "partial_mfunc"
 THEN MATCH_ACCEPT_TAC (LIST_CONJ thmlist));;

let ROM_fun_thm = new_specification
  `ROM_fun_thm`
  [`constant`,`ROM_fun`]
  exists_thm;;

% ================================================================= %
% Write out each conjunct as a separate theorem.                    %
% ================================================================= %
letrec write_out n th =
  (is_conj (concl th))
   => ( save_thm(`ROM_fun_`^(string_of_int n),(CONJUNCT1 th))
      ; tty_write(`theorem ROM_fun_`^(string_of_int n)^` written
`)
      ; write_out (n+1)(CONJUNCT2 th))
    | save_thm(`ROM_fun_`^(string_of_int n), th);;

write_out 0 ROM_fun_thm;;
% ================================================================= %

timer false;;
close_theory ();;
print_theory `-`;;
