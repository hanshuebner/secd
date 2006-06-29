%                                                                 %
% FILE: phase_proof_fcn.ml                                        %
%                                                                 %
% DESCRIPTION: Provides a proof function that returns a theorem   %
%              about the value of the outputs and the next state  %
%              of the implementation for any valid mpc value.     %
%                                                                 %
%               top level functions:                              %
%                 phase_proof_fcn :(:word9)term -> theorem        %
%                 proof_loop 0 43;;                               %
%                    (produces theorems for values 0 through 43)  %
%                                                                 %
% USES FILES:  SYS_proofs.th, wordn library, unwind library,      %
%              SPLIT_CONJUNCTS.ml, template.ml,                   %
%              cu_types.th, dp_types.th                           %
%                                                                 %
% Brian Graham 27.11.89                                           %
%                                                                 %
% Modifications:                                                  %
% 03.01.90 - Stripped out all theorems, etc. and placed in parent %
%            theories.  It is no longer a theory, but just a file %
%            of function definitions to be loaded.                %
% 09.05.90 - renamed phase_...                                    %
% 27.11.91 - BtG - updated to HOL2 (UNWIND/PRUNE)                 %
% =============================================================== %

% =============================================================== %
% In order to use this file, one must be in a theory with         %
% the following conditions holding:                               %
%  * SYS_proofs must be an ancestor theory                        %
% =============================================================== %
let mtime = ":num";;

let msig = ":^mtime->bool"
and w9_mvec = ":^mtime->word9"
and w14_mvec = ":^mtime->word14"
and w27_mvec = ":^mtime->word27"
and w32_mvec = ":^mtime->word32";;

let mem14_32 = ":word14->word32";;
let m14_32_mvec = ":^mtime->^mem14_32";;
%%

loadf `wordn`;; 
map load_library
[ `unwind`];;
loadt `SPLIT_CONJUNCTS`;;
loadt `phase_template`;;

letrec truncate i l =
 if i=0 then [] else hd l.truncate(i-1)(tl l);;

letrec seg (m,n) l =
 (if m<0 or n<m then fail
  if m=0 then truncate ((n-m)+1) l
         else seg (m-1,n-1) (tl l)
 ) ? failwith `seg`;;

load_theorem `SYS_proofs` `Base_thm`;;

map (load_definition `cu_types`)
[ `A_field`
; `Write_field`
; `Read_field`
; `Alu_field`
; `Test_field`
];;
map (load_theorem `dp_types`)
 [ `bus32_cons_fields_lemma`
 ; `car_bits_thm`
 ; `cdr_bits_thm`
 ; `addr_to_num_inst`
 ; `bus_append_lemma`
 ];;

% ================================================================= %
% Now some functions, etc. to use in the proof function, largely    %
% to manipulate conversions of numbers to bit strings, etc.         %
% ================================================================= %
letrec int_of_bin l v =
  (l = []) => v |
              (int_of_bin (tl l) (v + v + ((hd l = `0`)=> 0 | 1)));;

let word9_EQ_CONV = wordn_EQ_CONV (theorem `cu_types` `Word9_11`);;

% ============================================================ %
% convert a num to a boolean list (1's and 0's).               %
%                                                              %
% functions:                                                   %
%   mk_bit_list (num,size) res                                 %
%       returns a list of strings of 1's and 0's,              %
%       of length size.                                        %
%   example : #mk_bit_list (3,4)[];;                           %
%             [`0`; `0`; `1`; `1`] : string list               %
% ============================================================ %
let rem (x,y) = x - y * (x / y);;

letrec mk_bit_list (num, size) res =
   (size = 0) => res |
                 (mk_bit_list ((num/2), (size-1)) 
                   (((string_of_int o rem) (num,2)) . res));;

% ============================================================ %
% two functions for creating constants.                        %
% these 2 functions return the appropriate wordn object, from  %
% a pair or list of pairs.                                     %
% ============================================================ %
let mk_word9_from_num n =
	mk_const
           (implode (`#` . (mk_bit_list (n,9) ([]:(string)list))),
           ":word9");;

let splice al bl = map2 (\x,y. x,y) (al,bl);;

% ================================================================= %
% Some things specific to doing the proofs ...                      %
% ================================================================= %
% |- ((mpc t = #000010110) \/ (mpc t = #000011000) =                %
%     (mpc t = #000010110) \/ (mpc t = #000011000)) /\              %
%    ((mpc t = #000101011) \/ (mpc t = #000011000) =                %
%     (mpc t = #000101011) \/ (mpc t = #000011000))                 %
% ================================================================= %
let flag_lemma = CONJ
(REFL "(mpc (t:num) = #000010110) \/ (mpc t = #000011000)")
(REFL "(mpc (t:num) = #000101011) \/ (mpc t = #000011000)");;

let mpc_marker = genvar ":word9";;

let flag_template1 =
 "((mpc (t:num) = #000010110) \/ (mpc       t = #000011000) =
   (^mpc_marker = #000010110) \/ (^mpc_marker = #000011000)) /\
  ((mpc (t:num) = #000101011) \/ (mpc       t = #000011000) =
   (^mpc_marker = #000101011) \/ (^mpc_marker = #000011000))" ;;

let flag_template2 =
 "((mpc (t:num) = #000010110) \/ (mpc       t = #000011000) = 
   idl \/ error) /\
  ((mpc (t:num) = #000101011) \/ (mpc       t = #000011000) =
   tocs \/ error)" ;;

% =============================================================== %
% The little forward proof rule gets rid of nasty existentially   %
% quantified variables, as the final step in the top proof func.  %
% =============================================================== %
let getridofit thm =
  prr [car_bits_thm; cdr_bits_thm;
       AND_CLAUSES; EXISTS_SIMP; addr_to_num_inst]
      (re_conv_rule EXISTS_AND_CONV thm);;

% =============================================================== %
% Specialized unwinding function for the general proof function.  %
%                                                                 %
% This unwinding conversion will use for unwinding only those     %
% conjuncts whose rhs does not have a lhs from any conjunct free  %
% in it.  It considers the entire lhs in judging this, and thus   %
% will unwind in places where checking the variable names alone   %
% will not permit.                                                %
% This process is repeated until no more unwinds are possible.    %
% NOTE: it is possible to get into an infinite loop, if the       %
%       equations rewrite have a cycle in which the lhs of        %
%       one of them reappears on a rhs.                           %
% =============================================================== %
letrec my_UNWIND_CONV tm =
 let p tm =
  (let eqns = conjuncts tm
   in 
   letrec check_frees l t = (if null l            then true
			     if free_in (hd l)t   then false
			     else                 check_frees (tl l) t)
   in
   let lefts = mapfilter lhs eqns
   in
  (\t. check_frees lefts (rhs t) ? false))
 in
 let th = UNWIND_ONCE_CONV (p tm) tm
 in  if lhs (concl th) = rhs (concl th)
     then th
     else th TRANS (my_UNWIND_CONV (rhs (concl th)));;

% replaced by the more general conversion above...

let atom_name tm = (fst o (\t. dest_var t ? dest_const t) o line_var) tm 
                   ? failwith `atom_name`;; 

let UNWIND_ALL_BUT_CONV l tm =
 (let line_names = subtract (mapfilter atom_name (conjuncts tm)) l
  in
  let p line = \tm. (atom_name tm) = line
  in
  let itfn line = \th. th TRANS (UNWIND_CONV (p line) (rhs (concl th)))
  in
  itlist itfn line_names (REFL tm)
 ) ? failwith `UNWIND_ALL_BUT_CONV`;;
%
% =============================================================== %
% The main proof function.  This is designed to produce any       %
% of the 400 lemmas required, evaluating all outputs of the       %
%  control unit for a given mpc value.                            %
%                                                                 %
% It is not fast, and may yet require optimization.  Recorded     %
% timing (for arg = "#110000110") is :                            %
% 	Run time: 270.8s                                          %
% 	Garbage collection time: 486.5s                           %
% 	Intermediate theorems generated: 21558                    %
%                                                                 %
% Format:                                                         %
%         prove_CU_lemma "#000111000";;                           %
%    returns:                                                     %
%         [ "clock_constraint SYS_Clocked"                        %
%         ; "CU SYS_Clocked ...          "                        %
%         ]                                                       %
%         |- (mpc t = #000111000) ==>                             %
%            (mpc (SUC t) = #000111001) /\                        %
%            (s0 (SUC t) = s0 t) /\                               %
%            ...                                                  %
%            (ralu t = F) /\                                      %
%            ...                                                  %
%            (flag1 t = F)                                        %
%                                                                 %
% =============================================================== %
let phase_proof_fcn addr =
  let assum = "(mpc:num->word9) t = ^addr"
  and add_tok = string_of_int(int_of_bin ((tl o explode o fst o dest_const) addr) 0)
  in				% 0.1s 0.0s %
  let ROM_lemma = SUBS [SYM (ASSUME assum)]
                       (theorem `microcode` (`ROM_fun_`^add_tok))
  in				% 0.1s 0.0s 3 %
  let char_list = (explode o fst o dest_const o snd o dest_eq o concl)
                   ROM_lemma
  in				% 0.0s 0.0s %
  let ROM_lemma' = (CONV_RULE o DEPTH_CONV o CHANGED_CONV)
                   wordn_CONV ROM_lemma
  in 				% 0.4s 0.0s 30 %

  let Test_field_lemmas =	% 2.6s 0.0s 147 %
    (let Test_val = implode(seg(10,13)char_list)
    in
    (CONJUNCTS
     (MP (theorem `CU_proofs` (`Test_base_`^Test_val))
         (SUBS[(SYM o wordn_CONV o mk_const)(`#`^Test_val,":word4")]
              (porr[Test_field](AP_TERM "Test_field" ROM_lemma'))))))

  and Alu_field_lemmas =	% 2.4s 20.0s 147 %
    (let Alu_val = implode(seg(14,17)char_list)
    in
    (CONJUNCTS
     (MP (theorem `CU_proofs` (`Alu_base_`^Alu_val))
         (SUBS[(SYM o wordn_CONV o mk_const)(`#`^Alu_val,":word4")]
              (porr[Alu_field](AP_TERM "Alu_field" ROM_lemma'))))))

  and Read_field_lemmas =	% 3.3s 0.0s 169 %
    (let Read_val = implode(seg(23,27)char_list)
    in
    (CONJUNCTS
     (MP (theorem `CU_proofs` (`Read_base_`^Read_val))
         (SUBS[(SYM o wordn_CONV o mk_const)(`#`^Read_val,":word5")]
              (porr[Read_field](AP_TERM "Read_field" ROM_lemma'))))))

  and Write_field_lemmas =	% 2.9s 0.0s 157 %
    (let Write_val = implode(seg(18,22)char_list)
    in
    (CONJUNCTS
     (MP (theorem `CU_proofs` (`Write_base_`^Write_val))
         (SUBS[(SYM o wordn_CONV o mk_const)(`#`^Write_val,":word5")]
              (porr[Write_field](AP_TERM "Write_field" ROM_lemma'))))))

  and Inc9_lem =		% 0.1s 0.0s 3 %
    SUBS [SYM (ASSUME assum)] (theorem `Inc9_proofs` (`Inc9_lem_`^add_tok))

  and Afield_lem =		% 2.0s 0.0s 124 %
    SUBS [(SYM o wordn_CONV o mk_const)
          (implode(seg(0,9)char_list),":word9")]
         (porr [A_field](AP_TERM "A_field" ROM_lemma'))

  and Flag_lemmas = 		% 8.5s 20.1s 441 %
    CONJUNCTS
    (porr[OR_CLAUSES]
         (SUBST
          (splice (map (\tm. word9_EQ_CONV (mk_eq (addr,tm)))
	               ["#000010110";"#000011000";"#000101011"])
                  ["idl:bool"; "error:bool"; "tocs:bool"])
         flag_template2
         (SUBST [ASSUME assum, mpc_marker] flag_template1 flag_lemma)))

  in
  let almost_thm = 		 % all rewrites:118.1s 107.5s 7104 %
  ( (CONV_RULE(DEPTH_EXISTS_CONV my_UNWIND_CONV
               THENC (DEPTH_CONV(CHANGED_CONV PRUNE_ONCE_CONV))))
  o (porr [EXISTS_SIMP])	
  o (porr [EXISTS_SIMP])			% 12.1s  0.0s  815 %
  o (porr [EXISTS_SIMP])	
  o (in1_conv_rule ETA_CONV)			%  5.7s  0.0s  398 %
  o (porr [bus_append_lemma])			%  6.2s 20.4s  419 %
  o (porr[COND_CLAUSES])			%  %
  o (porr[COND_CLAUSES])			%  %
  o (prr [AND_CLAUSES; OR_CLAUSES])		% 25.7s 45.0s 2047 %
  o (porr[IMP_CLAUSES])				%  %
  o (porr[AND_CLAUSES; OR_CLAUSES; IMP_CLAUSES; COND_CLAUSES])
						%  9.0s  0.0s  596 %
  o (SUBS ((tl o CONJUNCTS)NOT_CLAUSES))	%  0.3s  0.0s    5 %
  ) (SUBST					% 11.3s  0.0s    1 %
     (splice
      ( Alu_field_lemmas
      @ Test_field_lemmas
      @ Read_field_lemmas
      @ Write_field_lemmas
      @ Flag_lemmas
      @ [Inc9_lem; Afield_lem]
      )
      marker_list)
     template
     Base_thm)
  in
  DISCH assum
        (if (is_exists (concl almost_thm))
         then (getridofit almost_thm)
         else almost_thm)
  ;;

% =============================================================== %
% Recorded time for #000111000:                                   %
%                                                                 %
% Run time: 125.0s                                                %
% Garbage collection time: 169.1s                                 %
% Intermediate theorems generated: 6838                           %
%                                                                 %
% phase_proof_fcn (mk_word9_from_num 328);;                       %
% phase_proof_fcn (mk_word9_from_num 390);;                       %
% phase_proof_fcn (mk_word9_from_num 0);;                         %
% This is a nasty example:  try testing with it ...               %
% phase_proof_fcn (mk_word9_from_num 41);;                        %
% =============================================================== %

letrec proof_loop low high =
 (high < low) 
 => "T"
  |  (save_thm (`phase_lemma_`^(string_of_int high),
                 phase_proof_fcn (mk_word9_from_num high))
     ; tty_write(`phase_lemma_`^(string_of_int high)^` is proven (--> `^(string_of_int low)^`)
`)
     ; proof_loop low (high - 1));;

% =============================================================== %
% proof_loop 0 43;;                                               %
% =============================================================== %

timer true;;


% no longer used conversion
               (UNWIND_ALL_BUT_CONV
                 [ `mpc`; `s0`; `s1`; `s2`; `s3`; `memory`
                 ; `rmem_pin`; `bus_pins`; `buf1`; `buf2`
                 ; `mar_pins`; `s`; `e`; `c`; `d`; `free`
                 ; `x1`; `x2`; `car`; `arg`; `parent`; `root`
                 ; `y1`; `y2`; `write_bit_pin`; `flag0_pin`; `flag1_pin`
                 ])
%
