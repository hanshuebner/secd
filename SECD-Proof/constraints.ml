% SECD verification                                                 %
%                                                                   %
% FILE:                constraints.ml                               %
%                                                                   %
% DESCRIPTION:  Contains the constraint predicates that limit the   %
%               states that are subject to verification.            %
%                                                                   %
% USES FILES:   rt_SYS.th, top_SECD.th                              %
%                                                                   %
% Brian Graham 89.09.11                                             %
%                                                                   %
% Modifications:                                                    %
% 90.03.08 - changed the valid_codes_constraint to 14 bit values    %
%            from 9 bit values.                                     %
% 16.04.91 - BtG - updated to HOL12                                 %
% ================================================================= %
new_theory `constraints`;;

loadt `wordn`;;
load_library `integer`;;

map new_parent [`rt_SYS` ;
                `top_SECD` ];;
load_theorem `interface` `ID_THM`;;
load_theorem `cu_types` `Word9_11`;;
load_theorem `more_arith` `AND_DIST_OR`;;

map (load_definition `dp_types`)
 [ `atom_bits`
 ; `is_symbol`
 ; `is_cons`
 ];;
map (load_definition `rt_SECD`)
  [`opcode_bits`
  ];;
map (load_theorem `dp_types`)
  [`Bits28_Word28`
  ;`Word32_Induct`
  ;`bus32_symb_fields_lemma`
  ;`records_distinct`
  ;`rec_types_DISTINCT`
  ];;
load_definition `top_SECD` `nth`;;
load_definition `rt_SYS` `Store14`;;

letrec truncate i l =
 if i=0 then [] else hd l.truncate(i-1)(tl l);;

letrec seg (m,n) l =
 (if m<0 or n<m then fail
  if m=0 then truncate ((n-m)+1) l
         else seg (m-1,n-1) (tl l)
 ) ? failwith `seg`;;
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
let state = ":bool # bool";;
let state_msig = ":^mtime->^state";;
% ================================================================= %
let LD_instr9    = "#000000001"
and LD_instr28   = "#0000000000000000000000000001"
and LDC_instr9   = "#000000010"
and LDC_instr28  = "#0000000000000000000000000010"
and LDF_instr9   = "#000000011"
and LDF_instr28  = "#0000000000000000000000000011"
and AP_instr9    = "#000000100"
and AP_instr28   = "#0000000000000000000000000100"
and RTN_instr9   = "#000000101"
and RTN_instr28  = "#0000000000000000000000000101"
and DUM_instr9   = "#000000110"
and DUM_instr28  = "#0000000000000000000000000110"
and RAP_instr9   = "#000000111"
and RAP_instr28  = "#0000000000000000000000000111"
and SEL_instr9   = "#000001000"
and SEL_instr28  = "#0000000000000000000000001000"
and JOIN_instr9  = "#000001001"
and JOIN_instr28 = "#0000000000000000000000001001"
and CAR_instr9   = "#000001010"
and CAR_instr28  = "#0000000000000000000000001010"
and CDR_instr9   = "#000001011"
and CDR_instr28  = "#0000000000000000000000001011"
and ATOM_instr9  = "#000001100"
and ATOM_instr28 = "#0000000000000000000000001100"
and CONS_instr9  = "#000001101"
and CONS_instr28 = "#0000000000000000000000001101"
and EQ_instr9    = "#000001110"
and EQ_instr28   = "#0000000000000000000000001110"
and ADD_instr9   = "#000001111"
and ADD_instr28  = "#0000000000000000000000001111"
and SUB_instr9   = "#000010000"
and SUB_instr28  = "#0000000000000000000000010000"
and MUL_instr9   = "#000010001"
and MUL_instr28  = "#0000000000000000000000010001"
and DIV_instr9   = "#000010010"
and DIV_instr28  = "#0000000000000000000000010010"
and REM_instr9   = "#000010011"
and REM_instr28  = "#0000000000000000000000010011"
and LEQ_instr9   = "#000010100"
and LEQ_instr28  = "#0000000000000000000000010100"
and STOP_instr9  = "#000010101"
and STOP_instr28 = "#0000000000000000000000010101";;

timer true;;
% ================================================================= %
% Abstracting from the "state" of the rt level implementation to    %
% the top level spec state concerns only the mpc contents.  The     %
% mapping is defined only for 4 mpc values, and is an arbitrary     %
% value otherwise.                                                  %
% ================================================================= %
let state_abs = new_definition 
 (`state_abs`,
  "state_abs mpc =
      (mpc = #000010110) => idle          |  % 22 %
      (mpc = #000011000) => error0        |  % 24 %
      (mpc = #000011010) => error1        |  % 26 %
      (mpc = #000101011) => top_of_cycle  |  % 43 %
                            (@stat.F)");;

let state_abs_thm = prove_thm
(`state_abs_thm`,
 "(state_abs #000010110 = idle)         /\
  (state_abs #000011000 = error0)       /\
  (state_abs #000101011 = top_of_cycle) /\ 
  (state_abs #000011010 = error1)",
  rt[state_abs]
  THEN in_conv_tac wordn_CONV
  THEN rt[Word9_11; Bus_11; Wire_11]
  );;

let is_major_state = new_definition 
 (`is_major_state`,
  "is_major_state mpc (t:^mtime) =
      (mpc t = #000010110) \/
      (mpc t = #000011000) \/
      (mpc t = #000101011) \/
      (mpc t = #000011010)");;
      
let is_major_state_lemma = prove
("is_major_state mpc t ==>
     (state_abs (mpc t) =
      (mpc t = #000010110) => idle          |     % 22 %
      (mpc t = #000011000) => error0        |     % 24 %
      (mpc t = #000011010) => error1        |     % 26 %
   %  (mpc t = #000101011) => % top_of_cycle) "   % 43 %  ,
 prt[is_major_state; state_abs]
 THEN STRIP_TAC
 THEN art[]
 );;

%=================================================================%
% The system clock always cycles, never the shift register clock. %
%=================================================================%
let clock_constraint = new_definition
(`clock_constraint`,
 "clock_constraint (SYS_Clocked:^msig) =
  !t:^mtime. SYS_Clocked t"
 );;

%=================================================================%
% 3 reserved words always contain the symbolic constants.         %
%=================================================================%
let reserved_words_constraint = new_definition
(`reserved_words_constraint`,
 "reserved_words_constraint (mpc:^w9_mvec) (memory:^m14_32_mvec)=
  !t:^mtime. (state_abs (mpc t) = top_of_cycle) ==>
       ((memory t NIL_addr =
         bus32_symb_append #0000000000000000000000000000) /\
        (memory t T_addr   =
         bus32_symb_append #0000000000000000000000000001) /\
        (memory t F_addr   =
         bus32_symb_append #0000000000000000000000000010))"
 );;

% ================================================================= %
% A function to trace a car/cdr chain in a memory.                  %
% Note that we check that the cells are cons cells, otherwise the   %
%      path could take a 14 bit field of a symbol or number,        %
%      and end up in a meaningless memory location.                 %
% Note also that this function returns pointers to cells in memory, %
%      not the cells themselves.                                    %
% ================================================================= %
let path = new_list_rec_definition
(`path`,
 "(path (mem:word14->word32) (v:word14) [] = v) /\
  (path mem v (CONS l L) =
  (is_cons (mem v))
   => l => (path mem(cdr_bits(mem v))L)
         | (path mem(car_bits(mem v))L)
    | v)
 ");;

% ================================================================= %
% Predicate for path args for cdr'ing through free list.            %
% ================================================================= %
let all_cdr_path = new_list_rec_definition
(`all_cdr_path`,
 "(all_cdr_path [] = T) /\
  (all_cdr_path (CONS h tl) = h /\ (all_cdr_path tl))");;

% ================================================================= %
% free list is linear ending with NIL                               %
% ================================================================= %
let linear_free_list = new_definition
(`linear_free_list`,
 "linear_free_list (mem:word14->word32) (free:word14) = 
  !l1 l2. (all_cdr_path l1) /\ (all_cdr_path l2) ==>
          ~(l1 = l2) ==>
          (path mem free l1 = path mem free l2) ==>
          (path mem free l1 = NIL_addr)"
 );;

% ================================================================= %
% non intersection of cells reachable from v and those from free.   %
% ================================================================= %
let nonintersecting = new_definition
(`nonintersecting`,
 "nonintersecting (mem:word14->word32) (free:word14) (v:word14) =
  (!l1 l2. (all_cdr_path l2) ==>
           ~(path mem free l2 = NIL_addr) ==>
           ~(path mem v l1 = path mem free l2))"
 );;

% ================================================================= %
% a specific word is not in the free list.                          %
% ================================================================= %
let not_in_free_list = new_definition
(`not_in_free_list`,
 "not_in_free_list (mem:word14->word32) (free:word14) (v:word14) =
  !l. (all_cdr_path l) ==> ~(path mem free l = v)"
 );;

% ================================================================= %
% Function to require n cells in the free list.                     %
% ================================================================= %
let n_cells_in_free_list = new_definition
(`n_cells_in_free_list`,
 "n_cells_in_free_list (mem:word14->word32)(free:word14) n =
  (!n':num. (n' < n) ==>
            (is_cons (nth n' (mem o cdr_bits)(mem free))))"
 );;

% ================================================================= %
% The well formed free list, when in top_of_cycle state:            %
%  - is nonempty, containing 4 cells minimum                        %
%  - is a linear cdr-linked list                                    %
%  - does not intersect any cell in the s,e,c, or d data structures %
%  - the head of the free list is not the reserved NUM_addr.        %
% ================================================================= %
let well_formed_free_list = new_definition
(`well_formed_free_list`,
 "well_formed_free_list (memory:^m14_32_mvec) (mpc:^w9_mvec) 
                        (free:^w14_mvec) (s:^w14_mvec)
                        (e:^w14_mvec) (c:^w14_mvec) (d:^w14_mvec) =
 !t:^mtime.
   (state_abs (mpc t) = top_of_cycle) ==>
     (n_cells_in_free_list (memory t) (free t) 4) /\
     (linear_free_list (memory t) (free t)) /\
     (let nonintersecting_with_free_list =
	  (nonintersecting (memory t) (free t))
      in
      (nonintersecting_with_free_list (s t) /\
       nonintersecting_with_free_list (e t) /\
       nonintersecting_with_free_list (c t) /\
       nonintersecting_with_free_list (d t))) /\
     (not_in_free_list (memory t) (free t) NUM_addr)"
 );;

%=================================================================%
% Once initialized, there is always a valid program in memory.    %
% Presently it is written to ensure that a valid instruction      %
% opcode is in place.  This will need revision to include a       %
% requirement for valid arguments as well.                        %
%                                                                 %
%                 | next_c                                        %
%             __ _v                                               %
%      c' -->|__|__|head_c                                        %
%         ____/   \__ __                                          %
%  instr'|____|   |__|__|                                         %
%              ____/   \__ __                                     %
%             |____|   |__|__|                                    %
%                       /   \...                                  %
%                                                                 %
% The complexity of this constraint requires some consideration.  %
% Hardly any of the specific constraints here, aside from the     %
% possible instruction bit values and the requirement that the    %
% arguments to the LD instruction be a pair of positive integers  %
% when abstracted from word32 to integer, apply to the proof of   %
% the next state of the machine from the rtl view.                %
%                                                                 %
% The additional constraints on the type of records in memory     %
% (for example, that the top of s  is a cons cell for the CAR     %
% instruction) are needed for the abstracted operation to         %
% correspond to the top level description.  Would it not be       %
% better if the top level had these constraints, rather than      %
% muddying the picture here?                                      %
%                                                                 %
% How can these constraints be introduced?                        %
%                                                                 %
% 1. as part of the top level definition: i.e. the behaviour is   %
%    determined iff the constraint holds                          %
% 2. as a distinct constraint introduced in the correctness       %
%    statement:  i.e. low level constraints ==>                   %
% 		    ^SYS_imp ==>                                  %
%                     high_level_constraints                      %
% 			(on abstracted signals) ==>               %
%                     top_SECD                                    %
%                                                                 %
% The possible instruction codes are over constrained here.       %
% The full 14 bit field is defined for each instruction, while the%
% machine will work perfectly well if the high order bits are not %
% all 0's.                                                        %
%=================================================================%
let valid_codes_constraint = new_definition
(`valid_codes_constraint`,
 "valid_codes_constraint (memory:^m14_32_mvec) (mpc:^w9_mvec)
                           (c :^w14_mvec) = 
   !t:^mtime.
   (state_abs (mpc t) = top_of_cycle) ==>
     let head_c = memory t (c  t)
     in
      let instr' = (memory t) (car_bits head_c)
      and next_c = (cdr_bits head_c)
      in
       let instr = opcode_bits instr'
       in
       (((instr = ^LD_instr9) /\		       
         let arg_cons_cell = memory t (car_bits (memory t next_c))
         in
          let m_cell = memory t (car_bits arg_cons_cell)
          and n_cell = memory t (cdr_bits arg_cons_cell)
          in
          ((is_number m_cell) /\
           (is_number n_cell) /\
           (~(NEG (iVal (Bits28 (atom_bits m_cell))))) /\
           (~(NEG (iVal (Bits28 (atom_bits n_cell))))))
         ) \/
         (instr = ^LDC_instr9)  \/   (instr = ^LDF_instr9)  \/
         (instr = ^AP_instr9)   \/   (instr = ^RTN_instr9)  \/
         (instr = ^DUM_instr9)  \/   (instr = ^RAP_instr9)  \/
         (instr = ^SEL_instr9)  \/   (instr = ^JOIN_instr9) \/
         (instr = ^CAR_instr9)  \/   (instr = ^CDR_instr9)  \/
         (instr = ^ATOM_instr9) \/   (instr = ^CONS_instr9) \/
         (instr = ^EQ_instr9)   \/   (instr = ^ADD_instr9)  \/
         (instr = ^SUB_instr9)  \/
%        (instr = ^MUL_instr9)  \/   (instr = ^DIV_instr9)  \/ %
%        (instr = ^REM_instr9)  \/                             %
         (instr = ^LEQ_instr9)  \/   (instr = ^STOP_instr9))"
 );;

% ================================================================= %
% valid_codes_lemma =                                               %
% |- !memory mpc c .                                                %
%     valid_codes_constraint memory mpc c  =                        %
%     (!t.                                                          %
%       (state_abs(mpc t) = top_of_cycle) ==>                       %
%       (opcode_bits(memory t(car_bits(memory t(c  t))))            %
% 		  = #000000001) /\                                  %
%       is_number (memory t(car_bits(memory t(car_bits(memory t     %
% 		   (cdr_bits(memory t(c  t)))))))) /\               %
%       is_number (memory t(cdr_bits(memory t(car_bits(memory t     %
%                    (cdr_bits(memory t(c  t)))))))) /\             %
%       ~NEG(iVal(Bits28(atom_bits(memory t(car_bits(memory t       %
%          (car_bits(memory t(cdr_bits(memory t(c  t))))))))))) /\  %
%       ~NEG(iVal(Bits28(atom_bits(memory t(cdr_bits(memory t       %
%          (car_bits(memory t(cdr_bits(memory t(c  t))))))))))) \/  %
%       (opcode_bits(memory t(car_bits(memory t(c  t))))            %
% 		  = #000000010) \/                                  %
%       (opcode_bits(memory t(car_bits(memory t(c  t))))            %
% 		  = #000000011) \/                                  %
% 		         ...                                        %
%       (opcode_bits(memory t(car_bits(memory t(c  t))))            %
% 		  = #000010100) \/                                  %
%       (opcode_bits(memory t(car_bits(memory t(c  t))))            %
% 		  = #000010101))                                    %
% ================================================================= %
let valid_codes_lemma = save_thm
(`valid_codes_lemma`,
 ( (in_conv_rule BETA_CONV)
 o (prr[ID_THM])
 o (in_conv_rule ETA_CONV)
 o (prr[LET_DEF]))
 valid_codes_constraint
 );;

% ================================================================= %
% LD:   has an argument in c  consisting of the cons of 2 numbers,  %
%       should also have a constraint requiring there to be         %
%       long enough lists in the environment.                       %
%                                                                   %
% LDC:  has an atomic argument in c                                 %
%                                                                   %
% LDF:  has an argument in c                                        %
%                                                                   %
% AP:   closure & args on s : (car s ) and (cdr s )                 %
%           are both cons records                                   %
%                                                                   %
% RAP:  same as AP, plus                                            %
%       NIL on top of e                                             %
%                                                                   %
% DUM:  none                                                        %
%                                                                   %
% RTN:  only one arg on top of s ,                                  %
%       d  has s, e, c components,                                  %
%       nothing after RTN on c                                      %
%                                                                   %
% JOIN: d  is a cons,                                               %
%       nothing after JOIN in c                                     %
%                                                                   %
% SEL:  symbol on top of s                                          %
%       2 args in c                                                 %
%                                                                   %
% CAR, CDR:                                                         %
%       a cons record on top of s                                   %
%                                                                   %
% ATOM: one arg on top of s                                         %
%                                                                   %
% CONS, EQ:                                                         %
%       2 args on top of s                                          %
%                                                                   %
% ADD, SUB, MUL, DIV, REM, LEQ:                                     %
%       2 NUMERIC args on top of s                                  %
%                                                                   %
% STOP: last thing in control list,                                 %
%       s  is a list                                                %
% ================================================================= %
let valid_program_constraint = new_definition
(`valid_program_constraint`,
 "valid_program_constraint
  (memory:^m14_32_mvec) (mpc:^w9_mvec) (button_pin:^msig)
  (s :^w14_mvec) (e :^w14_mvec) (c :^w14_mvec) (d :^w14_mvec) = 
                           
   !t:^mtime.

   (((state_abs (mpc t) = idle) /\ button_pin t) ==>
     (is_cons (memory t NUM_addr)) /\
     (is_cons (memory t (car_bits (memory t NUM_addr))))) /\

   ((state_abs (mpc t) = top_of_cycle) ==>
     let head_c = memory t (c  t)
     in
     ((is_cons head_c) /\
      let instr' = (memory t) (car_bits head_c)
      and next_c = (cdr_bits head_c)
      in
      ((is_number instr') /\
       let instr = atom_bits instr'
       in
        (((instr = ^LD_instr28) /\	
          (is_cons (memory t next_c)) /\
          let arg_cons_cell = memory t (car_bits (memory t next_c))
          in
          ((is_cons arg_cons_cell) /\
           let m_cell = memory t (car_bits arg_cons_cell)
           and n_cell = memory t (cdr_bits arg_cons_cell)
           in
           ((is_number m_cell) /\
            (is_number n_cell) /\
            let m = (iVal(Bits28(atom_bits m_cell)))
            and n = (iVal(Bits28(atom_bits n_cell)))
            in
            ((~NEG m) /\
             (~NEG n) /\
             (!m'. (m' <= (pos_num_of m))  ==>
                   (is_cons (nth m' ((memory t) o cdr_bits)
                             (memory t (e  t))))) /\
             (!n'. (n' <= (pos_num_of n)) ==>
                   (is_cons (nth n' ((memory t) o cdr_bits)
                                 (memory t(car_bits 
                                            (nth (pos_num_of m)
                                            ((memory t) o cdr_bits)
                                            (memory t (e  t)))))))))))
         ) \/
         ((instr = ^LDC_instr28) /\	
          (is_cons (memory t next_c)) /\
          (is_atom (memory t (car_bits (memory t next_c))))
         ) \/
         ((instr = ^LDF_instr28) /\	
          (is_cons (memory t next_c)) 
         ) \/
         (((instr = ^AP_instr28) \/
           ((instr = ^RAP_instr28) /\	
            (is_cons (memory t (e  t))) /\
            (car_bits (memory t (e  t)) = NIL_addr) /\
            (e t = cdr_bits(memory t(car_bits(memory t(s t))))))) /\
          (is_cons (memory t (s  t))) /\
          (is_cons (memory t (car_bits (memory t (s  t))))) /\
          (is_cons (memory t (cdr_bits (memory t (s  t)))))
         ) \/
         ((instr = ^RTN_instr28) /\	
          (is_cons (memory t (d  t))) /\
          (is_cons (memory t (cdr_bits (memory t (d  t))))) /\
          (is_cons (memory t (cdr_bits (memory t
                              (cdr_bits (memory t (d  t))))))) /\
          (is_cons (memory t (s  t))) /\
          (next_c  = NIL_addr)
         ) \/
         (instr = ^DUM_instr28) \/
         ((instr = ^SEL_instr28) /\	
          (is_cons (memory t (s  t))) /\
          (is_symbol (memory t (car_bits (memory t (s  t))))) /\
          (is_cons (memory t next_c)) /\
          (is_cons (memory t (cdr_bits (memory t next_c))))
         ) \/
         ((instr = ^JOIN_instr28) /\	
          (is_cons (memory t (d  t))) /\
          (next_c = NIL_addr)
         ) \/
         (((instr = ^CAR_instr28) \/
           (instr = ^CDR_instr28)) /\	
          (is_cons (memory t (s  t))) /\
          (is_cons (memory t (car_bits (memory t (s  t)))))
         ) \/
         ((instr = ^ATOM_instr28) /\	
          (is_cons (memory t (s  t)))
         ) \/
         ((instr = ^CONS_instr28) /\	
          (is_cons (memory t (s  t))) /\
          (is_cons (memory t (cdr_bits (memory t (s  t)))))
         ) \/
         ((instr = ^EQ_instr28) /\	
          (is_cons (memory t (s  t))) /\
          (is_cons (memory t (cdr_bits (memory t (s  t))))) /\
          ((is_atom (memory t (car_bits (memory t (s t))))) \/
           (is_atom (memory t (car_bits (memory t (cdr_bits (memory t (s  t))))))))
         ) \/
         (((instr = ^ADD_instr28) \/
           (instr = ^SUB_instr28) \/
%          (instr = ^MUL_instr28) \/                               %
%          (instr = ^DIV_instr28) \/                               %
%          (instr = ^REM_instr28) \/                               %
           (instr = ^LEQ_instr28)) /\	
          (is_cons (memory t (s  t))) /\
          (is_cons (memory t (cdr_bits (memory t (s  t))))) /\
          (is_number (memory t (car_bits (memory t (s  t))))) /\
          (is_number (memory t (car_bits (memory t
                                (cdr_bits (memory t (s  t)))))))
         ) \/
         ((instr = ^STOP_instr28) /\	
          (is_cons (memory t (s  t))) /\
          (next_c = NIL_addr))))))"
 );;


let valid_program_lemma = save_thm
(`valid_program_lemma`,
 ( (in_conv_rule BETA_CONV)
 o (in_conv_rule ETA_CONV)
 o (prr[LET_DEF])
 o (prr[porr[CONJ_SYM] AND_DIST_OR]))
 valid_program_constraint
 );;

% ================================================================= %
% If the larger atom_bits subfields are equal then the smaller      %
% opcode_bits subfields are equal.                                  %
% ================================================================= %
let EQ_atom_IMP_EQ_opcode = prove_thm
(`EQ_atom_IMP_EQ_opcode`,
 "!w32.opcode_bits
        (Word32(Bus F(Bus F(Bus T(Bus T(Bits28(atom_bits w32))))))) =
       opcode_bits w32",
 INDUCT_THEN Word32_Induct ASSUME_TAC
 THEN REPEAT GEN_TAC
 THEN port[atom_bits]
 THEN port[Bits28_Word28]
 THEN port[opcode_bits]
 THEN REFL_TAC
 );;

% ================================================================= %
% The weaker valid_codes_constraint is implied by the stronger      %
% valid_programs_constraint.  The distinct constraints are used     %
% to explicitly minimize the constraints required for the           %
% liveness of the chip, while the more extensive constraints        %
% are needed in the proof of the correctness relating the rtl and   %
% SYS_spec.                                                         %
% ================================================================= %
let valid_program_IMP_valid_codes = prove_thm
(`valid_program_IMP_valid_codes`,
 "!memory mpc button_pin s  e  c  d .
   valid_program_constraint memory mpc button_pin s  e  c  d  ==>
     valid_codes_constraint memory mpc c ",
 REPEAT GEN_TAC
 THEN SUBST_TAC
      [SPEC_ALL valid_codes_lemma; SPEC_ALL valid_program_lemma]
 THEN DISCH_THEN
      (\th. GEN_TAC
            THEN DISCH_THEN
	         (\th1. CONJUNCTS_THEN2
	                (K ALL_TAC)
			(\th2. CONJUNCTS_THEN2
			       (K ALL_TAC)
			       (CONJUNCTS_THEN2
				(K ALL_TAC)
				(REPEAT_TCL
				 DISJ_CASES_THEN
				 (REPEAT_TCL STRIP_THM_THEN ASSUME_TAC)))
			       (MP th2 th1))
		        (SPEC_ALL th)))
 THEN FIRST_ASSUM
 (\th. is_eq (concl th) 
   => type_of (fst (dest_eq (concl th))) = ":word28"
      =>
  (SUBST1_TAC o (porr[SYM(wordn_CONV
			  (mk_const(implode(`#`.(seg(20,28)(explode
			   (fst(dest_const(snd(dest_eq
			    (concl th)))))))),":word9")))])
	      o (porr[opcode_bits])
              o (porr[Bits28_Word28])
	      o (in_conv_rule wordn_CONV)
	      o (porr [EQ_atom_IMP_EQ_opcode])
	      o (prr[o_THM])
              o (AP_TERM "opcode_bits o Word32 o (Bus F) o (Bus F)
                          o (Bus T) o (Bus T) o Bits28")) th
	      | NO_TAC | NO_TAC )
 THEN art[]
 );;

% ================================================================= %
% The NIL reserved word is a symbol.                                %
% ================================================================= %
let NIL_is_symbol = prove
("(memory NIL_addr =
   bus32_symb_append #0000000000000000000000000000) ==>
  (is_symbol (memory NIL_addr))",
 DISCH_THEN SUBST1_TAC
 THEN port[is_symbol]
 THEN port[bus32_symb_fields_lemma]
 THEN REFL_TAC
 );;

% ================================================================= %
% If NIL reserved word is in place,                                 %
% then a cons cell address is distinct from NIL_addr.               %
% ================================================================= %
let NIL_not_cons = prove_thm
(`NIL_not_cons`,
 "(memory NIL_addr =
   bus32_symb_append #0000000000000000000000000000) ==>
  !free.
   is_cons (memory free) ==> 
   ~(free = NIL_addr)",
 DISCH_THEN (ASSUME_TAC o (MATCH_MP NIL_is_symbol))
 THEN GEN_TAC
 THEN STRIP_TAC
 THEN DISCH_THEN SUBST_ALL_TAC
 THEN IMP_RES_TAC (records_distinct)
 );;

% ================================================================= %
% Derive the meaning of the n_cells_in_free_list constraint at 4.   %
% ================================================================= %
let n_cells_in_free_list_4_thm = prove_thm
(`n_cells_in_free_list_4_thm`,
 "n_cells_in_free_list mem free 4 ==>
  is_cons(mem free) /\
  is_cons(mem(cdr_bits(mem free))) /\
  is_cons(mem(cdr_bits(mem(cdr_bits(mem free))))) /\
  is_cons(mem(cdr_bits(mem(cdr_bits(mem(cdr_bits(mem free)))))))",
 port[n_cells_in_free_list]
 THEN re_conv_tac num_CONV
 THEN DISCH_THEN
 (\th. MAP_EVERY
  (\tm. port1 
        (rr[LESS_MONO_EQ; LESS_0; nth; o_THM]
	   (SPEC tm th)))
  ["0";"SUC 0";"SUC(SUC 0)";"SUC(SUC(SUC 0))"])
 THEN rt[]
 );;

% ================================================================= %
% ================================================================= %
let cons_cells_not_NIL = prove
("reserved_words_constraint mpc memory ==>
  !t.
  (state_abs(mpc t) = top_of_cycle) ==>
  !v. 
   (is_cons(memory t v) ==> ~(v = NIL_addr))",
 port[reserved_words_constraint]
 THEN DISCH_THEN
 (\th1. GEN_TAC
        THEN DISCH_THEN
	(\th2. (ASSUME_TAC
		o (porr[SYM_RULE rec_types_DISTINCT])
		o (porr[bus32_symb_fields_lemma])
		o (porr[is_cons])
		o (AP_TERM "is_cons")
		o CONJUNCT1)
	 (MATCH_MP th1 th2)))
 THEN port[is_cons]
 THEN GEN_TAC
 THEN STRIP_TAC
 THEN DISCH_THEN SUBST_ALL_TAC
 THEN RES_TAC
);;

% ================================================================= %
% To begin, a set of lemmas that constrain how much of memory is    %
% affected by sequential Store14 operations, with parts of the      %
% well_formed_free_list constraint in effect.                       %
%                                                                   %
% If x is distinct from free list cells                             %
% and free list is linear,                                          %
% then mem[n+1 writes] at x is unchanged from mem[n writes] at x,   %
%      for 0 <= n <= 3                                              %
% ================================================================= %
let Store14_1_lemma = prove_thm
(`Store14_1_lemma`,
 "!x. ~(free = x) ==>
   !z. memory x = Store14 free z memory x",
 GEN_TAC
 THEN DISCH_THEN (STRIP_ASSUME_TAC o SYM_RULE)
 THEN GEN_TAC
 THEN port[Store14]
 THEN in1_conv_tac BETA_CONV
 THEN art[]
 );;

let Store14_2_step_lemma = prove
("!x.
  ~(free = x) /\
  ~(cdr_bits(memory free) = x) ==>
  !z zz.
   Store14 free zz memory x = 
%  memory x = ****** equally provable ******* %
   Store14 (cdr_bits(memory free)) z (Store14 free zz memory) x",
 GEN_TAC
 THEN DISCH_THEN (STRIP_ASSUME_TAC o SYM_RULE)
 THEN REPEAT GEN_TAC
 THEN prt[Store14]
 THEN in_conv_tac BETA_CONV
 THEN art[]
 );;

let Store14_3_step_lemma = prove
("!x.
  ~(free = x) /\
  ~(cdr_bits(memory free) = x) /\
  ~(cdr_bits(memory(cdr_bits(memory free))) = x) /\
  ~(free = cdr_bits(memory free))
  ==>
  !z zz zzz.
   Store14 (cdr_bits(memory free)) zz (Store14 free zzz memory) x = 
   Store14(cdr_bits(Store14 free zzz memory(cdr_bits(memory free))))
          z
          (Store14(cdr_bits(memory free))
                  zz
                  (Store14 free zzz memory))
          x",
 GEN_TAC
 THEN DISCH_THEN (STRIP_ASSUME_TAC o SYM_RULE)
 THEN REPEAT GEN_TAC
 THEN prt[Store14]
 THEN in_conv_tac BETA_CONV
 THEN art[]
 );;

% ================================================================= %
% The similar versions that take the cell back to the original      %
% memory, rather than just one step...                              %
%                                                                   %
% If x is distinct from free list cells                             %
% and free list is linear,                                          %
% then mem[n+1 writes] at x is unchanged from mem[0 writes] at x,   %
%      for 1 <= n <= 3                                              %
% ================================================================= %
let Store14_2_lemma = prove_thm
(`Store14_2_lemma`,
 "!x.
  ~(free = x) /\
  ~(cdr_bits(memory free) = x) ==>
  !z zz.
   memory x = 
   Store14 (cdr_bits(memory free)) z (Store14 free zz memory) x",
 GEN_TAC
 THEN DISCH_THEN (STRIP_ASSUME_TAC o SYM_RULE)
 THEN REPEAT GEN_TAC
 THEN prt[Store14]
 THEN in_conv_tac BETA_CONV
 THEN art[]
 );;

let Store14_3_lemma = prove_thm
(`Store14_3_lemma`,
 "!x.
  ~(free = x) /\
  ~(cdr_bits(memory free) = x) /\
  ~(cdr_bits(memory(cdr_bits(memory free))) = x) /\
  ~(free = cdr_bits(memory free))
  ==>
  !z zz zzz.
   memory x = 
   Store14(cdr_bits(Store14 free zzz memory(cdr_bits(memory free))))
          z
          (Store14(cdr_bits(memory free))
                  zz
                  (Store14 free zzz memory))
          x",
 GEN_TAC
 THEN DISCH_THEN (STRIP_ASSUME_TAC o SYM_RULE)
 THEN REPEAT GEN_TAC
 THEN prt[Store14]
 THEN in_conv_tac BETA_CONV
 THEN art[]
 );;

% ================================================================= %
% Note : an error uncovered here on 90.08.29.  There was an         %
%        incorrect 1st argument to the 2nd last Store14             %
% ================================================================= %
let Store14_4_lemma = prove_thm
(`Store14_4_lemma`,
 "!x.
  ~(free = x) /\
  ~(cdr_bits(memory free) = x) /\
  ~(cdr_bits(memory(cdr_bits(memory free))) = x) /\
  ~(cdr_bits(memory(cdr_bits(memory(cdr_bits(memory free))))) = x) /\
  ~(free = cdr_bits(memory free)) /\
  ~(free = cdr_bits(memory(cdr_bits(memory free)))) /\
  ~(cdr_bits(memory free) =
    cdr_bits(memory(cdr_bits(memory free)))) ==>
  !z zz zzz zzzz.
   memory x =
   Store14(cdr_bits(Store14(cdr_bits(memory free))
                           zzz
                           (Store14 free zzzz memory)
                    (cdr_bits(Store14 free zzzz memory
                              (cdr_bits(memory free))))))
           z
           (Store14(cdr_bits(Store14 free zzzz memory
                             (cdr_bits(memory free))))
                   zz
                   (Store14(cdr_bits(memory free))
                           zzz
                           (Store14 free zzzz memory)))
           x",
 GEN_TAC
 THEN DISCH_THEN (STRIP_ASSUME_TAC o SYM_RULE)
 THEN REPEAT GEN_TAC
 THEN prt[Store14]
 THEN in_conv_tac BETA_CONV
 THEN art[]
 );;
 
% ================================================================= %
% Notice that for the 1st M_Cons, the precondition is an assumption.%
%                                                                   %
% If free list is linear and next cell is a cons,                   %
% then it remains a cons after 2-4 writes.                          %
% ================================================================= %
let M_Cons_2_precond_lemma = prove_thm
(`M_Cons_2_precond_lemma`,
 "~(free = (cdr_bits(memory free)))          /\
   is_cons(memory(cdr_bits(memory free)))    ==>
   !z. is_cons (Store14 free z memory(cdr_bits(memory free)))",
 REPEAT STRIP_TAC
 THEN IMP_RES_THEN (SUBST1_TAC o SYM o (SPEC "z:word32"))
        (SPEC "cdr_bits(memory(free:word14))" Store14_1_lemma)
 THEN art[]
 );;

let M_Cons_3_precond_lemma = prove_thm
(`M_Cons_3_precond_lemma`,
 "~(free = cdr_bits(memory free))                    /\
  ~(free = cdr_bits(memory(cdr_bits(memory free))))  /\
  ~(cdr_bits(memory free) =
    cdr_bits(memory(cdr_bits(memory free))))         /\
  is_cons(memory(cdr_bits(memory(cdr_bits(memory free))))) 
  ==>
  !z zz.
   is_cons(Store14(cdr_bits(memory free))
                  z
                  (Store14 free zz memory)
                  (cdr_bits(Store14 free zz memory
                            (cdr_bits(memory free)))))",
 DISCH_THEN
 \th.
 (\[th1;th2;th3;th4].
  REPEAT GEN_TAC
  THEN SUBST1_TAC
       (SYM_RULE
	(SPEC "zz:word32"
	      (MP (SPEC "cdr_bits(memory(free:word14))"
			Store14_1_lemma)
		  th1)))  
  THEN SUBST1_TAC
       (SYM_RULE
	(SPECL ["z:word32";"zz:word32"]
	     (MATCH_MP Store14_2_step_lemma (CONJ th2 th3))))
  THEN SUBST1_TAC
       (SYM_RULE
	(SPEC "zz:word32"
	      (MP (SPEC "cdr_bits(memory(cdr_bits(memory free)))"
			Store14_1_lemma)
		  th2)))
  THEN port1 th4
  ) (CONJUNCTS th)
 );;

let M_Cons_4_precond_lemma = prove_thm
(`M_Cons_4_precond_lemma`,
 "~(free = cdr_bits(memory free))                    /\
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
  !z zz zzz.
   is_cons
   (Store14
    (cdr_bits(Store14 free zzz memory(cdr_bits(memory free))))
    z
    (Store14(cdr_bits(memory free))zz(Store14 free zzz memory))
    (cdr_bits
     (Store14
      (cdr_bits(memory free))
      zz
      (Store14 free zzz memory)
      (cdr_bits(Store14 free zzz memory(cdr_bits(memory free)))))))",
 DISCH_THEN
 (\th. let [th1;th2;th3;th4;th5;th6;th7] = CONJUNCTS th in
       let thd = MATCH_MP Store14_2_step_lemma (CONJ th2 th4)
       and thc = MATCH_MP Store14_2_step_lemma (CONJ th3 th5)
       and tha = MATCH_MP Store14_3_step_lemma (LIST_CONJ [th3;th5;th6;th1]) in
 REPEAT GEN_TAC
 THEN 
 let thm1 =
 (SYM(SPEC "zzz:word32"
	   (MP (SPEC "cdr_bits(memory (free:word14))"
		     Store14_1_lemma)
	       th1)))
 in
 (SUBST1_TAC thm1
  THEN SUBST1_TAC (SYM (SPECL ["zz:word32";"zzz:word32"] thd))
  THEN (SUBST1_TAC
       o SYM
       o (SPEC "zzz:word32"))
      (MP (SPEC "cdr_bits(memory(cdr_bits(memory free)))"
		Store14_1_lemma)
	  th2)
  THEN SUBST1_TAC (SYM (SUBS[thm1](SPEC_ALL tha)))
  THEN (SUBST1_TAC
		 o SYM
		 o (SPECL ["zz:word32";"zzz:word32"])) thc
  THEN SUBST1_TAC
      (SYM(SPEC "zzz:word32"
		(MP (SPEC "cdr_bits(memory(cdr_bits(memory(cdr_bits(memory(free:word14))))))"
			  Store14_1_lemma)
		    th3)))
  THEN port1 th7 			  
  )));;

% ================================================================= %
% ================================================================= %
% ================================================================= %
% The well formed free list constraint flattened somewhat.          %
%                                                                   %
% The first 4 conjuncts follow directly from                        %
% n_cells_in_free_list_4_thm above.                                 %
% The remaining arise from the linear_free_list constraint,         %
% and the reserved_words_constraint for NIL_addr.                   %
% By using cons_cells_not_NIL with the rhs of                       %
% n_cells_in_free_list_4_thm, we get inequalities of the cells      %
% concerned and NIL_addr.                                           %
% Next, we split into the 6 conjuncts, and specialize               %
% linear_free_list with the appropriate path function arguments to  %
% get the cells concerned.                                          %
% Simplify the term by expanding definitions, and discharge.        %
% Rewrite with the is_cons assumptions.                             %
%                                                             qed.  %
% ================================================================= %
let well_formed_free_list_lemma = prove_thm
(`well_formed_free_list_lemma`,
 "(reserved_words_constraint mpc memory /\
   well_formed_free_list memory mpc free s e c d)==>
  !t.
  (state_abs(mpc t) = top_of_cycle) ==>
  ((is_cons(memory t(free t))) /\
   (is_cons(memory t(cdr_bits(memory t(free t))))) /\
   (is_cons(memory t(cdr_bits(memory t(cdr_bits(memory t(free t))))))) /\
   (is_cons(memory t(cdr_bits(memory t(cdr_bits(memory t
                    (cdr_bits(memory t(free t))))))))) /\
   (~(free t = cdr_bits(memory t(free t)))) /\
   (~(free t = cdr_bits(memory t(cdr_bits(memory t(free t)))))) /\
   (~(free t = cdr_bits(memory t(cdr_bits(memory t
              (cdr_bits(memory t(free t)))))))) /\
   (~(cdr_bits(memory t(free t)) =
          cdr_bits(memory t(cdr_bits(memory t(free t)))))) /\
   (~(cdr_bits(memory t(free t)) = cdr_bits(memory t(cdr_bits(memory t
              (cdr_bits(memory t(free t)))))))) /\
   (~(cdr_bits(memory t(cdr_bits(memory t(free t)))) = cdr_bits(memory t(cdr_bits(memory t
              (cdr_bits(memory t(free t)))))))))",
 DISCH_THEN
 (\th1. GEN_TAC THEN DISCH_THEN
  (\th2. (CONJUNCTS_THEN2
	  (\th3.ASSUME_TAC
	   (MATCH_MP(MATCH_MP cons_cells_not_NIL th3)th2))
	  (\th4.
	   (\[a;b;c;d].STRIP_ASSUME_TAC(MATCH_MP n_cells_in_free_list_4_thm a)
	               THEN art[] THEN RES_TAC THEN ASSUME_TAC b)
	   (CONJUNCTS(MATCH_MP(porr[well_formed_free_list]th4)th2)))
	  th1)))
 THEN let th = ASSUME "linear_free_list(memory t)(free (t:num))" in
 (REPEAT CONJ_TAC
  THENL
  (map
   (\(a,b).
    ( (\th1. ASSUME_TAC th1 THEN (UNDISCH_TAC (concl th1)))
    o (rr[all_cdr_path;CONS_11;NOT_NIL_CONS;path]))
    (SPECL [a;b] (porr[linear_free_list]th)))
   ["[]:(bool)list","[T]"
   ;"[]:(bool)list","[T;T]"
   ;"[]:(bool)list","[T;T;T]"
   ;"[T]","[T;T]"
   ;"[T]","[T;T;T]"
   ;"[T;T]","[T;T;T]"
   ]))
 THEN art[]
 );;

% ================================================================= %
% This theorem gives the desired form for the proof function in     %
% mu-prog_proof_fcn.ml, to replace the original general             %
% free_list_constraint with the newer constraints.                  %
% This covers the maximum of 4 cons'es done by any sequence (AP).   %
% ================================================================= %
let free_list_constraint_thm = prove_thm
(`free_list_constraint_thm`,
 "(reserved_words_constraint mpc memory /\
   well_formed_free_list memory mpc free s e c d) ==>
   !t:num. (state_abs (mpc t) = top_of_cycle) ==>

    (((free t) = NIL_addr) = F) /\

    (((cdr_bits(memory t(free t))) = NIL_addr) = F) /\

    (!c1.
     (cdr_bits(Store14 (free t) c1
		       (memory t)
		       (cdr_bits(memory t(free t)))) =
      NIL_addr) = F) /\

    (!c1 c2.
     (cdr_bits(Store14(cdr_bits(memory t(free t)))
		      c2
		      (Store14(free t)c1(memory t))
		      (cdr_bits(Store14 (free t) c1
					(memory t)
					(cdr_bits(memory t(free t))))
		      )) = NIL_addr) = F)",
 STRIP_TAC THEN GEN_TAC
 THEN STRIP_TAC
 THEN IMP_RES_THEN (IMP_RES_THEN IMP_RES_TAC)
                   well_formed_free_list_lemma
 THEN IMP_RES_THEN (IMP_RES_THEN IMP_RES_TAC)
                   cons_cells_not_NIL
 THEN prt[Store14]
 THEN in_conv_tac BETA_CONV
 THEN REPEAT CONJ_TAC
 THEN REPEAT GEN_TAC
 THEN REPEAT (EVERY_ASSUM (port1 o SYM_RULE) THEN art[])
 );;
 
% ================================================================= %
% Another derivation of properties of well_formed_free_list; this   %
% time the nonintersection component is extracted.                  %
% ================================================================= %
let well_formed_free_list_nonintersection_lemma = prove_thm
(`well_formed_free_list_nonintersection_lemma`,
 "well_formed_free_list memory mpc free s e c d ==>
    (!t.
      (state_abs(mpc t) = top_of_cycle) ==>
      nonintersecting(memory t)(free t)(s t) /\
      nonintersecting(memory t)(free t)(e t) /\
      nonintersecting(memory t)(free t)(c t) /\
      nonintersecting(memory t)(free t)(d t))",
 port[well_formed_free_list]
 THEN STRIP_TAC
 THEN GEN_TAC
 THEN DISCH_THEN
      (ANTE_RES_THEN (port1 o (in_conv_rule BETA_CONV) o (porr[LET_DEF])))
 THEN rt[]);;

timer false;;
close_theory ();;
print_theory `-`;;
