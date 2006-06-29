%                                                                  %
% FILE: CU_proofs.ml                                               %
%                                                                  %
% DESCRIPTION: This proves some properties of the register-        %
%              transfer definition of the control unit.            %
%                                                                  %
% USES FILES:  rt_CU.th, interface.th, constraints.th,             %
%              Inc9_proofs.th, CU_wordn_proofs.th                  %
%                                                                  %
% Brian Graham 12.09.89                                            %
%                                                                  %
% Modifications:                                                   %
% 13.09.89 - installed functions to prove 400 lemmas for each      %
%            mpc value                                             %
%          - also proved 37 lemmas about word4 and word5 to speed  %
%            the above proofs                                      %
% 14.09.89 - memory exhausted failure - this is too large to work. %
% 20.11.91 - BtG - updated to HOL2                                 %
% ================================================================ %
new_theory `CU_proofs`;;

loadf `wordn`;;

map new_parent [ `rt_CU`
	       ; `interface`
               ; `constraints`
               ; `Inc9_proofs`
               ; `CU_wordn_proofs`
               ];;

map (load_definition `rt_CU`)
[ `STATE_REG`
; `MPC9`
; `S_latch9`
; `ROM_t`
; `CU_DECODE`
; `CU`
];;
load_definition `constraints` `clock_constraint`;;
map (load_theorem `cu_types`)
[ `Word4_11`
; `Word5_11`
; `Word9_11`
];;
load_definition `interface` `one_asserted_12`;;
load_theorem `interface` `ID_THM`;;

map load_library
[ `unwind`
];;

letrec truncate i l =
 if i=0 then [] else hd l.truncate(i-1)(tl l);;

letrec seg (m,n) l =
 (if m<0 or n<m then fail
  if m=0 then truncate ((n-m)+1) l
         else seg (m-1,n-1) (tl l)
 ) ? failwith `seg`;;

map loadt 
[ `BINDER_EQ_TAC`
; `SPLIT_CONJUNCTS`
];;
% ================================================================= %
let mtime = ":num";;
let msig = ":^mtime->bool"
and w9_mvec = ":^mtime->word9"
and w27_mvec = ":^mtime->word27";;
let mvec = ":num->^msig";;
% ================================================================= %
%%

timer true;;
% ================================================================= %
let four_tuple_lemma = TAC_PROOF
(([],"((aa:word9,bb:word9,cc:word9,dd:word9) =
      x1 => (a',b',c',d') |
      x2 => (a'',b'',c'',d'') |
            (a''',b''',c''',d''')) =
   (aa = x1 => a' | x2 => a'' | a''') /\
   (bb = x1 => b' | x2 => b'' | b''') /\
   (cc = x1 => c' | x2 => c'' | c''') /\
   (dd = x1 => d' | x2 => d'' | d''')"),
 COND_CASES_TAC THEN COND_CASES_TAC THEN art[PAIR_EQ]);;

%------------------------------------------------------------%
% lemma to help unfold the state register definitions.       %
%------------------------------------------------------------%
let state_reg_lemma = TAC_PROOF
(([], 
 "STATE_REG SYS_Clocked load
         (next_mpc,next_s0,next_s1,next_s2,next_s3)
         (     mpc,     s0,     s1,     s2,     s3) =
 (mpc 0 = #000000000) /\
 (!t.mpc(SUC t)= (SYS_Clocked t =>         next_mpc t | mpc t)) /\
 (!t.s0(SUC t) = (SYS_Clocked t =>(load t =>next_s0 t | s0 t) | s0 t)) /\
 (!t.s1(SUC t) = (SYS_Clocked t =>(load t =>next_s1 t | s1 t) | s1 t)) /\
 (!t.s2(SUC t) = (SYS_Clocked t =>(load t =>next_s2 t | s2 t) | s2 t)) /\
 (!t.s3(SUC t) = (SYS_Clocked t =>(load t =>next_s3 t | s3 t) | s3 t))"),
  prt[STATE_REG; MPC9; S_latch9]
      
  THEN port[SPEC "mpc 0 = #000000000" CONJ_ASSOC]
  THEN REFL_TAC);;
%%

let stack_cell_lemma = TAC_PROOF
(([], "((push \/ pop) => 
           (push => 
            Inc9mpc | 
            (pop => (s1:*) | s0)) |
           s0) =
     (push =>  Inc9mpc | 
               (pop => s1 | s0))"),
 MAP_EVERY ASM_CASES_TAC ["push:bool"; "pop:bool"]
 THEN art[]);;

%------------------------------------------------------------%
% The, entire Control unit unwound.                          %
%------------------------------------------------------------%
let CU_unwound_lemma = prove_thm
(`CU_unwound_lemma`,
 "CU     SYS_Clocked
         button
         mpc s0 s1 s2 s3
         opcode
         atomflag bit30flag bit31flag zeroflag nilflag eqflag leqflag
         flag0 flag1
         ralu rmem rarg rbuf1 rbuf2 rcar rs re rc rd rmar rx1 rx2
         rfree rparent rroot ry1 ry2 rnum rnil rtrue rfalse rcons
         write_bit bidir
         warg wbuf1 wbuf2 wcar ws we wc wd wmar wx1 wx2
         wfree wparent wroot wy1 wy2
         dec add sub mul div rem
         setbit30 setbit31 resetbit31 replcar replcdr resetbit30 =
   (!t.
     (mpc 0 = #000000000) /\
     (mpc(SUC t) =
      (SYS_Clocked t => 
        ((((Test_field (ROM_fun (mpc t))) = #0001) \/
          ((Test_field (ROM_fun (mpc t))) = #0011) /\ bit30flag t \/
          ((Test_field (ROM_fun (mpc t))) = #0100) /\ bit31flag t \/
          ((Test_field (ROM_fun (mpc t))) = #0101) /\ eqflag t \/
          ((Test_field (ROM_fun (mpc t))) = #0110) /\ leqflag t \/
          ((Test_field (ROM_fun (mpc t))) = #0111) /\ nilflag t \/
          ((Test_field (ROM_fun (mpc t))) = #1000) /\ atomflag t \/
          ((Test_field (ROM_fun (mpc t))) = #1001) /\ zeroflag t \/
          ((Test_field (ROM_fun (mpc t))) = #1010) /\ button t \/
          ((Test_field (ROM_fun (mpc t))) = #1011)) => 
         (A_field (ROM_fun (mpc t))) | 
         (((Test_field (ROM_fun (mpc t))) = #1100) => 
          s0 t | 
          (((Test_field (ROM_fun (mpc t))) = #0010) => 
           opcode t | 
           Inc9(mpc t)))) | 
       mpc t)) /\
     (s0(SUC t) =
      (SYS_Clocked t => 
       ((Test_field (ROM_fun (mpc t)) = #1011) => 
        Inc9(mpc t) | 
        ((Test_field (ROM_fun (mpc t)) = #1100) => s1 t | s0 t)) |
       s0 t)) /\
     (s1(SUC t) =
      (SYS_Clocked t => 
       ((Test_field (ROM_fun (mpc t)) = #1011) => 
        s0 t | 
        ((Test_field (ROM_fun (mpc t)) = #1100) => s2 t | s1 t)) | 
       s1 t)) /\
     (s2(SUC t) =
      (SYS_Clocked t => 
       ((Test_field (ROM_fun (mpc t)) = #1011) => 
        s1 t | 
        ((Test_field (ROM_fun (mpc t)) = #1100) => s3 t | s2 t)) | 
       s2 t)) /\
     (s3(SUC t) =
      (SYS_Clocked t => 
       ((Test_field (ROM_fun (mpc t)) = #1011) => 
        s2 t | 
        ((Test_field (ROM_fun (mpc t)) = #1100) => #000000000 | s3 t)) | 
       s3 t)) /\
     (ralu t = ((Read_field (ROM_fun (mpc t))) = #00001)) /\
     (rmem t = ((Read_field (ROM_fun (mpc t))) = #00010)) /\
     (rarg t = ((Read_field (ROM_fun (mpc t))) = #00011)) /\
     (rbuf1 t = ((Read_field (ROM_fun (mpc t))) = #00100)) /\
     (rbuf2 t = ((Read_field (ROM_fun (mpc t))) = #00101)) /\
     (rcar t = ((Read_field (ROM_fun (mpc t))) = #00110)) /\
     (rs t = ((Read_field (ROM_fun (mpc t))) = #00111)) /\
     (re t = ((Read_field (ROM_fun (mpc t))) = #01000)) /\
     (rc t = ((Read_field (ROM_fun (mpc t))) = #01001)) /\
     (rd t = ((Read_field (ROM_fun (mpc t))) = #01010)) /\
     (rmar t = ((Read_field (ROM_fun (mpc t))) = #01011)) /\
     (rx1 t = ((Read_field (ROM_fun (mpc t))) = #01100)) /\
     (rx2 t = ((Read_field (ROM_fun (mpc t))) = #01101)) /\
     (rfree t = ((Read_field (ROM_fun (mpc t))) = #01110)) /\
     (rparent t = ((Read_field (ROM_fun (mpc t))) = #01111)) /\
     (rroot t = ((Read_field (ROM_fun (mpc t))) = #10000)) /\
     (ry1 t = ((Read_field (ROM_fun (mpc t))) = #10001)) /\
     (ry2 t = ((Read_field (ROM_fun (mpc t))) = #10010)) /\
     (rnum t = ((Read_field (ROM_fun (mpc t))) = #10011)) /\
     (rnil t = ((Read_field (ROM_fun (mpc t))) = #10100)) /\
     (rtrue t = ((Read_field (ROM_fun (mpc t))) = #10101)) /\
     (rfalse t = ((Read_field (ROM_fun (mpc t))) = #10110)) /\
     (rcons t = ((Read_field (ROM_fun (mpc t))) = #10111)) /\
     (write_bit t = ~((Write_field(ROM_fun (mpc t))) = #00001)) /\
     (bidir t = ~((Write_field(ROM_fun (mpc t))) = #00001)) /\
     (warg t = ((Write_field(ROM_fun (mpc t))) = #00010)) /\
     (wbuf1 t = ((Write_field(ROM_fun (mpc t))) = #00011)) /\
     (wbuf2 t = ((Write_field(ROM_fun (mpc t))) = #00100)) /\
     (wcar t = ((Write_field(ROM_fun (mpc t))) = #00101)) /\
     (ws t = ((Write_field(ROM_fun (mpc t))) = #00110)) /\
     (we t = ((Write_field(ROM_fun (mpc t))) = #00111)) /\
     (wc t = ((Write_field(ROM_fun (mpc t))) = #01000)) /\
     (wd t = ((Write_field(ROM_fun (mpc t))) = #01001)) /\
     (wmar t = ((Write_field(ROM_fun (mpc t))) = #01010)) /\
     (wx1 t = ((Write_field(ROM_fun (mpc t))) = #01011)) /\
     (wx2 t = ((Write_field(ROM_fun (mpc t))) = #01100)) /\
     (wfree t = ((Write_field(ROM_fun (mpc t))) = #01101)) /\
     (wparent t = ((Write_field(ROM_fun (mpc t))) = #01110)) /\
     (wroot t = ((Write_field(ROM_fun (mpc t))) = #01111)) /\
     (wy1 t = ((Write_field(ROM_fun (mpc t))) = #10000)) /\
     (wy2 t = ((Write_field(ROM_fun (mpc t))) = #10001)) /\
     (dec t = ((Alu_field (ROM_fun (mpc t))) = #0001)) /\
     (add t = ((Alu_field (ROM_fun (mpc t))) = #0010)) /\
     (sub t = ((Alu_field (ROM_fun (mpc t))) = #0011)) /\
     (mul t = ((Alu_field (ROM_fun (mpc t))) = #0100)) /\
     (div t = ((Alu_field (ROM_fun (mpc t))) = #0101)) /\
     (rem t = ((Alu_field (ROM_fun (mpc t))) = #0110)) /\
     (setbit30 t = ((Alu_field (ROM_fun (mpc t))) = #0111)) /\
     (setbit31 t = ((Alu_field (ROM_fun (mpc t))) = #1000)) /\
     (resetbit31 t = ((Alu_field (ROM_fun (mpc t))) = #1001)) /\
     (replcar t = ((Alu_field (ROM_fun (mpc t))) = #1010)) /\
     (replcdr t = ((Alu_field (ROM_fun (mpc t))) = #1011)) /\
     (resetbit30 t = ((Alu_field (ROM_fun (mpc t))) = #1100)) /\
     (flag0 t = (mpc t = #000010110) \/ (mpc t = #000011000)) /\
     (flag1 t = (mpc t = #000101011) \/ (mpc t = #000011000))
  )",
  SUBST1_TAC
      (SPEC_ALL CU) 			      %  10.1s  8.6s   75 %
  THEN port [state_reg_lemma; CU_DECODE; ROM_t]     %  72.4s 101.1s  2146 %
  THEN in_conv_tac let_CONV
  THEN port [four_tuple_lemma] 
  THEN CONV_TAC
       (RATOR_CONV
	(RAND_CONV
	 (DEPTH_EXISTS_CONV
	  ((REDEPTH_CONV(CHANGED_CONV(FORALL_AND_CONV)))
	   THENC (UNWIND_ALL_BUT_CONV [`mpc`; `s0`; `s1`; `s2`; `s3`]))
	   THENC PRUNE_CONV
	   THENC (REDEPTH_CONV(CHANGED_CONV(AND_FORALL_CONV)))
	   THENC RIGHT_AND_FORALL_CONV)))
  THEN port [stack_cell_lemma]
  THEN BINDER_EQ_TAC
  THEN REPEAT REORDER_SPLIT_CONJUNCTS_TAC
  );;
%%
%<
%------------------------------------------------------------%
% A function to abstract out a subterm from a theorem        %
% conclusion, so the result is beta_convertable to the       %
% original.  This is useful when the subterm will explode    %
% in the course of simplification, which can be done in      %
% one place rather than multiple occurrences in the term,    %
% and the beta reduction accomplished only after the         %
% simplification is complete.                                %
%------------------------------------------------------------%
let BETA_INV (t1,t2) thm =
  SUBS
    [SYM
     (BETA_CONV
      (mk_comb
       (mk_abs (t1, subst [t1,t2](concl thm)),
       t2)))]
  thm;;
>%

let base_thm = ((SPEC "t:^mtime") o UNDISCH o fst o EQ_IMP_RULE)
         CU_unwound_lemma;;

%-------------------------------------------------------------------%
% a series of partition lemmas let us split the huge control        %
% unit into segments, for proofs of each possibiliity for           %
% sets of ouput signals, etc.                                       %
%                                                                   %
% state_base_lemma =                                                %
% . |- (\tests.                                                     %
%        (mpc 0 = #000000000) /\                                    %
%        (mpc(SUC t) =                                              %
%         (SYS_Clocked t =>                                         %
%           (((tests = #0001) \/                                    %
%             (tests = #0011) /\ bit30flag t \/                     %
%             (tests = #0100) /\ bit31flag t \/                     %
%             (tests = #0101) /\ eqflag t \/                        %
%             (tests = #0110) /\ leqflag t \/                       %
%             (tests = #0111) /\ nilflag t \/                       %
%             (tests = #1000) /\ atomflag t \/                      %
%             (tests = #1001) /\ zeroflag t \/                      %
%             (tests = #1010) /\ button t \/                        %
%             (tests = #1011)) =>                                   %
%            A_field(ROM_fun(mpc t)) |                              %
%            ((tests = #1100) =>                                    %
%             s0 t |                                                %
%             ((tests = #0010) => opcode t | Inc9(mpc t)))) |       %
%          mpc t)) /\                                               %
%        (s0(SUC t) =                                               %
%         (SYS_Clocked t =>                                         %
%           ((tests = #1011) =>                                     %
%            Inc9(mpc t) |                                          %
%            ((tests = #1100) => s1 t | s0 t)) |                    %
%          s0 t)) /\                                                %
%        (s1(SUC t) =                                               %
%         (SYS_Clocked t =>                                         %
%           ((tests = #1011) => s0 t |                              %
%                               ((tests = #1100) => s2 t | s1 t)) | %
%          s1 t)) /\                                                %
%        (s2(SUC t) =                                               %
%         (SYS_Clocked t =>                                         %
%           ((tests = #1011) => s1 t |                              %
%                               ((tests = #1100) => s3 t | s2 t)) | %
%          s2 t)) /\                                                %
%        (s3(SUC t) =                                               %
%         (SYS_Clocked t =>                                         %
%           ((tests = #1011) =>                                     %
%            s2 t |                                                 %
%            ((tests = #1100) => #000000000 | s3 t)) |              %
%          s3 t)))                                                  %
%      (Test_field(ROM_fun(mpc t)))                                 %
% reads_base_lemma =                                                %
% . |- (\reads.                                                     %
%        (ralu t = (reads = #00001)) /\                             %
%        (rmem t = (reads = #00010)) /\                             %
%        (rarg t = (reads = #00011)) /\                             %
%        (rbuf1 t = (reads = #00100)) /\                            %
%        (rbuf2 t = (reads = #00101)) /\                            %
%        (rcar t = (reads = #00110)) /\                             %
%        (rs t = (reads = #00111)) /\                               %
%        (re t = (reads = #01000)) /\                               %
%        (rc t = (reads = #01001)) /\                               %
%        (rd t = (reads = #01010)) /\                               %
%        (rmar t = (reads = #01011)) /\                             %
%        (rx1 t = (reads = #01100)) /\                              %
%        (rx2 t = (reads = #01101)) /\                              %
%        (rfree t = (reads = #01110)) /\                            %
%        (rparent t = (reads = #01111)) /\                          %
%        (rroot t = (reads = #10000)) /\                            %
%        (ry1 t = (reads = #10001)) /\                              %
%        (ry2 t = (reads = #10010)) /\                              %
%        (rnum t = (reads = #10011)) /\                             %
%        (rnil t = (reads = #10100)) /\                             %
%        (rtrue t = (reads = #10101)) /\                            %
%        (rfalse t = (reads = #10110)) /\                           %
%        (rcons t = (reads = #10111)))                              %
%      (Read_field(ROM_fun(mpc t)))                                 %
% writes_base_lemma =                                               %
% . |- (\writes.                                                    %
%        (write_bit t = ~(writes = #00001)) /\                      %
%        (bidir t = ~(writes = #00001)) /\                          %
%        (warg t = (writes = #00010)) /\                            %
%        (wbuf1 t = (writes = #00011)) /\                           %
%        (wbuf2 t = (writes = #00100)) /\                           %
%        (wcar t = (writes = #00101)) /\                            %
%        (ws t = (writes = #00110)) /\                              %
%        (we t = (writes = #00111)) /\                              %
%        (wc t = (writes = #01000)) /\                              %
%        (wd t = (writes = #01001)) /\                              %
%        (wmar t = (writes = #01010)) /\                            %
%        (wx1 t = (writes = #01011)) /\                             %
%        (wx2 t = (writes = #01100)) /\                             %
%        (wfree t = (writes = #01101)) /\                           %
%        (wparent t = (writes = #01110)) /\                         %
%        (wroot t = (writes = #01111)) /\                           %
%        (wy1 t = (writes = #10000)) /\                             %
%        (wy2 t = (writes = #10001)))                               %
%      (Write_field(ROM_fun(mpc t)))                                %
% alus_base_lemma =                                                 %
% . |- (\alus.                                                      %
%        (dec t = (alus = #0001)) /\                                %
%        (add t = (alus = #0010)) /\                                %
%        (sub t = (alus = #0011)) /\                                %
%        (mul t = (alus = #0100)) /\                                %
%        (div t = (alus = #0101)) /\                                %
%        (rem t = (alus = #0110)) /\                                %
%        (setbit30 t = (alus = #0111)) /\                           %
%        (setbit31 t = (alus = #1000)) /\                           %
%        (resetbit31 t = (alus = #1001)) /\                         %
%        (replcar t = (alus = #1010)) /\                            %
%        (replcdr t = (alus = #1011)) /\                            %
%        (resetbit30 t = (alus = #1100)))                           %
%      (Alu_field(ROM_fun(mpc t)))                                  %
% outputs_base_lemma =                                              %
% . |- (flag0 t = (mpc t = #000010110) \/ (mpc t = #000011000)) /\  %
%      (flag1 t = (mpc t = #000101011) \/ (mpc t = #000011000))     %
%-------------------------------------------------------------------%
%<
let [state_base_lemma; reads_base_lemma; writes_base_lemma;
      alus_base_lemma; outputs_base_lemma] =
  (\l. [BETA_INV ("tests:word4",
                  "Test_field(ROM_fun((mpc:num->word9)t))")
                 (LIST_CONJ (seg(0,5)l));
        BETA_INV ("reads:word5",
                  "Read_field(ROM_fun((mpc:num->word9)t))")
                 (LIST_CONJ (seg(6,28)l));
        BETA_INV ("writes:word5",
                  "Write_field(ROM_fun((mpc:num->word9)t))")
                 (LIST_CONJ (seg(29,46)l));
        BETA_INV ("alus:word4",
                  "Alu_field(ROM_fun((mpc:num->word9)t))")
                 (LIST_CONJ (seg(47,58)l));
        LIST_CONJ (seg(59,60)l)
       ]
  ) (CONJUNCTS base_thm);;
>%
%%
%------------------------------------------------------------%
% derive the one_asserted'ness property of the alu outputs   %
% from their definition.  this is used later when the cu is  %
% composed with the dp, to drop the implication from the     %
% alu behavioural definition.                                %
%------------------------------------------------------------%
let alucntl_one_asserted_lemma = prove_thm
(`alucntl_one_asserted_lemma`,
 "CU     SYS_Clocked
         button
         mpc s0 s1 s2 s3
         opcode
         atomflag bit30flag bit31flag zeroflag nilflag eqflag leqflag
         flag0 flag1
         ralu rmem rarg rbuf1 rbuf2 rcar rs re rc rd rmar rx1 rx2
         rfree rparent rroot ry1 ry2 rnum rnil rtrue rfalse rcons
         write_bit bidir
         warg wbuf1 wbuf2 wcar ws we wc wd wmar wx1 wx2
         wfree wparent wroot wy1 wy2
         dec add sub mul div rem
         setbit30 setbit31 resetbit31 replcar replcdr resetbit30
  ==>
  one_asserted_12 replcar replcdr sub add dec mul div rem
                  setbit30 setbit31 resetbit30 resetbit31
 ",
 DISCH_THEN                                   % 137.0s 87.3s 4965 %
 ((\thl. port[one_asserted_12]
   THEN GEN_TAC
   THEN (REPEAT CONJ_TAC)
   THEN port thl) o
   (seg (47,58)) o
   CONJUNCTS o
   (SPEC "t:^mtime") o
   (SUBST [CU_unwound_lemma,"xxx:bool"]"xxx:bool"))
 THEN DISCH_THEN
 (\th. SUBST1_TAC th
  THEN rt[theorem `CU_wordn_proofs` ((`word_`^(implode o tl o explode o
					    fst o dest_const o snd o
					    dest_eq o concl)th))])
 );;                       % total for proof : 256.7s 239.8s 10044 %

let word4_EQ_CONV = wordn_EQ_CONV (Word4_11);;
let word5_EQ_CONV = wordn_EQ_CONV (Word5_11);;
let word9_EQ_CONV = wordn_EQ_CONV (Word9_11);;

%------------------------------------------------------------%
% we need lemmas for each used mpc value, giving the outputs %
% of each signal.  this should be generated somewhat         %
% automatically if feasible....  this first effort will      %
% ensure the form of the lemmas is reasonable.               %
%------------------------------------------------------------%
%%
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

letrec int_of_bin l v =
  (l = []) => v |
              (int_of_bin (tl l) (v + v + ((hd l = `0`)=> 0 | 1)));;
% ============================================================ %
% here is the stuff necessary for the major proof function     %
% below.  including:                                           %
%   - definitions of field selector functions from cu_types    %
%   - a base theorem for the forward proofs                    %
%   - a conversion for expanding word27 constants only         %
%   - function "clear" to strip redundancies from a list       %
% ============================================================ %
%%
%<
	NO LONGER USED IN THE PROOF !!!

let generic_prove_fcn (str,ty) thm =
  let tm = (snd o dest_comb o concl) thm
  and stem = (implode o tl o explode) str
  in
  let assum = mk_eq(tm,mk_const(str,ty))
  in 
  let simp = theorem `CU_wordn_proofs` (`word_`^stem)
  in 
  let th1 = SUBS [ASSUME assum] thm
  in
  save_thm
   ((((fst o dest_const o fst o dest_comb) tm)^`_`^stem),
    (DISCH_ALL o (prr [AND_CLAUSES;OR_CLAUSES;
		       COND_CLAUSES;NOT_CLAUSES])
	       o (SUBS (CONJUNCTS simp)))
	       (SUBS [BETA_CONV (concl th1)] th1));;
  
letrec proof_series n ty thm = 
  (n < 0) =>
     "T" |
     ((let len = (int_of_string o hd o tl o tl o tl o tl o
                 explode o fst o dest_type)ty
       in 
       generic_prove_fcn
        (implode(`#`.(mk_bit_list(n,len)([]:(string)list))),ty) thm) ;
       proof_series (n-1) ty thm);;

% ============================================================ %
% prove the whole lot of therorems about the various           %
% possible values for things.                                  %
% ============================================================ %

proof_series 12 ":word4" alus_base_lemma;;
proof_series 12 ":word4"
  (rr[SUBS [SPEC "SYS_Clocked:num->bool" clock_constraint]
           (ASSUME "clock_constraint SYS_Clocked")]
     state_base_lemma);;
proof_series 23 ":word5" reads_base_lemma;;
proof_series 17 ":word5" writes_base_lemma;;

>% 
% ============================================================ %
% This previous work has been supplanted by the need for       %
% tackling the cases at a higher level.  This is accomplished  %
% here by proving the values for subfields, in a form that     %
% will SUBST in the BASE_thm in SYS_proofs.ml.                 %
% ============================================================ %
let Alu_term_list =
 ["(Alu_field(ROM_fun(mpc (t:^mtime))) = #0001)";
  "(Alu_field(ROM_fun(mpc (t:^mtime))) = #0010)";
  "(Alu_field(ROM_fun(mpc (t:^mtime))) = #0011)";
  "(Alu_field(ROM_fun(mpc (t:^mtime))) = #0100)";
  "(Alu_field(ROM_fun(mpc (t:^mtime))) = #0101)";
  "(Alu_field(ROM_fun(mpc (t:^mtime))) = #0110)";
  "(Alu_field(ROM_fun(mpc (t:^mtime))) = #0111)";
  "(Alu_field(ROM_fun(mpc (t:^mtime))) = #1000)";
  "(Alu_field(ROM_fun(mpc (t:^mtime))) = #1001)";
  "(Alu_field(ROM_fun(mpc (t:^mtime))) = #1010)";
  "(Alu_field(ROM_fun(mpc (t:^mtime))) = #1011)";
  "(Alu_field(ROM_fun(mpc (t:^mtime))) = #1100)"];;

let Test_term_list =
 ["(Test_field(ROM_fun(mpc (t:^mtime))) = #0001)";
  "(Test_field(ROM_fun(mpc (t:^mtime))) = #0010)";
  "(Test_field(ROM_fun(mpc (t:^mtime))) = #0011)";
  "(Test_field(ROM_fun(mpc (t:^mtime))) = #0100)";
  "(Test_field(ROM_fun(mpc (t:^mtime))) = #0101)";
  "(Test_field(ROM_fun(mpc (t:^mtime))) = #0110)";
  "(Test_field(ROM_fun(mpc (t:^mtime))) = #0111)";
  "(Test_field(ROM_fun(mpc (t:^mtime))) = #1000)";
  "(Test_field(ROM_fun(mpc (t:^mtime))) = #1001)";
  "(Test_field(ROM_fun(mpc (t:^mtime))) = #1010)";
  "(Test_field(ROM_fun(mpc (t:^mtime))) = #1011)";
  "(Test_field(ROM_fun(mpc (t:^mtime))) = #1100)"];;

let Read_term_list =
 ["(Read_field(ROM_fun(mpc (t:^mtime))) = #00001)";
  "(Read_field(ROM_fun(mpc (t:^mtime))) = #00010)";
  "(Read_field(ROM_fun(mpc (t:^mtime))) = #00011)";
  "(Read_field(ROM_fun(mpc (t:^mtime))) = #00100)";
  "(Read_field(ROM_fun(mpc (t:^mtime))) = #00101)";
  "(Read_field(ROM_fun(mpc (t:^mtime))) = #00110)";
  "(Read_field(ROM_fun(mpc (t:^mtime))) = #00111)";
  "(Read_field(ROM_fun(mpc (t:^mtime))) = #01000)";
  "(Read_field(ROM_fun(mpc (t:^mtime))) = #01001)";
  "(Read_field(ROM_fun(mpc (t:^mtime))) = #01010)";
  "(Read_field(ROM_fun(mpc (t:^mtime))) = #01011)";
  "(Read_field(ROM_fun(mpc (t:^mtime))) = #01100)";
  "(Read_field(ROM_fun(mpc (t:^mtime))) = #01101)";
  "(Read_field(ROM_fun(mpc (t:^mtime))) = #01110)";
  "(Read_field(ROM_fun(mpc (t:^mtime))) = #01111)";
  "(Read_field(ROM_fun(mpc (t:^mtime))) = #10000)";
  "(Read_field(ROM_fun(mpc (t:^mtime))) = #10001)";
  "(Read_field(ROM_fun(mpc (t:^mtime))) = #10010)";
  "(Read_field(ROM_fun(mpc (t:^mtime))) = #10011)";
  "(Read_field(ROM_fun(mpc (t:^mtime))) = #10100)";
  "(Read_field(ROM_fun(mpc (t:^mtime))) = #10101)";
  "(Read_field(ROM_fun(mpc (t:^mtime))) = #10110)";
  "(Read_field(ROM_fun(mpc (t:^mtime))) = #10111)"
  ];;

let Write_term_list =
 ["(Write_field(ROM_fun(mpc (t:^mtime))) = #00001)";
  "(Write_field(ROM_fun(mpc (t:^mtime))) = #00010)";
  "(Write_field(ROM_fun(mpc (t:^mtime))) = #00011)";
  "(Write_field(ROM_fun(mpc (t:^mtime))) = #00100)";
  "(Write_field(ROM_fun(mpc (t:^mtime))) = #00101)";
  "(Write_field(ROM_fun(mpc (t:^mtime))) = #00110)";
  "(Write_field(ROM_fun(mpc (t:^mtime))) = #00111)";
  "(Write_field(ROM_fun(mpc (t:^mtime))) = #01000)";
  "(Write_field(ROM_fun(mpc (t:^mtime))) = #01001)";
  "(Write_field(ROM_fun(mpc (t:^mtime))) = #01010)";
  "(Write_field(ROM_fun(mpc (t:^mtime))) = #01011)";
  "(Write_field(ROM_fun(mpc (t:^mtime))) = #01100)";
  "(Write_field(ROM_fun(mpc (t:^mtime))) = #01101)";
  "(Write_field(ROM_fun(mpc (t:^mtime))) = #01110)";
  "(Write_field(ROM_fun(mpc (t:^mtime))) = #01111)";
  "(Write_field(ROM_fun(mpc (t:^mtime))) = #10000)";
  "(Write_field(ROM_fun(mpc (t:^mtime))) = #10001)"
 ];;

let sett marker assum term =
 SUBST [assum, marker]
 (mk_eq (term, mk_eq (marker, snd(dest_eq term))))
 (REFL term);;

let proof_fcn (term, ty, label) term_list = 
 let marker = genvar ty
 in
 let assum = ASSUME term
 in
 let num_str =
   ((implode o tl o explode o fst o dest_const o snd o dest_eq)term)
 in         
 let thm2 = theorem `CU_wordn_proofs` (`word_`^num_str)
 in
 save_thm
 (label^num_str,
  ( (DISCH term)
  o (SUBS (CONJUNCTS thm2))
  o LIST_CONJ
  o (map (sett marker assum))
  ) term_list);;


letrec proof_seq (n, (stem,ty,label,term_list))   =
 (n < 0)  =>
  "T" |
  ((let len = (int_of_string o hd o tl o tl o tl o tl o
               explode o fst o dest_type)ty
    in
    proof_fcn (mk_eq (stem,
		      (mk_const
		       (implode
			(`#`.(mk_bit_list(n,len)([]:(string)list))),
		       ty))),
	       ty,
	       label)
              term_list)
   ;
   proof_seq (n-1,(stem,ty,label,term_list)));;

map2 proof_seq
 ([12;12;23;17],
  ["Alu_field(ROM_fun(mpc (t:^mtime)))",   ":word4",
   `Alu_base_`,                            Alu_term_list;
   "Test_field(ROM_fun(mpc (t:^mtime)))",  ":word4",
   `Test_base_`,                           Test_term_list;
   "Read_field(ROM_fun(mpc (t:^mtime)))",  ":word5",
   `Read_base_`,                           Read_term_list;
   "Write_field(ROM_fun(mpc (t:^mtime)))", ":word5",
   `Write_base_`,                          Write_term_list
  ]);;

timer false;;
close_theory ();;
print_theory `-`;;
