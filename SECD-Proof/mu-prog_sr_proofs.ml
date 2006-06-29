% SECD verification                                                 %
%                                                                   %
% FILE:         mu-prog_sr_proofs.ml                                %
%                                                                   %
% DESCRIPTION:  This proves the correctness of the subroutines.     %
%                                                                   %
% USES FILES:   constraints.th, mem_abs.th, when.th                 %
%               phase_lemmas7.th                                    %
%                                                                   %
% Brian Graham 89.12.05                                             %
%                                                                   %
% Modifications:                                                    %
%                                                                   %
% ================================================================= %
new_theory `mu-prog_sr_proofs`;;

loadf `wordn`;;
% load_library `unwind`;; %

map new_parent [ `mem_abs`
               ; `when`
               ; `phase_lemmas7`
               ];;
map (load_definition `constraints`)
    [ `is_major_state`
    ];;

% load_library `eval`;;				 for "seg" function %
% no longer needed ?????????????? %
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
% Constraints:                                                      %
% ================================================================= %
let clock_constraint = "clock_constraint SYS_Clocked";;

timer true;;
% ================================================================= %
% First a series of ml functions for use in managing the proof.     %
% Most of this consists of deriving a number from a word9 constant, %
% and vice versal                                                   %
% ================================================================= %
% ================================================================= %
% functions:                                                        %
%                                                                   %
%   mk_bit_list (num,size) res                                      %
%       returns a list of strings of 1's and 0's,                   %
%       of length size.                                             %
%     example : #mk_bit_list (3,4)[];;                              %
%               [`0`; `0`; `1`; `1`] : string list                  %
%                                                                   %
%   mk_word9_from_num n                                             %
%       returns a word9 constant corresponding to n                 %
%     example : #mk_word9_from_num 17;;                             %
%               "#000010001" : term                                 %
%                                                                   %
%   int_of_word9 w                                                  %
%       returns the integer equivalent of the word9 constant        %
%     example : #int_of_word9 "#000100010";;                        %
%               34 : int                                            %
%                                                                   %
% ================================================================= %
let rem (x,y) = x - y * (x / y);;

letrec mk_bit_list (num, size) res =
   (size = 0) => res |
                 (mk_bit_list ((num/2), (size-1)) 
                   (((string_of_int o rem) (num,2)) . res));;

let mk_word9_from_num n =
	mk_const
           (implode (`#` . (mk_bit_list (n,9) ([]:(string)list))),
           ":word9");;

letrec int_of_bin_list l ttl =
  l = [] => ttl | int_of_bin_list (tl l)(ttl + ttl + (hd l));;

let int_of_word9 w =
  int_of_bin_list (map int_of_string ((tl o explode o fst o dest_const)w)) 0;;

%%
% ================================================================= %
% Functions for managing the proof steps.                           %
%                                                                   %
%   word9_EQ_CONV - determines the (in)equality of any word         %
%                     constants                                     %
%                                                                   %
%   in_major_state - true if the word9 argument is a major state    %
%                                                                   %
%   prove_state_value - given a theorem of the form :               %
% 	|- (mpc (SUC^n t) = #010101010) /\                          %
%          .....                                                    %
%                         it determines if the mpc at the given     %
%                         time is a major state or not, returning   %
%                         a theorem of the form:                    %
% 	|- ~(is_major_state mpc (SUC^n t))                          %
%                         or:                                       %
% 	|- is_major_state mpc (SUC^n t)                             %
%                                                                   %
%   Consx1x2,Numberbuf,PreOperation,PostOperation =                 %
%   ("#101000101", "#101001011", "#100110101", "#100111110")        %
%                                                                   %
%   find2 : * -> *list -> **list -> **                              %
%       returns the corresponding element from the 2nd list to      %
%       the position of the single element in the 1st list          %
%     example: #find2 2 [1; 2; 3; 4] [`a`; `b`; `c`; `d`];;         %
%              `b` : string                                         %
% ================================================================= %
let word9_EQ_CONV = wordn_EQ_CONV (theorem `cu_types` `Word9_11`);;

let in_major_state v =
  mem v [ "#000010110"; "#000011000"; "#000101011"; "#000011010"];;

let prove_state_value lem =
  let mpct,v = (dest_eq o concl)lem
  in
  let thm =
    porr[lem]
    (SPECL ((\x.[fst x; snd x]) (dest_comb mpct)) is_major_state)
  in
  if (in_major_state v)
  then (rr[] thm)
  else ((rr[] o in1_conv_rule word9_EQ_CONV) thm);;

let [Consx1x2;Numberbuf;PreOperation;PostOperation] = 
   (map mk_word9_from_num [325;331;309;318]);;

letrec find2 x xl yl =
 (xl = []) => hd yl |
              (x = hd xl) => hd yl |
                             find2 x (tl xl) (tl yl);;

% ================================================================= %
% This bit will be used to prove that we don't hit a major state in %
% the microcode addresses we get to.                                %
% ================================================================= %
% ================================================================= %
% Next_step =                                                       %
% |- !ts tf f.                                                      %
%     ~f tf /\ (!t. ts < t /\ t < tf ==> ~f t) ==>                  %
%     (!t. ts < t /\ t < (SUC tf) ==> ~f t)                         %
% ================================================================= %
let Next_step = TAC_PROOF
(([], "! (ts tf:num) f.
          (~(f tf) /\
           !t. (ts < t) /\ (t < tf) ==> ~(f t)) ==>
          (!t. (ts < t) /\ (t < (SUC tf)) ==> ~(f t))"),
 REPEAT GEN_TAC
 THEN STRIP_TAC
 THEN GEN_TAC
 THEN port[LESS_THM]
 THEN STRIP_TAC
 THENL
 [ art[]
 ; RES_TAC
 ]);;

% ================================================================= %
% Next_interval =                                                   %
% |- !ts tm tf f.                                                   %
%     (!t. ts < t /\ t < (SUC tm) ==> ~f t) /\                      %
%     (!t. tm < t /\ t < tf ==> ~f t) ==>                           %
%     (!t. ts < t /\ t < tf ==> ~f t)                               %
% ================================================================= %
let Next_interval = TAC_PROOF
(([], "!ts tm tf f.
    (!t. ts < t /\ t < (SUC tm) ==> ~f t) /\
    (!t. tm < t /\ t < tf ==> ~f t) ==>
    (!t. ts < t /\ t < tf ==> ~f t)"),
 REPEAT GEN_TAC
 THEN STRIP_TAC
 THEN GEN_TAC
 THEN STRIP_TAC
 THEN ASM_CASES_TAC "t < (SUC tm)"
 THENL [ALL_TAC; IMP_RES_TAC (porr[SYM_RULE NOT_LESS]OR_LESS)]
 THEN RES_TAC);;

% ================================================================= %
% Empty_range =                                                     %
% |- !t t'. ~((PRE t') < t /\ t < t')                               %
%                                                                   %
% Reproduces a theorem in mu-prog_level.th, but due to hierarchy ...%
% ================================================================= %
let Empty_range = prove
("! t t'. ~(PRE t' < t /\ t < t')",
 GEN_TAC
 THEN INDUCT_TAC
 THEN prt [PRE]
 THENL
 [ rt[LESS_ANTISYM]
 ; STRIP_TAC
   THEN IMP_RES_THEN
      (DISJ_CASES_THENL
       ([ \th. SUBST_ALL_TAC th THEN IMP_RES_TAC LESS_REFL
        ; \th. ASSUME_TAC th THEN IMP_RES_TAC LESS_ANTISYM]))
	  ((fst o EQ_IMP_RULE o SPEC_ALL) LESS_THM)
 ]);;

% ================================================================= %
% Start_lem :                                                       %
% |- !t' f t. (PRE t') < t /\ t < t' ==> ~f t                       %
% ================================================================= %
let Start_lem = TAC_PROOF
(([], "! t' f t. (PRE t' < t) /\ (t < t') ==> ~(f t)"),
 rt[Empty_range]
 );;

% ================================================================= %
% snd_thm :                                                         %
% |- !t''. (PRE t) < t'' /\ t'' < t ==> ~is_major_state mpc t''     %
% ================================================================= %
let snd_thm = SPECL ["t:^mtime"; "is_major_state mpc"] Start_lem;;

% ================================================================= %
% This function does the proof for each microcode step.  2 theorems %
% are supplied as arguments:                                        %
% - thm1 is of the form:                                            %
%    .... |- (mpc (SUC^n t) = #---------) /\ ...                    %
% - thm2 is of the form:                                            %
%    .... |- !t'.                                                   %
%           (PRE t) < t' /\ t' < (SUC^n t) ==>                      %
% 	  ~is_major_state mpc t')                                   %
%                                                                   %
% We call up the theorem phase_lemma_(# that corresponds to #--------)%
% and update the state of the system after executing that microcode %
% instruction, returning a theorem of the same form as thm1.        %
% The state of the mpc at that time will not be a major state,      %
% so we extend the 2nd theorem by raising the upper limit by one.   %
% ================================================================= %
let prove_next_step ptheory (thm1, thm2) =
 let mpc_t = CONJUNCT1 thm1
 in
 let n = int_of_word9 ((snd o dest_eq o concl) mpc_t)
 in		% get rid of conditional on mpc %
 ((\th. ((is_cond o snd o dest_eq o concl o CONJUNCT1)th) =>
     (porr [COND_CLAUSES] th) | th)
  (porr (CONJUNCTS thm1)
    (porr [CONJUNCT2 PRE]
      (MATCH_MP
        (theorem ptheory (`phase_lemma_`^(string_of_int n)))
        mpc_t))),
 MATCH_MP Next_step (CONJ (prove_state_value mpc_t) thm2))
;;

% ================================================================= %
% Two versions of the interval proof function are provided.         %
% The first is used when an assumption about the free list must     %
% be discharged and specialized.  The second (primed (') version)   %
% us used when there is no free list assumption.                    %
% ================================================================= %
let prove_next_interval asm ((th1a,th1b),(th2a,th2b)) =
 let mpc_t = CONJUNCT1 th1a
 in
 let mpc_assum = "mpc (t:^mtime) = ^((snd o dest_eq o concl) mpc_t)"
 in
 let thmA,thmB =
  (UNDISCH
   (porr(CONJUNCTS th1a)
	(porr[CONJUNCT2 PRE]
			(MATCH_MP
			 (( (DISCH mpc_assum)
			    o (DISCH asm)
			    )
			  th2a) mpc_t))),
   UNDISCH
   (porr(CONJUNCTS th1a)
	(porr[CONJUNCT2 PRE]
			(MATCH_MP
			 (( (DISCH mpc_assum)
			    o (DISCH asm)
			    )
			  th2b) mpc_t))))
 in
 (thmA,
  MATCH_MP Next_interval (CONJ th1b thmB))
 ;;

% ================================================================= %
% This is just a wrapper for the proof function, to effect          %
% recursive calls of it.                                            %
% It has grown in scope since the original version of the called    %
% proof step function, so that it no longer needs explicit numeric  %
% parameters.  It determines what theorems to call based on the     %
% value of the mpc in the current theorem argument.  It also        %
% determines when to call an interval proof function for subroutine %
% calls, and stops when it comes to the end of the subroutine.      %
% A slight modification to this should work on code sequences, by   %
% simply adding a check for being in a major state (this is likely  %
% not even necessary, since it will recognize that it does not have %
% a simple expression for the next mpc value).                      %
% It might also need a quick look at the front end, if the fact that%
% it starts in a major state has any side effects on the proof.     %
% ================================================================= %
let asm = "(free(PRE t) = NIL_addr) = F";;
let ptheory = `phase_lemmas7`;;

letrec recursive f arg =
  let mpc_t = (concl o CONJUNCT1 o fst) arg
  in
  let nextA = ((snd o dest_eq) mpc_t)
  in
  (is_const nextA)
  => (mem nextA [Consx1x2;Numberbuf;PreOperation;PostOperation])
     => ((is_var o snd o dest_comb o fst o dest_eq) mpc_t)
        => recursive f (f arg)
         | (let stem =
            find2 nextA
                  [Consx1x2;Numberbuf;PreOperation;PostOperation]
                  [`Consx1x2`;`Numberbuf`;`PreOperation`;`PostOperation`]
            in
            let thms = (theorem `mu-prog_sr_proofs` (stem^`_state`),
                        theorem `mu-prog_sr_proofs` (stem^`_nonmajor`))
            in
            recursive f (prove_next_interval asm (arg, thms)))
      | recursive f (f arg)
   | arg;;

let save_seq_proof thms_arg (n1,n2) =
 let (th1,th2) = recursive (prove_next_step ptheory) (thms_arg)
 in
 (save_thm (n1, th1),
  save_thm (n2, th2))
 ;;


% ***************************************************************** %
% Now, start by proving the subroutines.  The first are simple:     %
%   Consx1x2, Numberbuf, and PreOperation.                          %
% PostOperation is typical of most code segments, in that it        %
% has a subroutine call within it.  It will be the prototype for    %
% developing proof functions for proving all instruction sequences. %
%                                                                   %
% An unnecessary free list assumption is added to the PreOperation  %
% proof.  It arose originally as an error, but was kept for         %
% consistency of all subroutines, and their proofs.                 %
%                                                                   %
% It is harmless, as the assumption will have to be introduced      %
% eventually every time the PreOperation subroutine is called.      %
% ***************************************************************** %
let Consx1x2_state,Consx1x2_nonmajor =
 save_seq_proof
   (CONJ (ASSUME "(mpc (t:^mtime)) = ^(mk_word9_from_num 325)")
         (ASSUME "(free (PRE t) = NIL_addr) = F"),
    snd_thm)
   (`Consx1x2_state`,`Consx1x2_nonmajor`)
 ;;

let Numberbuf_state,Numberbuf_nonmajor =
 save_seq_proof
   (CONJ (ASSUME "(mpc (t:^mtime)) = ^(mk_word9_from_num 331)")
         (ASSUME "(free (PRE t) = NIL_addr) = F"),
    snd_thm)
   (`Numberbuf_state`,`Numberbuf_nonmajor`)
 ;;

let PreOperation_state,PreOperation_nonmajor =
 save_seq_proof
   (CONJ (ASSUME "(mpc (t:^mtime)) = ^(mk_word9_from_num 309)")
         (ASSUME "(free (PRE t) = NIL_addr) = F"),
    snd_thm)
   (`PreOperation_state`,`PreOperation_nonmajor`)
 ;;

let PostOperation_state,PostOperation_nonmajor =
 save_seq_proof
   (CONJ (ASSUME "(mpc (t:^mtime)) = ^(mk_word9_from_num 318)")
         (ASSUME "(free (PRE t) = NIL_addr) = F"),
    snd_thm)
   (`PostOperation_state`,`PostOperation_nonmajor`)
 ;;

timer false;;
close_theory ();;
print_theory `-`;;
