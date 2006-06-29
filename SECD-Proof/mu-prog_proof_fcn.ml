% SECD verification                                                 %
%                                                                   %
% FILE:         mu-prog_proof_fcn.ml                                %
%                                                                   %
% DESCRIPTION:  This file is loaded for proving correctness         %
%                of all code sequences above subroutines.           %
%                                                                   %
% USES FILES:   constraints.th, mem_abs.th, when.th,                %
%               mu-prog_sr_proofs.th, phase_lemmas*.th,             %
%               mu-prog_init_proof.th (for mu-prog_proof_*.th)      %
%                                                                   %
% Brian Graham 90.02.21                                             %
%                                                                   %
% Modifications:                                                    %
% 90.02.26 - Adapted to the eliminition of SUC^n expressions to     %
%            also work with conditional branch sequences.           %
%                                                                   %
% ================================================================= %
loadf `wordn`;;

if (mem `mu-prog_level` (parents `-`))
then ()
else (new_parent `mu-prog_level`);;

if (current_theory() = `mu-prog_sr_proofs`)
then (fail())
else (new_parent `mu-prog_sr_proofs`;
      if (current_theory() = `mu-prog_init_proofs`)
      then (load_definition `rt_SECD` `Opcode`;
	    load_theorem `mu-prog_level` `Initial_range_thm`)
      else (new_parent `mu-prog_init_proofs`));;
% ================================================================= %
let mtime = ":num";;
let w14_mvec = ":^mtime->word14"
and w9_mvec = ":^mtime->word9"
and m14_32_mvec = ":^mtime->(word14->word32)";;
% ================================================================= %
map (load_definition `when`)
    [ `Next`
    ];;

map (load_definition `constraints`)
    [ `is_major_state`
    ];;

map (load_theorem `mu-prog_level`)
    [ `Next_step`
    ; `Next_interval`
    ; `join_branches_thm`
    ; `F_refld`
    ; `PRE_SUC`
    ];;

let free_list_conjuncts =
 CONJUNCTS (theorem `mu-prog_level` `free_list_thm`);;

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

% ================================================================= %
% Functions for managing the proof steps.                           %
%                                                                   %
%   word9_EQ_CONV - determines the (in)equality of any word         %
%                     constants                                     %
%                                                                   %
%   in_major_state - true if the word9 argument is a major state    %
%                                                                   %
%   prove_state_value - given a theorem of the form :               %
% 	|- (mpc (SUC^n t) = #010101010)                             %
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
%   find2 : * -> *list -> **list -> ** ->**                         %
%       returns the corresponding element from the 2nd list to      %
%       the position of the single element in the 1st list          %
%     example: #find2 2 [1; 2; 3; 4] [`a`; `b`; `c`; `d`] `e`;;     %
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

letrec find2 x xl yl err =
 (xl = []) => err |
              (x = hd xl) => hd yl |
                             find2 x (tl xl) (tl yl) err;;

% ================================================================= %
% This bit will be used to prove that we don't hit a major state in %
% the microcode addresses we get to.                                %
% ================================================================= %
% ================================================================= %
% proves a thm of the form: "t < SUC(SUC(SUC t))", for any number   %
% of applications of SUC.  For example:                             %
%     #prove_time_less "SUC(SUC(SUC t))";;                          %
%     |- t < (SUC(SUC(SUC t)))                                      %
% ================================================================= %
letrec prove_time_less time =
  let targ = (snd o dest_comb) time
  in
  ((is_comb targ)
   => MATCH_MP LESS_SUC (prove_time_less targ) 
    | (SPEC targ LESS_SUC_REFL));;

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
% We call up the theorem phase_lemma_(# that corresponds to #------)%
% and update the state of the system after executing that microcode %
% instruction, returning a theorem of the same form as thm1.        %
% The state of the mpc at that time will not be a major state,      %
% so we extend the 2nd theorem by raising the upper limit by one,   %
%                                                                   %
% Some adjustment was necessary when reaching a major state.        %
% The values of all the state and output values at the time the     %
% machine is in a major state are needed in the theorem, and not    %
% the next mpc state, etc.                                          %
% Additionally, the range that the temporal abstraction predicate   %
% is false cannot be extended, so instead we produce the definitive %
% statement giving the time when it "Next" holds.                   %
% ================================================================= %
let prove_next_step ptheory (thm1, thm2) =
 let mpc_t = CONJUNCT1 thm1
 in
 let nextA = (snd o dest_eq o concl) mpc_t
 in
 let n = int_of_word9 nextA
 in
 ((in_major_state nextA)
		% in a major state, so craft the final form of theorem %
		% note the theorem is always in `phase_lemmas1` %
  => let thm = theorem `phase_lemmas1` (`phase_lemma_`^(string_of_int n))
     in
     let hy = (fst o dest_imp o concl) thm
     in 
     let time = (snd o dest_comb o fst o dest_eq o concl) mpc_t
     in
     let new_state_thm = ((LIST_CONJ
                           o (filter(\th.
                            ((mem o fst o dest_comb o fst
                                  o dest_eq o concl) th)
                            [ "s:^w14_mvec"
			    ; "e:^w14_mvec"
			    ; "c:^w14_mvec"
			    ; "d:^w14_mvec"
			    ; "free:^w14_mvec"
			    ]))
                           o CONJUNCTS
                           o (porr[PRE_SUC]))
			   (MATCH_MP (((DISCH hy)
				      o LIST_CONJ
				      o tl o tl o tl o tl o tl o tl
				      o CONJUNCTS
				      o UNDISCH)
				      thm)
				    mpc_t))
     in
     let new_whole_conj = (SUBS (CONJUNCTS thm1) new_state_thm ?
                           porr (CONJUNCTS thm1) new_state_thm)
     in
     (LIST_CONJ
      (append
       (filter(\th.(is_forall (concl th))
                   or
		   (((mem o fst o dest_comb o fst o dest_eq o concl)
                     th)
		    [ "mpc:^w9_mvec" ; "memory:^m14_32_mvec"]))
	      (CONJUNCTS thm1))
       [ new_whole_conj ]),
      porr [SYM_RULE Next]
           (CONJ (prove_time_less time)
                 (CONJ (prove_state_value mpc_t) thm2)))

		% otherwise just do one step %
                % is the rewrite of COND_CLAUSES still needed? %
   | ((\th.((is_cond o snd o dest_eq o concl o CONJUNCT1)th)
           => (porr [COND_CLAUSES] th)
            | th)   % rewrite with the free constraint %
      (SUBS (CONJUNCTS thm1)
            (porr [PRE_SUC]
                  (MATCH_MP
		   (theorem ptheory 
			    (`phase_lemma_`^(string_of_int n)))
		   mpc_t))),
      MATCH_MP Next_step (CONJ (prove_state_value mpc_t) thm2)))
 ;;

% ================================================================= %
% The interval proof function is used for subroutines.              %
%                                                                   %
% Although the PreOperation subroutine doesn't need it, it is also  %
% supplied with a free list assumption, just for consistency        %
% in proof techniques.                                              %
% ================================================================= %
let prove_next_interval asm ((th1a,th1b),(th2a,th2b)) =
 let mpc_t = CONJUNCT1 th1a
 in
 let mpc_assum = "mpc (t:^mtime) = ^((snd o dest_eq o concl) mpc_t)"
 in
 let thm =
     (porr[PRE_SUC]	% CONJ together & do once only %
	  (MATCH_MP (( (DISCH mpc_assum)
                     o (DISCH asm)
		     )
		     (CONJ th2a th2b)) mpc_t))
 in
 let thmA = 
 (( (porr[IMP_CLAUSES])
  o (SUBS [F_refld])
  o (porr free_list_conjuncts)
  o (SUBS (CONJUNCTS th1a))
  ) thm)
 in
 (CONJUNCT1 thmA,
  MATCH_MP Next_interval
           (CONJ th1b (CONJUNCT2 thmA)))
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

letrec recursive f arg =
  let nextA = (snd o dest_eq o concl o CONJUNCT1 o fst) arg
  in
  (is_const nextA) 		% if a simple address %
  => (mem nextA [Consx1x2;Numberbuf;PreOperation;PostOperation])
				% if a subroutine call %
     => (let stem =
         find2 nextA
           [Consx1x2;Numberbuf;PreOperation;PostOperation]
           [`Consx1x2`;`Numberbuf`;`PreOperation`;`PostOperation`]
           `not a subroutine`
         in
         let thms = (theorem `mu-prog_sr_proofs` (stem^`_state`),
                     theorem `mu-prog_sr_proofs` (stem^`_nonmajor`))
         in
	(tty_write(fst(dest_const nextA)^`: `^stem^`
`)
         ; recursive f (prove_next_interval asm (arg, thms))))
     |  (in_major_state nextA)  % else if major state reached %
        => (tty_write(fst(dest_const nextA)^`: `^
			 (find2 nextA
           ["#000010110";"#00101011";"#000101011"]
           [`idle`;`top_of_cycle`;`error0`;`error1`]
	   `not a major state`)^`
`)
           ; f arg)		% we need only one more step %
                                % else carry on ... %
        |  (tty_write(fst(dest_const nextA)^`: step
`)
           ; recursive f (f arg))
				% else if it is a branch %
  |  (is_cond nextA) 
     => let cond = (fst o dest_cond ) nextA
        in
        let condt = mk_eq (cond, "T")
        and condf = mk_eq (cond, "F")
        in
        let th1,th2 = arg
        in			% prove thm pairs for each branch %
        let t1a,t1b =
         (tty_write(fst(dest_const(fst(snd(dest_cond nextA))))^`: branch 1
`)
         ; recursive f (prr[ASSUME condt; COND_CLAUSES] th1,
		      ADD_ASSUM condt th2))
        and t2a,t2b =
         (tty_write(fst(dest_const(snd(snd(dest_cond nextA))))^`: branch 2
`)
         ; recursive f (prr[ASSUME condf; COND_CLAUSES] th1,
		      ADD_ASSUM condf th2))
        in			% combine the branch thms %
        (porr[join_branches_thm]
             (CONJ (DISCH condt t1a)(DISCH condf t2a)),
	 porr[join_branches_thm]
             (CONJ (DISCH condt t1b)(DISCH condf t2b)))
				% unsolvable (in this series) next step %
     |  (tty_write(`return from subroutine
`)
         ; arg);;

% ================================================================= %
% This function is used to prove instruction sequences aside from   %
% subroutines.  It is useful in proving the longer sequences, which %
% cause static structure limit errors (AP, RAP, and likely LD).     %
% It is designed to prove the sequences between subroutine calls.   %
% ================================================================= %
letrec stepper f arg =
  let nextA = (snd o dest_eq o concl o CONJUNCT1 o fst) arg
  in
  (is_const nextA) 		% if a simple address %
  => (mem nextA [Consx1x2;Numberbuf;PreOperation;PostOperation])
				% if a subroutine call %
     => (let stem =
         find2 nextA
           [Consx1x2;Numberbuf;PreOperation;PostOperation]
           [`Consx1x2`;`Numberbuf`;`PreOperation`;`PostOperation`]
           `not a subroutine`
         in
        (tty_write(fst(dest_const nextA)^`: `^stem^`
`)
        ; arg))
     |  (in_major_state nextA)  % else if major state reached %
        => (tty_write(fst(dest_const nextA)^`: top_of_cycle
`)
           ; arg)		% we leave last step 'til later %
                                % else carry on ... %
        |  (tty_write(fst(dest_const nextA)^`: step
`)
           ; stepper f (f arg))
				% else if it is a branch %
  |  (is_cond nextA) 
     => let cond = (fst o dest_cond ) nextA
        in
        let condt = mk_eq (cond, "T")
        and condf = mk_eq (cond, "F")
        in
        let th1,th2 = arg
        in			% prove thm pairs for each branch %
        let t1a,t1b =
         (tty_write(fst(dest_const(fst(snd(dest_cond nextA))))^`: branch 1
`)
         ; stepper f (prr[ASSUME condt; COND_CLAUSES] th1,
		      ADD_ASSUM condt th2))
        and t2a,t2b =
         (tty_write(fst(dest_const(snd(snd(dest_cond nextA))))^`: branch 2
`)
         ; stepper f (prr[ASSUME condf; COND_CLAUSES] th1,
		      ADD_ASSUM condf th2))
        in			% combine the branch thms %
        (porr[join_branches_thm]
             (CONJ (DISCH condt t1a)(DISCH condf t2a)),
	 porr[join_branches_thm]
             (CONJ (DISCH condt t1b)(DISCH condf t2b)))
				% unsolvable (in this series) next step %
     |  (tty_write(`return from subroutine
`)
         ; arg);;

% ================================================================= %
% The top level subroutine proof function has a pair of theorems    %
% and a pair of strings as arguments.  We want 2 theorems for each  %
% subroutine.                                                       %
% One will define the state of the machine after executing the      %
% microcode sequence, the other will state that we are never in a   %
% major state in the sequence.                                      %
% These results will compose with other results to prove            %
% instruction code sequences correct, and define when we get to     %
% the Next major state.                                             %
% The initial pair of theorems given as arguments are an assumption %
% of the mpc value at tiem t, CONJ'ed to either an assumption about %
% the value of "free (PRE t)", or simply TRUTH.  The second theorem %
% is the starting lemma, that the temporal abstraction predicate is %
% false for all values in an empty interval.                        %
% ================================================================= %
% ***************************************************************** %
% Getting rid of SUC^n                                              %
% ***************************************************************** %
letrec num_of_SUC tm =
  (is_comb tm) => 1 + (num_of_SUC ((snd o dest_comb) tm))
  	        | 0;;

let MK_t_plus_num_THM n =
 SYM (porr[porr[ADD_SYM](CONJUNCT1 ADD)]
          (prr[porr[ADD_SYM](CONJUNCT2 ADD)]
	      (REDEPTH_CONV num_CONV
			    "t + ^(mk_const(string_of_int n,":num"))")));;

let reformat th1 th2 =
 SUBS (let mpc_conjunct = CONJUNCT1 th1
       in
       let n = ((num_of_SUC o snd o dest_comb o fst o dest_eq
                            o concl)mpc_conjunct)
       in
       let num_l = MK_t_plus_num_THM n
       in
       let pre_l = porr[PRE_SUC](AP_TERM "PRE" num_l)
       in
       [num_l; pre_l])
       (CONJ th1 th2);;

% ================================================================= %
% The top level function uses the above functions to produce a      %
% time parameter in the form "t+n" (instead of "SUC^n t").          %
% It can deal with linear sequences or single branches.             %
%                                                                   %
% The order of substitutions may be significant, if, for example,   %
% we have 2 terms : "SUC t" and "SUC (SUC (SUC t))".  The first     %
% may use part of what the 2nd one should use.                      %
% ================================================================= %
let save_seq_proof ptheory arg (n1,n2) =
 let (th1,th2) = recursive (prove_next_step ptheory) arg
 in
 let tm = concl th2
 in
 let tmlist = (is_cond tm)
              => (\t.[fst t; snd t]) (snd (dest_cond tm)) | [tm]
 in
 let thmlist = map (MK_t_plus_num_THM o num_of_SUC o hd o tl
				      o snd o strip_comb) tmlist
 in
 (save_thm (n1, SUBS thmlist th1),
  save_thm (n2, SUBS thmlist th2))
 ;;

timer true;;
