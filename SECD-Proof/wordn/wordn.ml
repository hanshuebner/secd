% FILE		: wordn.ml						%
% DESCRIPTION   : wordn type definition package.			%
%									%
% READS FILES	: wordn.th						%
% WRITES FILES  : <none>						%
%									%
% AUTHOR	: (c) T. Melham						%
% DATE		: 87.09.23						%
% 									%
% NOTE		: PRELIMINARY RELEASE. Please do not distribute.	%
%                 (This was cleared with T. Melham for use with the     %
%                  SECD proof example distribution. - BtG)              %
%                                                                       %
% REVISIONS	: 09.04.91 - BtG - made compatible with Version 1.12.	%
%                                  loadx & HOLdir                       %
%                                  EXISTS_IMP_FORALL_CONV               %
%                                  tok_of_int                           %
%                                  BOOL_EQ_CONV                         %
%                                  define_new_type_bijections           %
%                                  misc. other fixes...                 %

if draft_mode() 
 then (print_newline();
       print_string`wordn declared a new parent`;
       print_newline();
       new_parent`wordn`)
 else load_theory`wordn`;;

load (`bus`, get_flag_value `print_lib`);;

% Fetch theorems from wordn.th						%
let wordn_DEF_THM = theorem `wordn` `wordn_DEF_THM` 
and exists_wordn_rep = theorem `wordn` `exists_wordn_rep`;;

% Fetch theorems from bus.						%
let Width_Wire = theorem `bus` `Width_Wire`
and Width_Bus = theorem `bus` `Width_Bus`
and Hd_bus = INST_TYPE [":bool",":*"]  (definition `bus` `Hd_bus`) 
and Tl_bus =  INST_TYPE [":bool",":*"] (definition `bus` `Tl_bus`);;


% ---------------------------------------------------------------------	%
% procedures for cleaning up the type axiom (wordn_DEF_THM).		%
% --------------------------------------------------------------------- %

% BINDER_CONV conv "B x. tm[x]" applies conv to tm[x]			%
let BINDER_CONV conv =  (RAND_CONV (ABS_CONV conv));;

% LHS_CONV conv "OP t1 t2" applies conv to t1				%
let LHS_CONV = RATOR_CONV o RAND_CONV ;;

% DEPTH_FORALL_CONV : BINDER_CONV in depth				%
letrec DEPTH_FORALL_CONV conv tm = 
       if (is_forall tm) then
          BINDER_CONV (DEPTH_FORALL_CONV conv) tm else
	  conv tm;;

% ---------------------------------------------------------------------	%
% The following code is for ELIM_WID_CONV.  I wish this conversion was	%
% much faster and simpler, but this will have to do for now...		%
% ---------------------------------------------------------------------	%

% A couple of lemmas.							%
let Wid_Wire  = INST_TYPE [":bool",":*"] Width_Wire and
    Wid_Bus = INST_TYPE [":bool",":*"] Width_Bus;;

% Complicated rule for use in LEN_SIMP_CONV below			%
letrec CHOOSE_RULE th1 th2 = 
       if (not(is_exists (concl th1))) then SUBS [th1] th2 else
       let (v,body) = dest_exists (concl th1) in
       let var = genvar (type_of v) in
       let tm = subst [var,v] body in
       let thm1 = CHOOSE_RULE (ASSUME tm) th2 in
       let thm2 = EXISTS(mk_exists(var,concl thm1),var) thm1 in
           CHOOSE (var,th1)thm2;;

% Also complicated....							%
letrec EXISTS_RULE evars th = 
       if (null evars) then th else
       let ev = hd(evars) in
       let evar = genvar (type_of ev) in
       let epat = mk_exists(evar,subst_occs [[2]] [evar,ev] (concl th)) in
       let th' = EXISTS (epat,ev) th in
           EXISTS_RULE (tl evars) th';;

% Complicated... used in LEN_SIMP_CONV below...				%
letrec DO_ASM th asm = 
   if (not(is_exists (concl asm))) then 
      let wit = (lhs(snd(strip_exists (concl th)))) in
      let var = genvar (type_of wit) in
      let subs = 
         if (is_const wit) then
	     subst_occs [[1;3]] [var,wit] else
	     subst [var,wit] in
     let epat = 
	 mk_exists (var,subs (mk_conj(concl th,concl asm))) in
       EXISTS (epat,wit) (CONJ th asm) else
    let (v,body) = dest_exists (concl asm) in
    let thm1 = DO_ASM th (ASSUME body) in CHOOSE (v,asm)thm1;;

% WID_SIMP_CONV : "?l.  (?a1..an. l = tm[a1...an]) /\ tm2[l]"		%
%									%
% ---> "?a1...an. tm2[tm[a1...an]]"					%
let WID_SIMP_CONV tm = 
    let th1,th2 = CONJ_PAIR (ASSUME (snd(dest_exists tm))) in
    let th3 = CHOOSE_RULE th1 th2 in
    let imp1 = DISCH tm (CHOOSE ((fst(dest_exists tm)),(ASSUME tm)) th3) in
    let res = snd(dest_imp(concl imp1)) in
    let asm = ASSUME res in
    let th4 = REFL (rand(rhs(snd(strip_exists res)))) in
    let evars = rev(fst(strip_exists res)) in
    let th5 = EXISTS_RULE evars th4 in
    let imp2 = DISCH res (DO_ASM th5 asm) in
    IMP_ANTISYM_RULE imp1 imp2;;

% ELIM_WID_CONV : Length l = SUC(SUC(SUC 0)) --> ?a b c. l = [a;b;c]	%
letrec ELIM_WID_CONV tm = 
       let bus = rand(lhs tm) and wid = rhs tm in
       if (wid = "SUC 0") then TRANS (REFL tm) (SPEC bus (Wid_Wire)) else
       let thm1 = SPECL [bus;(rand (rand wid))] Wid_Bus in
       let conv1 = 
	  (RAND_CONV(BINDER_CONV(BINDER_CONV(LHS_CONV ELIM_WID_CONV)))) in
       let conv2 = (RAND_CONV(BINDER_CONV WID_SIMP_CONV)) in
       CONV_RULE (conv1 THENC conv2) thm1;;

% Eliminate all "Width bus = SUC(SUC 0)" terms in favour of		%
% ?a b.bus = Bus a (Wire b).. etc					%
let RM_WID_CONV = 
    BINDER_CONV(BINDER_CONV(BINDER_CONV(LHS_CONV ELIM_WID_CONV)));;

% iterated version of EXISTS_IMP_FORALL_CONV				%
letrec E_I_CONV tm =
       if (is_exists(fst(dest_imp tm))) then
          (LEFT_IMP_EXISTS_CONV THENC (BINDER_CONV E_I_CONV)) tm else
          REFL tm;;

% !x b c. x = tm ==> t[x,a,b,c]    =    t[tm,a,b,c]			%
let EQ_ANTE_ELIM tm = 
    let vars,body = strip_forall tm in
    let x,t = dest_eq(fst(dest_imp body)) in
    let specl = map (\tm. if (tm=x) then t else tm) vars in
    let genl = filter (\tm. not(tm = x)) vars in
    let imp1 = DISCH tm (GENL genl (MP (SPECL specl (ASSUME tm)) (REFL t))) in
    let asm1 = (SPECL genl (ASSUME (snd(dest_imp(concl imp1))))) in
    let th = (DISCH "^x = ^t" (SUBS [SYM(ASSUME "^x = ^t")] asm1)) in
    let imp2 = DISCH_ALL (GENL vars th) in
    IMP_ANTISYM_RULE imp1 imp2;;

% Extract components of a bus						%
letrec extract_bus var tm = 
       if (fst(dest_comb tm) = "Wire:bool->(bool)bus") then 
           ["Hd_bus ^var:bool"] else
       let Bus,[b;bus] = strip_comb tm in
       "Hd_bus ^var:bool". extract_bus "Tl_bus ^var:(bool)bus" bus;;

% Make the function for specialization.					%
let spec_fn n thm = 
    let (f,body) = (I # (snd o dest_abs o rand)) (dest_forall(concl thm)) in
    let bus = rand(rhs(snd(strip_forall body))) and
        var = genvar ":(bool)bus" in
    let argsl = extract_bus var bus in
    letrec mk_f_ty n = if (n=0) then ":*" else
			  mk_type(`fun`,[":bool";mk_f_ty (n-1)]) in
    let name = mk_primed_var(`f`,mk_f_ty n) in
    let fspec = mk_abs(var,list_mk_comb (name,argsl)) in
    let thm1 = SPEC fspec thm in
    CONV_RULE (BINDER_CONV(DEPTH_FORALL_CONV(RAND_CONV BETA_CONV))) thm1;;

% HD_TL_SIMP = rewrite with Hd and Tl, 					%
% only works on Hd(Tl(Tl(Tl ... (Cons a (Cons ...))			%
letrec HD_TL_SIMP tm = 
       let op1,op2,val = (I # dest_comb) (dest_comb tm) in
       let on1 = fst(dest_const op1) and
           on2 = if (is_const op2) then 
		    fst(dest_const op2) else 
		    fst(dest_const (rator op2)) in
       (if (on1 = `Hd_bus` & on2 = `Bus`) then
             REWR_CONV (CONJUNCT2 Hd_bus) tm else
	if (on1 = `Hd_bus` & on2 = `Wire`) then
             REWR_CONV (CONJUNCT1 Hd_bus) tm else
        if (on1 = `Tl_bus` & on2 = `Bus`) then 
	    REWR_CONV Tl_bus tm else
	if (on1 = `Hd_bus` or on1 = `Tl_bus`) then
   	   ((RAND_CONV HD_TL_SIMP) THENC HD_TL_SIMP) tm else fail);;

% Simplify a rhs of the form f t1 t2 t3..				%
letrec SIMP_RHS tm = 
       if (is_var tm) then REFL tm else
       MK_COMB(SIMP_RHS (rator tm), HD_TL_SIMP (rand tm));;

let sub_conv conv tm =
    let rator,bv,body = (I # dest_abs) (dest_comb tm) in
    MK_COMB(REFL rator,MK_ABS(GEN bv (conv body))) ;;

letrec list_gen_alpha l = 
       if (null l) then ALL_CONV else
       GEN_ALPHA_CONV (hd l) THENC (sub_conv (list_gen_alpha (tl l)));;

let cleanup tm = 
    let vars,body = (strip_forall tm) in
    letrec mk_new_vars n l = 
           if (null l) then [] else
              (mk_primed_var(`b`^(string_of_int n), ":bool").
			     mk_new_vars  (n+1) (tl l)) in
    let newvars = mk_new_vars 0 vars in
    list_gen_alpha newvars tm;;

% ---------------------------------------------------------------------	%
% Now, the main program							%
% ---------------------------------------------------------------------	%

% define_wordn_type: construct and axiomatize a new type of n-bit words	%
%		     for given n.					%
%									%
% E.g. define_wordn_type 3  --> defines:				%
%									%
%	1) a type :word3						%
%	2) a constant  Word3:(bool)bus->word3				%
%									%
% and proves that word3 has the following axiom:			%
%									%
%	|- !f. ?!fn. !b0 b1 b2. fn(Word3 [b0;b1;b2] = f b0 b1 b2	%
%									%
% the axiom is stored under the name `Word3` and is returned.		%
%									%
% For convenience, some extra theorems are also returned.  These follow %
% from the axiom, but for speed are here proved from the type definition%

let define_wordn_type n = 
    if n<1 then fail else
    letrec mk_n_tm n = if (n=0) then "0" else "SUC ^(mk_n_tm (n-1))" in
    let e_th = SPEC (mk_n_tm (n-1)) exists_wordn_rep in
    let name = `word` ^ (string_of_int n) in
    let ty_ax = (new_type_definition 
		(name, rator(snd(dest_exists(concl e_th))), e_th)) in
    let ty_ISO_DEF = define_new_type_bijections
           (name^`_ISO_DEF`) (`ABS_`^name) (`REP_`^name) ty_ax in
    let [A_R; R_A] = CONJUNCTS ty_ISO_DEF in
    let [R_11; R_ONTO; A_11; A_ONTO] =
        map (\f. f ty_ISO_DEF)
            [prove_rep_fn_one_one; prove_rep_fn_onto;
             prove_abs_fn_one_one; prove_abs_fn_onto] in
    let th_inst = INST_TYPE [":*",":**";mk_type (name,[]), ":*"] 
			    wordn_DEF_THM in
    let A,R = (I # rator) (dest_comb(lhs(snd(dest_forall(concl A_R))))) in
    let th_concl = LIST_MP [A_ONTO;R_A] (SPECL [mk_n_tm (n-1);A;R] th_inst) in
    let thm1 = CONV_RULE RM_WID_CONV th_concl in
    let thm2 = CONV_RULE 
	       (BINDER_CONV (BINDER_CONV (BINDER_CONV E_I_CONV))) thm1 in
    let thm3 = CONV_RULE (BINDER_CONV(BINDER_CONV EQ_ANTE_ELIM)) thm2 in
    let wordn_name = `Word` ^ (string_of_int n) in
    let wordn_def = new_definition
    		 (wordn_name ^ `_DEF`,
		  "^(mk_primed_var(wordn_name,type_of A)) = ^A") in
    let thm4 = spec_fn n (SUBS [SYM wordn_def] thm3) in
    let thm5 = CONV_RULE
		(BINDER_CONV (DEPTH_FORALL_CONV(RAND_CONV SIMP_RHS))) thm4 in
    let thm6 = CONV_RULE (BINDER_CONV cleanup) thm5 in
    let ax = save_thm(`Word`^(string_of_int n),GEN_ALL thm6) in
    let wvar = mk_primed_var (`w`, mk_type(name,[])) in
    let busvar = mk_primed_var (`bus`, ":(bool)bus") in
    let bitsn_name = `Bits` ^ (string_of_int n) in 
    let bitsn_def = new_definition
    		 (bitsn_name ^ `_DEF`,
		  "^(mk_primed_var(bitsn_name,type_of R)) = ^R") in
    let wdef,bdef = SYM wordn_def, SYM bitsn_def in
    let wordn_bitsn = CONV_RULE (GEN_ALPHA_CONV wvar)(SUBS [wdef;bdef] A_R) in
    let ntm = mk_const(string_of_int n, ":num") in
    letrec conv tm = 
	   if (tm = "0") then REFL tm else
	      (num_CONV THENC RAND_CONV conv) tm in
    let ntm_thm = SYM(conv ntm) in
    let th1 = CONV_RULE(BINDER_CONV(LHS_CONV BETA_CONV)) R_A in
    let len_bitsn_wordn = CONV_RULE (GEN_ALPHA_CONV busvar)
			(SUBS [wdef;bdef;ntm_thm] th1) in
    let sptm = (rand(lhs(concl(SPEC_ALL wordn_bitsn)))) in
    let spthm = SPEC sptm len_bitsn_wordn in
    let subs_th = SUBS [EQT_INTRO (REFL sptm)]
		  (SUBS [SPEC_ALL wordn_bitsn] spthm) in
    let len_bitsn = GEN_ALL(EQT_ELIM subs_th) in
    let th2 = GEN_ALL(CONV_RULE (GEN_ALPHA_CONV wvar) (SPEC wvar R_11)) in
    let bits_11 = SUBS [bdef] th2 in
    let th3 = CONV_RULE(BINDER_CONV(LHS_CONV BETA_CONV)) R_ONTO in
    let th4 = CONV_RULE (GEN_ALPHA_CONV busvar) (SUBS [bdef;ntm_thm] th3) in
    let len_bits_onto = 
        CONV_RULE (BINDER_CONV(RAND_CONV(GEN_ALPHA_CONV wvar))) th4 in
    let ax_body = 
        snd(strip_forall(snd(dest_abs(rand(snd(dest_forall(concl ax))))))) in
    let blist = rand(rand(lhs ax_body)) in
    let len_thm = (SUBS [ntm_thm] (Width_CONV "Width ^blist")) in
    let bits_onto = GEN_ALL(EQ_MP (SPEC blist len_bits_onto) len_thm) in
    let bitsn_wordn = GEN_ALL(EQ_MP (SPEC blist len_bitsn_wordn) len_thm) in
    let A_11_beta = CONV_RULE (ONCE_DEPTH_CONV BETA_CONV) A_11 in
    letrec prime_blist tm = 
      if (is_const(rator tm)) then 
         "Wire ^((mk_var o  ((\t.t ^ `'`) # I) o dest_var) (rand tm))" else
      let c,[h;t] = strip_comb tm in
      "^c ^((mk_var o ((\t.t ^ `'`) # I) o dest_var) h) ^(prime_blist t)" in
    let blist' = prime_blist blist in
    let blist'_len = (SUBS [ntm_thm] (Width_CONV "Width ^blist'")) in
    let A_11_SPEC = SUBS [ntm_thm;wdef] (SPECL [blist;blist'] A_11_beta) in
    let w_11 = GEN_ALL(LIST_MP [len_thm;blist'_len] A_11_SPEC) in
    [ax;wordn_bitsn;bitsn_wordn;len_bitsn_wordn;len_bitsn;
     bits_11;bits_onto;len_bits_onto;w_11];;

% ---------------------------------------------------------------------	%
% AUXILLIARY PROGRAMS							%
% ---------------------------------------------------------------------	%

% BINDER_CONV conv "B x. tm[x]" applies conv to tm[x]			%
let BINDER_CONV conv =  (RAND_CONV (ABS_CONV conv));;

% DEPTH_FORALL_CONV : BINDER_CONV in depth				%
letrec DEPTH_FORALL_CONV conv tm = 
       if (is_forall tm) then
          BINDER_CONV (DEPTH_FORALL_CONV conv) tm else
	  conv tm;;

letrec DEPTH_EXISTS_CONV conv tm = 
       if (is_exists tm) then
          BINDER_CONV (DEPTH_EXISTS_CONV conv) tm else
	  conv tm;;

% LHS_CONV conv "OP t1 t2" applies conv to t1				%
let LHS_CONV = RATOR_CONV o RAND_CONV ;;

% ---------------------------------------------------------------------	%
% procedure for proving induction theorem from wordn type axiom		%
% ---------------------------------------------------------------------	%

% BINOP_CONV conv "OP t1 t2" applies conv to t1 and t2			%
let BINOP_CONV conv = (RAND_CONV conv) THENC (LHS_CONV conv);;

% A few little lemmas							%
let lemma1 = GEN_ALL(CONJUNCT1 (SPEC_ALL AND_CLAUSES)) and
    lemma2 = GEN_ALL(CONJUNCT1(CONJUNCT2 (SPEC_ALL EQ_CLAUSES))) and
    lemma3 = GEN_ALL(CONJUNCT1 (SPEC_ALL EQ_CLAUSES));;

% prove_wordn_induction_thm: from a wordn type axiom, prove induction 	%
%			     thm					%
%									%
% E.g. Input: 								%
%									%
% |- !f. ?! fn. !b0 b1 b2 b3. fn(Word4 b0 b1 b2 b3 ) = f b0 b1 b2 b3	%
%									%
% Output:								%
%									%
% |- !P. (!b0 b1 b2 b3. P(Word4 b0 b1 b2 b3 )) ==> (!x. P x)		%

let prove_wordn_induction_thm th = 
    let fn = fst(dest_abs(rand(concl(SPEC_ALL th)))) in
    let [ty;rty] = snd(dest_type (type_of fn)) in
    let th1 = CONV_RULE (DEPTH_FORALL_CONV(EXISTS_UNIQUE_CONV))
			(INST_TYPE [":bool",rty] th) in
    let th2 = GEN_ALL(CONJUNCT2 (SPEC_ALL th1)) in
    let tyvar = genvar ty and
        vars = 
	fst(strip_forall(snd(dest_abs(rand(snd(dest_forall(concl th))))))) in
    let fns = [list_mk_abs (vars,"T");"\^tyvar.T";"P:^ty->bool"] in
    let th3 = SPECL fns th2 in
    let BETA = DEPTH_FORALL_CONV(BINOP_CONV LIST_BETA_CONV) and
	ETA_REFL = EVERY_CONV [REPEATC (REWR_CONV FORALL_SIMP);
			       REWR_CONV REFL_CLAUSE] in
    let conv1 = EVERY_CONV 
		 [(LHS_CONV o LHS_CONV o EVERY_CONV) [BETA; ETA_REFL];
		   LHS_CONV (REWR_CONV lemma1);
   		   LHS_CONV ((DEPTH_FORALL_CONV o EVERY_CONV)
			     [RAND_CONV LIST_BETA_CONV; 
			      REWR_CONV lemma2])] in
    let conv2 = (RAND_CONV o EVERY_CONV)
		[FUN_EQ_CONV;BINDER_CONV(LHS_CONV BETA_CONV);
		 BINDER_CONV(REWR_CONV lemma3)] in
         GEN_ALL(CONV_RULE (conv1 THENC conv2) th3);;

% ---------------------------------------------------------------------	%
% cases for wordn types.						%
% ---------------------------------------------------------------------	%

let lemma1 = CONJUNCT1 NOT_CLAUSES;;

% prove_wordn_cases_thm : prove a cases theorem for a wordn type	%
%									%
% E.g. Input:								%
%									%
% |- !P. (!b0 b1 b2 b3. P(Word4 b0 b1 b2 b3 )) ==> (!x. P x)		%
%									%
% Output:								%
%									%
% |- !x. ?b0 b1 b2 b3. x = Word4 b0 b1 b2 b3 				%

let prove_wordn_cases_thm th = 
    (let x,P = dest_forall(snd(dest_imp(snd(dest_forall(concl th))))) in
     let xvar = genvar (type_of x) in
     let th1 = SPEC x (UNDISCH(SPEC "\^xvar.~(^x = ^xvar)" th)) in 
     let th2 = NOT_INTRO(DISCH_ALL (MP (CONV_RULE BETA_CONV th1) (REFL x))) in
     letrec conv1 tm =
         if (is_forall(dest_neg tm)) then
    	    (NOT_FORALL_CONV THENC BINDER_CONV conv1) tm else 
	    ((RAND_CONV BETA_CONV) THENC (REWR_CONV lemma1)) tm in
         GEN_ALL(CONV_RULE conv1 th2)) ? failwith `Can't prove cases thm`;;

% Define a wordn type and prove all the standard theorems.		%
let declare_wordn_type flag n = 
    let wn = `Word` ^ string_of_int n in
    let bn = `Bits` ^ string_of_int n in
    let [ax;wn_bn;bn_wn;wid_bn_wn;wid_bn;b_11;b_onto;wid_b_onto;w_11] =
	  define_wordn_type n in
    let ind = prove_wordn_induction_thm ax in
    let cases = prove_wordn_cases_thm ind in
    if (flag) then 
       (save_thm(wn ^ `_` ^ bn,wn_bn);
	save_thm(bn ^ `_` ^ wn,bn_wn);
	save_thm(`Width_` ^ bn ^ `_` ^ wn,wid_bn_wn);
	save_thm(`Width_` ^ bn, wid_bn);
	save_thm(bn ^ `_11`,b_11);
	save_thm(bn ^ `_Onto`,b_onto);
	save_thm(`Width_` ^ bn ^ `_Onto`,wid_b_onto);
	save_thm(wn ^ `_Induct`,ind);
	save_thm(wn ^ `_Onto`,cases);
	save_thm(wn ^ `_11`,w_11);());
     [ax;wn_bn;bn_wn;wid_bn_wn;wid_bn;b_11;b_onto;wid_b_onto;ind;cases;w_11];;

% ------------------------------------------------------------------ %
% Other tools...						     %
% ------------------------------------------------------------------ %

% Make an OL bus.						     %
% eg.	mk_ol_bus ":(*)list" ["T";"F";"F";"F"];;                     %
% 	"Bus T(Bus F(Bus F(Wire F)))" : term                         %

letrec mk_ol_bus ty l = 
       if (null l) then fail else
       if (null (tl l)) then "Wire ^(hd l)" else
	  "Bus ^(hd l) ^(mk_ol_bus ty (tl l))";;

%<  Old version; replaced below.
% wordn_CONV : "#1010" ---> |- #1010 = Word4 [F;T;F;T]			%
let wordn_CONV tm = 
    (let str,ty = dest_const tm in
     let size = (hd(rev(explode(fst(dest_type ty))))) in
     if (not (ty = (mk_type(`word` ^ size,[])))) then fail else
     let hash.bits = explode str in
     if (not (hash = `#`)) then fail else
     let const = mk_const(`Word`^size,":(bool)bus -> ^ty") and
         args = rev(map(\x.if (x=`1`) then "T" else "F") bits) in
         mk_thm([], "^tm = ^const ^(mk_ol_bus ":bool" args)"))?
     failwith `wordn_CONV`;;
>%

% Modified 89.06.26 - BtG :                                          %
% * Works for :wordn  where n>9                                      %
% * uses same bit ordering for both buses and wordn's:               %
% wordn_CONV : "#1010" ---> |- #1010 = Word4 [T;F;T;F]	             %
let wordn_CONV tm = 
    (let str,ty = dest_const tm in
     let size = (implode ((tl o tl o tl o tl)(explode(fst(dest_type ty))))) in
     if (not (ty = (mk_type(`word` ^ size,[])))) then fail else
     let hash.bits = explode str in
     if (not (hash = `#`)) then fail else
     let const = mk_const(`Word`^size,":(bool)bus -> ^ty") and
         args = map(\x.if (x=`1`) then "T" else "F") bits in
         mk_thm([], "^tm = ^const ^(mk_ol_bus ":bool" args)"))?
     failwith `wordn_CONV`;;

% wordn_EQ_CONV th "#aaa = #bbb" --> is #aaa = #bbb ?			%
let wordn_EQ_CONV th tm = 
    let conv1 = EVERY_CONV [RAND_CONV wordn_CONV; 
			    RATOR_CONV (RAND_CONV wordn_CONV)] in
    (conv1 THENC REWR_CONV th THENC BUS_EQ_CONV bool_EQ_CONV) tm;;

% ---------------------------------------------------------------------	%
% induction for wordn types: same as for recursive types.		%
% --------------------------------------------------------------------- %

% BINDER_CONV conv "B x. tm[x]" applies conv to tm[x]			%
let BINDER_CONV conv =  (RAND_CONV (ABS_CONV conv));;

% DEPTH_FORALL_CONV : BINDER_CONV in depth				%
letrec DEPTH_FORALL_CONV conv tm = 
       if (is_forall tm) then
          BINDER_CONV (DEPTH_FORALL_CONV conv) tm else
	  conv tm;;

% INDUCT_THEN th th_tac goal : general induction tactic for rec types	%
%									%
% Induct using induction thm th.  Use th_tac on induction hyps.		%

% Why is this redefined from the built-in version?  Is this a        %
% left-over from the implementation of this before hol88 was ready?  %
% Assuming this is the case, I eliminate it for now...               %
% 89.06.26 - BtG                                                     %
%<
let INDUCT_THEN th th_tac (A,t) = 
    (let x,body = dest_forall t in
     let tyi = snd(match (fst(dest_forall (concl th))) "\^x.T") in
     let spec = SPEC (mk_abs(x,body)) (INST_TYPE tyi th) in
     let thm = CONV_RULE(RAND_CONV(BINDER_CONV BETA_CONV)) spec in
     let thm' = DISCH_ALL (CONV_RULE (GEN_ALPHA_CONV x) (UNDISCH_ALL thm)) in
     let tac = 
     (MATCH_MP_TAC thm' THEN
      REPEAT CONJ_TAC THEN
      FIRST [CONV_TAC (DEPTH_FORALL_CONV BETA_CONV);
  	     REPEAT GEN_TAC THEN 
	     DISCH_THEN (\th. 
	      CONV_TAC (DEPTH_FORALL_CONV BETA_CONV) THEN
	      MAP_EVERY (th_tac o (CONV_RULE BETA_CONV)) (CONJUNCTS th))]) in
      (tac (A,t))) ? failwith `INDUCT_THEN`;;
>%

% ---------------------------------------------------------------------	%
% Tools for proving exhustive cases theorems for wordn			%
% ---------------------------------------------------------------------	%
let DISJ_ASSOC = 
    TAC_PROOF(([], "((A \/ B) \/ C) = (A \/ B \/ C)"),
    	      BOOL_CASES_TAC "A:bool" THEN REWRITE_TAC[]);;

% ---------------------------------------------------------------------	%
% Modified 89.06.26 - BtG :                                             %
% Now works for the ordering of bits built into wordn_CONV              %
% ---------------------------------------------------------------------	%
let prove_wordn_const_cases ind = 
    let n = 
       let ty = hd(snd(dest_type(type_of(fst(dest_forall(concl ind)))))) in
                int_of_string(hd(rev(explode(fst(dest_type ty))))) in
    let ntok = string_of_int n in
    letrec gen_bus i = 
	   let v = mk_var(`b` ^ (string_of_int i),":bool") in
	   if (i=1) then "Wire ^v" else
	      "Bus ^v ^(gen_bus (i-1))" in
    letrec gen_vars i = 
	   if (i=0) then [] else
	      let v = mk_var(`b` ^ (string_of_int i),":bool") in
	      v .(gen_vars (i-1)) in
    let vars = gen_vars n in
    let wdty = mk_type(`fun`,[":(bool)bus";mk_type(`word`^ntok,[])]) in
    let wd = mk_const(`Word` ^ ntok, wdty) in
    let bus = gen_bus n in
    let refl = REFL "^wd ^bus" in
    let conv b th tm = 
        let l,r = dest_eq tm in
	let bv = genvar ":bool" in
	let pat = "^l = ^(subst [bv,b] r)" in
        SUBST_CONV [th,bv] pat tm in
    let do_case bit th = 
        let cases_th = SPEC bit BOOL_CASES_AX in
	let T_case = ASSUME(fst(dest_disj(concl cases_th))) in
	let F_case = ASSUME(snd(dest_disj(concl cases_th))) in
	let T_thm = CONV_RULE (ONCE_DEPTH_CONV (conv bit T_case)) th in
	let F_thm = CONV_RULE (ONCE_DEPTH_CONV (conv bit F_case)) th in
	let T_or_thm = DISJ1 T_thm (concl F_thm) and
	    F_or_thm = DISJ2 (concl T_thm) F_thm in
           (DISJ_CASES cases_th T_or_thm F_or_thm) in
    letrec do_cases bits th = 
           if (null bits) then th else
	      do_case (hd bits) (do_cases (tl bits) th) in
    let cases_thm = do_cases vars refl in
    let wconv tm = 
        let l,(W,bits) = (I # dest_comb) (dest_eq tm) in
	letrec mk_bits b = 
	       if (is_const (rator b)) then 
	           [if(rand b) = "T" then `1` else `0`] else
	       let C,[h;t] = strip_comb b in
	       (if h = "T" then `1` else `0`).(mk_bits t) in
	let const = mk_const(implode (`#` . (mk_bits bits)),
			    mk_type(`word`^ntok,[])) in
	let eqn = SYM(wordn_CONV const) in
	RAND_CONV (REWR_CONV eqn) tm in
    let const_thm = CONV_RULE(ONCE_DEPTH_CONV wconv) cases_thm in
    let var = genvar(mk_type(`word`^ntok,[])) in
    let P = mk_abs(var,subst [var,"^wd ^bus"] (concl const_thm)) in
    let ind_thm = CONV_RULE(ONCE_DEPTH_CONV BETA_CONV) (SPEC P ind) in
    MP ind_thm (GENL vars const_thm);;


% ---------------------------------------------------------------------	%
% Function definitions on wordn						%
% ---------------------------------------------------------------------	%

% derive_existence_thm th tm						%
%									%
% If th is a wordn axiom and tm is a term giving a definition,		%
% derive an existence theorem for doing the definition.			%
% The existence theorem is suitably type-instantiated.			%
%									%
% E.g. Input								%
%									%
% |- !f. ?! fn. !b0 b1 b2 b3. fn(Word4 b0 b1 b2 b3 ) = f b0 b1 b2 b3 	%
%									%
% "FN x(Word4 a b c d)y = (x + y = 7) /\ a /\ b" 			%
%									%
% Output:								%
%									%
% |- !g1. ?fn. !g2 g3 g4 g5 g6 g7.					%
%    fn (Word4 g2 g3 g4 g5) g6 g7 = g1  g2 g3 g4 g5 g6 g7		%
%									%
% Note: the g's are genvars						%

let derive_wordn_existence_thm th tm = 
    (let var = (genvar o type_of) (fst(dest_forall(concl th))) in 
     let exists = CONJUNCT1 (CONV_RULE EXISTS_UNIQUE_CONV (SPEC var th)) in
     let e_fn = fst(dest_exists (concl exists)) in
     letrec splt l = 
	    if (is_var (hd l)) then 
	       (let bv,C,av = splt (tl l) in ((hd l).bv,C,av)) else
	    if (is_const (hd l) or (is_comb (hd l))) then
	       [],(hd l),(tl l) else fail in
     let bv,Con,av =splt(snd(strip_comb(lhs(snd(strip_forall tm))))) in
     let rhsfn = let cv = genvar(type_of Con) in
                 let r = rhs(snd(strip_forall tm)) in
                 list_mk_abs(cv. (bv @ av),r) in
     let th_inst = INST_TYPE (snd(match e_fn rhsfn)) exists in
     let fn = fst(dest_exists(concl th_inst)) in
     let argvars = map (genvar o type_of) (bv @ av) in
     let ap_ths th = 
         let v = map (genvar o type_of) (fst(strip_forall(concl th))) in
	 let th1 = rev_itlist (C AP_THM) argvars (SPECL v th) in
	     (GENL (v @ argvars) th1) in
     let th1 = (ap_ths (SELECT_RULE th_inst)) in
     let sel = mk_select(dest_exists (concl th_inst)) in
     GEN_ALL(EXISTS(mk_exists(fn,subst [fn,sel](concl th1)),sel)th1))?
     failwith `Can't derive existence theorem`;;

% mk_fn: make the function for the rhs of a clause in the existence thm	%
% 									%
% returns:  1) the function						%
%	    2) a list of variables that the clause should be SPECl	%
%	    3) a pre-done beta-conversion of the rhs.			%

let mk_fn (cl,(Fn,bv,C,av,r)) = 
    let lcl = hd(snd(strip_comb(lhs(snd(strip_forall cl))))) in
    let lclvars = tl(snd(strip_comb(lhs(snd(strip_forall cl))))) in
    let m = (fst(match lcl C)) @ combine((bv @ av),lclvars) in
    let cl' = subst m (snd(strip_forall cl)) in
    let nonrec = snd(strip_comb(rhs cl')) in
    let varsub = map (\v. (genvar (type_of v)),v) nonrec in
    let fn = list_mk_abs(fst(split varsub),subst varsub r) in
    let specl =  map (\v.(fst(rev_assoc v m))? v) (fst(strip_forall cl)) in
    let beta = LIST_BETA_CONV(list_mk_comb(fn,snd(strip_comb(rhs cl')))) in
        (fn,specl,beta);;

% instantiate_existence_thm eth tm : instantiate eth to match tm 	%
%									%
% E.g. INPUT:								%
%									%
% |- !g1. ?fn. !g2 g3 g4 g5 g6 g7.					%
%    fn (Word4 g2 g3 g4 g5) g6 g7 = g1  g2 g3 g4 g5 g6 g7		%
%									%
% "FN x(Word4 a b c d)y = (x + y = 7) /\ a /\ b" 			%
%									%
% OUTPUT:								%
%									%
%  |- ?fn. !a b c d x y. fn(Word4 a b c d)x y = (x + y = 7) /\ a /\ b	%

let instantiate_wordn_existence_thm eth tm = 
   (let cl = snd(strip_forall tm) in
    letrec splt l = 
	   if (is_var (hd l)) then 
	      (let bv,C,av = splt (tl l) in ((hd l).bv,C,av)) else
	   if (is_const (hd l) or (is_comb (hd l))) then
	      [],(hd l),(tl l) else fail in
    let dest tm = 
	let ((Fn,(bv,C,av)),r)=(((I # splt) o strip_comb) # I)(dest_eq tm) in
	    (Fn,bv,C,av,r) in
    let destcl = dest cl in
    let ecl = snd(dest_exists(snd(strip_forall(concl eth)))) in
    let spfn,spec,beta = mk_fn (ecl,destcl) in
    let ethsp = SPEC spfn eth in
    let SP = SPECL spec (SELECT_RULE ethsp) in
    let rule (th1,th2) = CONV_RULE (RAND_CONV (REWR_CONV th1)) th2 in
    let th = GEN_ALL(rule(beta,SP)) in
    let fn = fst(dest_exists (concl ethsp)) and
        fsel = mk_select(dest_exists(concl ethsp)) in
        (EXISTS (mk_exists(fn,subst [fn,fsel] (concl th)),fsel) th))?
    failwith `Can't instantiate existence theorem`;;

% prove_wordn_fn_exists th tm						%
%									%
% Given 1) th, a wordn type axiom.					%
%	2) tm, the specification of a function on wordn values.		%
%									%
% proves that such a function exists.					%

% Quantify the equations of the function spec.				%
let closeup tm = 
    let lvars t = subtract
		    (freesl(snd(strip_comb(lhs(snd (strip_forall t))))))
    		    (fst(strip_forall t)) in
    list_mk_conj(map (\tm.list_mk_forall(lvars tm,tm)) (conjuncts tm));;

let prove_wordn_fn_exists th tm = 
   (let eth = derive_wordn_existence_thm th tm in
    let ith = instantiate_wordn_existence_thm eth tm in
    letrec get_avars tm  = 
	   if (is_var (rand tm)) then (get_avars (rator tm)) else
	      (snd(strip_comb (rator tm)),rand tm) in
    let cl = snd(strip_forall tm) in
    let fn = fst(strip_comb(lhs cl)) and
        av,tv = (map (genvar o type_of) # (genvar o type_of))
	        (get_avars (lhs cl)) in
    let goal = ([],mk_exists(fn,closeup tm)) in 
    let etac th = 
	let efn = fst(strip_comb(lhs(snd(strip_forall(concl th))))) in
        EXISTS_TAC (list_mk_abs(av@[tv],list_mk_comb(efn,tv.av))) in 
    let fn_beta th (A,gl) = 
 	 let efn = fst(strip_comb(lhs(snd(strip_forall(concl th))))) in
         let eabs = (list_mk_abs(av@[tv],list_mk_comb(efn,tv.av))) in 
	 let epat = list_mk_comb(eabs, map (genvar o type_of) (av @ [tv])) in
	 let tms = find_terms (\tm. can (match epat) tm) gl in
	 SUBST_TAC (map LIST_BETA_CONV tms) (A,gl) in
    GEN_ALL(TAC_PROOF(goal,
            STRIP_ASSUME_TAC ith THEN FIRST_ASSUM etac THEN
            REPEAT STRIP_TAC THEN FIRST_ASSUM fn_beta THEN
            FIRST_ASSUM MATCH_ACCEPT_TAC)))?
    failwith `Can't prove that function exists`;;

% Make a new recursive function definition.				%
let new_wordn_definition infix_flag th name tm = 
    let thm = prove_wordn_fn_exists th tm in
    if (is_forall (concl thm)) then 
	failwith `definition contains free vars` else
    let def = mk_eq(fst(dest_exists (concl thm)),
    		    mk_select(dest_exists (concl thm))) in
    let defn = if (infix_flag) then
	           new_infix_definition (name ^ `_DEF`,def) else
	           new_definition (name ^ `_DEF`,def) in 
        save_thm (name,SUBS [SYM defn] (SELECT_RULE thm));;
