% This tactic is taken directly from the code for COND_CASES_TAC in the
  file ml/tactics.ml, and is modified to allow a tactical to be applied
  to the assumptions generated.   11.12.90 - BtG
%
%
Find a conditional "p=>t|u" that is free in the goal and whose condition p
is not a constant.  Perform a cases split on the condition.

	A(p=>t|u)
    =================
      [p=T] A(t)
      [p=F] A(u)
%

let COND_CASES_THEN tac (asl,w) =
    let is_good_cond tm =  not(is_const(fst(dest_cond tm))) ? false  in
    let cond = 
	find_term (\tm. is_good_cond tm & free_in tm w) w
        ? failwith `COND_CASES_THEN`
    in
    let p,t,u = dest_cond cond in
    let condcl =
      CONJUNCTS (SPECL [t;u] (INST_TYPE [type_of t, ":*"] COND_CLAUSES))
    in
    REPEAT_TCL DISJ_CASES_THEN
        (\th. SUBST1_TAC th  THEN  SUBST_TAC condcl  THEN  tac th)
	(SPEC p BOOL_CASES_AX)
    (asl,w) ;;
