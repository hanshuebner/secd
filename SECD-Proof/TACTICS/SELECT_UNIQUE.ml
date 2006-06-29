%
the first attempt proved a theorem:

g "(Q:*->bool) y
    ==>
    (!x z:*. (Q x /\ Q z) ==> (x = z))
    ==>
    ((@x.Q x) = y)";;
expand
 (DISCH_THEN
   (\th1.
   DISCH_THEN
    (\th2.
     in1_conv_tac ETA_CONV
     THEN ACCEPT_TAC
      (MP (SPECL ["$@ Q:*"; "y:*"] th2) 
          (CONJ (SELECT_INTRO th1) th1)))));;
%

%
	SELECT_UNIQUE_RULE:
	===================

	("x","y")   A1 |- Q[y]  A2 |- !x y.(Q[x]/\Q[y]) ==> (x=y)
	=========================================================
		A1 U A2 |- (@x.Q[x]) = y

Permits substitution for values specified by the Hilbert Choice
operator with a specific value, if and only if unique existance
of the specific value is proven.
%

let SELECT_UNIQUE_RULE (x,y) th1 th2 =
  let Q = mk_abs (x, subst [x,y] (concl th1))
  in
  let th1' = SUBST [SYM (BETA_CONV "^Q ^y"), "b:bool"] "b:bool" th1
  in
  (MP (SPECL ["$@ ^Q"; y] th2)
      (CONJ (in1_conv_rule BETA_CONV (SELECT_INTRO th1')) th1));;


%
	SELECT_UNIQUE_TAC:
	==================

	        [ A ] "(@x. Q[x]) = y"
	===================================================
        [ A ] "Q[y]"   [ A ] "!x y.(Q[x]/\Q[y]) ==> (x=y)"

Given a goal that requires proof of the value specified by the 
Hilbert choice operator, it returns 2 subgoals:
  1. "y" satisfies the predicate, and
  2. unique existance of the value that satisfies the predicate.
%
	
let SELECT_UNIQUE_TAC:tactic (gl,g) =
  let Q,y = dest_eq g
  in
  let x,Qx = dest_select Q
  in
  let x' = variant (x.freesl(g.gl))x
  in
  let Qx' = subst [x', x] Qx
  in
  ([gl,subst [y,x]Qx;
    gl, "!^x ^x'. (^Qx /\ ^Qx') ==> (^x = ^x')"],
   (\thl. SELECT_UNIQUE_RULE (x,y) (hd thl) (hd (tl thl))));;
