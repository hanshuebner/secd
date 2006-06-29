% SECD verification						  %
%								  %
% FILE: SPLIT_CONJUNCTS.ml					  %
%							          %
% DESCRIPTION: For hardware devices with multiple components, it  %
%              is desirable to split the task into proving each   %
%              component implementation derived equation is       %
%              equivalent to its specification equation.  This    %
%              tactic will be used after a REWRITE and EXPAND, so %
%              that all internal nodes are eliminated and the     %
%              form of the goal is two groups of corresponding    %
%              conjuncts (in the same order), thus                %
%              Note, I split only one pair of conjuncts.          %
%                                                                 %
%   {A} e0 /\ e1 = e0' /\ e1'                                     %
%   ==============================                                %
%   [ {A} e0 = e0'; {A} e1 = e1' ]                                %
%								  %
% Brian Graham 89.11.07      			                  %
%                                                                 %
%=================================================================%

% First the forward inference rule: CONJ_EQ                       %
%
CONJ_EQ :  thm -> (thm -> thm)
                                          
  {A1} |- e0 = e0' , {A2} |- e1 = e1'
  ===================================
  {A1 U A2} |- e0 /\ e1 = e0' /\ e1'
%

let CONJ_EQ th1 th2 =
 let th1a,th1c = dest_thm th1
 and th2a,th2c = dest_thm th2
 in
 let (a,b),(c,d) = (dest_eq#dest_eq)(th1c,th2c)
 in
 let mark1 = genvar ":bool"
 in
 SUBST [th1,mark1]
       "^a /\ ^c = ^mark1 /\ ^d"
       (AP_TERM "$/\ ^a" th2);;

% ================================================================= %
% now the tactic : SPLIT_CONJUNCTS_TAC                              %
% ================================================================= %
let split_conjuncts_tac (asl, term) =
  let (e0,e1),(e0',e1') = ((dest_conj # dest_conj) o dest_eq) term
  in
  ([asl,mk_eq (e0,e0'); asl,mk_eq(e1,e1')],
    \[th0;th1]. CONJ_EQ th0 th1);;

% ================================================================= %
% This solves the trivial conjuncts as well.                        %
% ================================================================= %
let SPLIT_CONJUNCTS_TAC =
  split_conjuncts_tac THEN (REFL_TAC ORELSE ALL_TAC) ;;
                                                 
% ================================================================= %
% now attempting to be more general ...                             %
% ================================================================= %

% ================================================================= %
% flatten one level of conjuncts.                                   %
% ================================================================= %
letrec my_conjuncts w =
 (let a,b = dest_conj w in a . my_conjuncts b) ? [w];;

% ================================================================= %
% Moves conjunct ctm to the front of a multi conjunct term tm.      %
%                ***                                       **       %
% ================================================================= %
let my_FRONT_CONJ_CONV ctm tm =
 let al = my_conjuncts tm
 in 
 FRONT_CONJ_CONV al ctm;;

% ================================================================= %
% RHS_CONV conv "t1 = t2" applies conv to t2			    %
% ================================================================= %
let RHS_CONV conv tm =
 (is_eq tm) => (RAND_CONV conv) tm
 | failwith `RHS_CONV applied to non eq term`;;

% ================================================================= %
% This tactic doesn't have to have the same ordering of IDENTICAL   %
% conjuncts on each side of the equality to solve it.               %
%                                                                   %
% This tactics must have IDENTICAL terms on each side of the        %
% equality to work.                                                 %
% ================================================================= %
let REORDER_SPLIT_CONJUNCTS_TAC (asl,gl) =
  let (e0,e1),(e0',e1') = ((dest_conj # dest_conj) o dest_eq) gl
  in
  ((e0 = e0') => (SPLIT_CONJUNCTS_TAC (asl,gl))
              |  (((CONV_TAC (RHS_CONV (my_FRONT_CONJ_CONV e0)))
		   THEN SPLIT_CONJUNCTS_TAC)(asl,gl)));;

