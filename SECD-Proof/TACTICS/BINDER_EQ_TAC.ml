% ================================================================= %
% BINDER_EQ_TAC: tactic                                             %
% *************                                                     %
%                                                                   %
% Synopsis: strips matching binders from a top-level equality goal. %
%                                                                   %
% Description: The tactic effects the inverse of the forward        %
%    inference rules FORALL_EQ, EXISTS_EQ, and SELECT_EQ.           %
%                                                                   %
% {A} *t. t1[t] = *t'. t2[t']  (* in [!,?,@])                       %
% ===========================                                       %
%    {A} t1[t''] = t2[t'']                                          %
%                                                                   %
% (t'' not free in *t.t1 nor t2)                                    %
%                                                                   %
%   The quantified terms need not be identical, but                 %
%   instead only alpha convertable (the types must match).          %
%                                                                   %
% Failure: fails if binders differ, or bound variables have         %
%    different types.                                               %
%                                                                   %
% Written by: Brian Graham 05.12.90                                 %
% ================================================================= %

let BINDER_EQ_TAC:tactic(l,t) =
 (let t1,t2 = dest_eq t
  in
  let q1,n1,w1 = ((I#dest_abs) o dest_comb) t1
  and q2,n2,w2 = ((I#dest_abs) o dest_comb) t2
  in
  if (q1 = q2)
  then if (type_of n1 = type_of n2)
       then if (n1 = n2)
            then let p[th] =  MK_COMB(REFL(fst(dest_comb t1)), ABS n1 th)
                 in
		 ([l,mk_eq(w1,w2)], p)
            else let n = variant ((frees t1)@(frees w2)) n1
	         in
		 let p[th] =
		   let abs_th = (ABS n th)
		   in
		   let lhs,rhs = dest_eq(concl abs_th)
		   in
	           MK_COMB(REFL(fst(dest_comb t1)),
			   TRANS (SYM (GEN_ALPHA_CONV n1 lhs))
			         (TRANS abs_th
					(GEN_ALPHA_CONV n2 rhs)))
						 
	    in
            ([l,mk_eq(subst [n,n1]w1,(subst [n,n2] w2))], p)
       else failwith `BINDER_EQ_TAC: quantified variables have different types`
  else failwith `BINDER_EQ_TAC: different binders at top level`
  ) ? failwith `BINDER_EQ_TAC`;;
