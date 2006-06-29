% SYM_TAC							%
%								%
%	a = b							%
%	=====							%
%	b = a							%

let SYM_TAC =
 (CONV_TAC (ONCE_DEPTH_CONV SYM_CONV))
 ? failwith `SYM_TAC`;;



% SYM_RULE							%
%								%
%	   a = b						%
%	----------						%
%	|- b = a						%

let SYM_RULE =
 (CONV_RULE (ONCE_DEPTH_CONV SYM_CONV))
 ? failwith `SYM_RULE`;;
