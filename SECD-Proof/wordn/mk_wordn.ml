% FILE		: mk_wordn.ml						%
% DESCRIPTION   : Creates the theory "wordn.th".			%
%									%
% READS FILES	: bus.th	 					%
% WRITES FILES	: wordn.th						%
%									%
% AUTHOR	: (c) T. Melham						%
% DATE		: 87.09.23						%
% 									%
% NOTE		: PRELIMINARY RELEASE. Please do not distribute.	%
%                 (This was cleared with T. Melham for use with the     %
%                  SECD proof example distribution. - BtG)              %
% 									%
% REVISIONS	: 09.04.91 - BtG - made compatible with Version 1.12.	%


% Create the new theory							%
new_theory `wordn`;;

% Parent theories							%
map new_parent [`bus`];;

% Fetch theorems.							%
let Width = definition `bus` `Width`;;

let REWRITE1_TAC = \th. REWRITE_TAC [th];;
let EXISTS_UNIQUE_TAC = (CONV_TAC o DEPTH_CONV o CHANGED_CONV) EXISTS_UNIQUE_CONV;;


% prove the theorem for defining wordn types.				%
let wordn_DEF_THM = 
    prove_thm
    (`wordn_DEF_THM`,
     "!n. !ABS. !REP.
      (!a:*. ?r:(bool)bus. (a = ABS r) /\ (\r. Width r = (SUC n)) r) ==>
      (!r:(bool)bus. (\r. Width r = (SUC n)) r = (REP(ABS r:*) = r)) ==>
      !f. ?!fn. !r:(bool)bus. 
         (Width r = (SUC n)) ==> (fn (ABS r):** = f r)",
    CONV_TAC (ONCE_DEPTH_CONV BETA_CONV) THEN
    REPEAT GEN_TAC THEN EXISTS_UNIQUE_TAC THEN 
    CONV_TAC (REDEPTH_CONV (BETA_CONV ORELSEC FUN_EQ_CONV)) THEN
    REPEAT STRIP_TAC THENL
    [EXISTS_TAC "((f:(bool)bus->**) o REP):*->**" THEN
     ASM_REWRITE_TAC [o_THM] THEN
     REPEAT (STRIP_GOAL_THEN REWRITE1_TAC);
     REPEAT (POP_ASSUM MP_TAC) THEN
     DISCH_THEN (STRIP_ASSUME_TAC o SPEC "x:*") THEN
     REPEAT STRIP_TAC THEN RES_TAC THEN
     ASM_REWRITE_TAC[]]);;

% For use in type definition package...					%
let exists_wordn_rep = 
    prove_thm
    (`exists_wordn_rep`,
     "!n. ?bus:(bool)bus. (\bus. Width bus = (SUC n)) bus",
     CONV_TAC (ONCE_DEPTH_CONV BETA_CONV) THEN
     INDUCT_TAC THENL
     [EXISTS_TAC "Wire @b:bool.T" THEN REWRITE_TAC [Width];
      POP_ASSUM STRIP_ASSUME_TAC THEN
      EXISTS_TAC "Bus T bus" THEN ASM_REWRITE_TAC [Width]]);;

