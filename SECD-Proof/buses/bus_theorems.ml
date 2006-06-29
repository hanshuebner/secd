% ================================================================= %
% This file contains a pair of tactics to extend the theory         %
% of buses.  Particularly important to break down buses on which we %
% do not induct, to subcomponents.                                  %
% ================================================================= %

let Wire_same_Width = theorem `bus_theorems` `Wire_same_Width`
and Bus_same_Width  = theorem `bus_theorems` `Bus_same_Width`
and bus_map         = definition `bus_theorems` `bus_map`
and bus_map2        = definition `bus_theorems` `bus_map2`
and bus_map_sum     = definition `bus_theorems` `bus_map_sum`
and shuffle         = definition `bus_theorems` `shuffle`
;;

let bus_Induct = theorem `bus` `bus_Induct`;;

% ================================================================= %
% Note that the goal should be in the form:                         %
%  !b b'. (Width b' = Width b) ==> (Ff b b')                        %
%                                                                   %
% Start by inducting on "b", so the inductive assumption still      %
% has the quantified "!b'" and doesn't get substituted by the       %
% new term for it.                                                  %
% ================================================================= %

let wire_width_tac =
  DISCH_THEN
(\th. REPEAT_TCL CHOOSE_THEN SUBST1_TAC (porr[Wire_same_Width] th));;

let bus_width_tac =
  DISCH_THEN
   (\th. SUBST_ALL_TAC th
         THEN REPEAT_TCL CHOOSE_THEN
         (\th1. ASSUME_TAC (CONJUNCT1 th1)
	        THEN CONJUNCTS_THEN2 (ANTE_RES_THEN ASSUME_TAC)
			             (SUBST_ALL_TAC) th1)
	 (porr[Bus_same_Width] th));;
