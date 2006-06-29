% FILE		: bus.ml.ml						%
% DESCRIPTION   : Defines useful conversions and other functions for	%
%		  use with busses.					%
%									%
% READS FILES	: bus.th						%
% WRITES FILES	: <none>						%
%									%
% AUTHOR	: (c) T. Melham						%
% DATE		: 87.05.30						%
% 									%
% NOTE		: PRELIMINARY RELEASE. Please do not distribute.	%
%                 (This was cleared with T. Melham for use with the     %
%                  SECD proof example distribution. - BtG)              %
% 									%
% Modifications                                                         %
% 89.06.14 - BtG - documented BUS_EQ_CONV                               %

let (Wid_Wire,Wid_Bus) = CONJ_PAIR (definition `bus` `Width`);;
let not_Wire_Bus = theorem `bus` `not_Wire_Bus`
and not_Bus_Wire = theorem `bus` `not_Bus_Wire`;;
let Bus_11 = theorem `bus` `Bus_11` and
    Wire_11 = theorem `bus` `Wire_11`;;

letrec Width_CONV_fn th1 th2 tm = 
       let len,l = dest_comb tm in
       if (is_const (rator l)) then
          (if (fst(dest_const (rator l)) = `Wire`) then 
               (SPEC (rand l) th1) else fail) else
       let c,[h;t] = strip_comb l in
       let th = SPECL [h;t] th2 in
       let tm' = rand(rand(concl th)) in
       let th' = Width_CONV_fn th1 th2 tm' in
           SUBS [th'] th;;

letrec is_bus tm = 
       (if (is_comb tm) then 
       (if (is_comb (rator tm)) then
           (let c,[h;t] = strip_comb tm in
   	        (fst(dest_const c) = `Bus`) & is_bus t) else
           (fst(dest_const (rator tm)) = `Wire`)) else
            false ? false);;

let Width_CONV tm = 
    let len,l = dest_comb tm in
    if ((fst(dest_const len) = `Width`) & is_bus l) then
       let lty =  hd(snd(dest_type(type_of l))) in
       let th1 = INST_TYPE [lty,":*"] Wid_Wire in
       let th2 = INST_TYPE [lty,":*"] Wid_Bus in
       Width_CONV_fn th1 th2 tm else fail;;


let lemma1 = GEN_ALL(CONJUNCT1(SPEC_ALL AND_CLAUSES)) and
    lemma2 = GEN_ALL(el 3 (CONJUNCTS(SPEC_ALL AND_CLAUSES)));;

% 									%
% BUS_EQ_CONV : (term -> thm) -> term -> thm                            %
%                                                                       %
% conv                                                                  %
%  "Bus x (Bus y ...(Wire z)) = Bus x' (Bus y' ... (Wire z'))" --->     %
%                                                                       %
% |- "Bus x (Bus y ...(Wire z)) = Bus x' (Bus y' ... (Wire z')) =       %
%     ^(conv "x = x'") /\ ^(conv "y = y'") /\ ... /\ ^(conv "z = z'")"  %
%                                                                       %
% Note: the rhs of the expression is simplified to T or F.              %

letrec BUS_EQ_CONV conv tm = 
       let l,r = dest_eq tm in
       if (l = r) then if (is_bus l) then EQT_INTRO (REFL l) else fail else
       if ((is_const (rator l)) & (is_const (rator r))) then
          (REWR_CONV Wire_11 THENC conv) tm else
       if (is_const (rator l)) then
          if (fst(dest_const (rator l))) = `Wire` then
	     let c,ht = strip_comb r in
             let th = (SPEC (rand l)
		(SPECL ht (INST_TYPE[type_of(hd ht),":*"]not_Bus_Wire))) in
  	  MATCH_MP NOT_F th else fail else
       if (is_const (rator r)) then
          if (fst(dest_const (rator r))) = `Wire` then
	     let c,ht = strip_comb l in
             let th = (SPEC (rand r)
		(SPECL ht (INST_TYPE[type_of(hd ht),":*"]not_Bus_Wire))) in
  	  MATCH_MP NOT_F th else fail else
       let cnv1 = (REWR_CONV Bus_11) THENC (RATOR_CONV(RAND_CONV conv)) in
       let cnv2 tm = if (fst(dest_conj tm) = "F") then
       			REWR_CONV lemma2 tm else
		        (REWR_CONV lemma1 THENC BUS_EQ_CONV conv) tm in
       (cnv1 THENC cnv2) tm;;


