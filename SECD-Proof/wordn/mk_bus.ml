% FILE		: mk_bus.ml						%
% DESCRIPTION   : Creates the theory "bus.th".			        %
%									%
% READS FILES	: <none>						%
% WRITES FILES	: bus.th						%
%									%
% AUTHOR	: (c) T. Melham						%
% DATE		: 87.09.03						%
% 									%
% NOTE		: PRELIMINARY RELEASE. Please do not distribute.	%
%                 (This was cleared with T. Melham for use with the     %
%                  SECD proof example distribution. - BtG)              %

% Create the new theory							%
new_theory `bus`;;

% define the type :bus							%
let bus_axiom = 
    define_type `bus_axiom` (`bus = Wire * | Bus * bus`);;

% prove induction theorem for bus.					%
let bus_Induct = 
    save_thm (`bus_Induct`,prove_induction_thm bus_axiom);;

% prove cases theorem for bus.						%
let bus_cases = 
    save_thm (`bus_cases`, prove_cases_thm bus_Induct);;

% prove that the constructor Ascii is one-to-one			%
let [Wire_11;Bus_11] =
    let [Wire_11;Bus_11] = 
         (CONJUNCTS (prove_constructors_one_one bus_axiom)) in
          map save_thm [`Wire_11`,Wire_11;`Bus_11`,Bus_11];;

% prove that the constructors Wire and bus are distinct			%
let not_Wire_Bus = 
    save_thm (`not_Wire_Bus`, prove_constructors_distinct bus_axiom);;

let not_Bus_Wire = 
    save_thm (`not_Bus_Wire`, (GEN_ALL(NOT_EQ_SYM(SPEC_ALL not_Wire_Bus))));;

% define a width function on busses.					%
let Width = 
    new_recursive_definition false bus_axiom `Width`
        "(!b. Width (Wire (b:*)) = (SUC 0)) /\
	 (!b bus. Width (Bus b bus) = SUC(Width bus))";;

% Define concatenation for busses					%
let Concat = 
    new_recursive_definition false bus_axiom `Concat`
      "(!b bus. Concat (Wire (b:*)) bus = Bus b bus) /\
       (!b bus1 bus2. Concat (Bus b bus1) bus2 = Bus b (Concat bus1 bus2))";;

% Define "at" for finding the value on a bus at a time t.		%
let at = 
    new_recursive_definition true bus_axiom `at`
      "(!b t. at (Wire b) t = Wire ((b:num->*) t)) /\
       (!b bus t. at (Bus b bus) t = Bus (b t) (at bus t))";;

let Concat_ASSOC = 
    prove_thm
     (`Concat_ASSOC`,
      "!b1:(*)bus. !b2 b3. 
	Concat b1 (Concat b2 b3) = (Concat (Concat b1 b2) b3)",
      INDUCT_THEN bus_Induct ASSUME_TAC THEN ASM_REWRITE_TAC [Concat]);;

let Width_Concat = 
    prove_thm
     (`Width_Concat`,
      "!b1:(*)bus.!b2. Width (Concat b1 b2) = (Width b1) + (Width b2)",
      INDUCT_THEN bus_Induct ASSUME_TAC THEN
      ASM_REWRITE_TAC [Width;Concat;ADD_CLAUSES]);;

let Width_at = 
    prove_thm
    (`Width_at`,
     "!bus:(num->(*))bus. !t. Width (bus at t) = Width bus",
      INDUCT_THEN bus_Induct ASSUME_TAC THEN
      ASM_REWRITE_TAC [Width;at]);;     

let Width_non_zero = 
    prove_thm
    (`Width_non_zero`,
     "!bus:(*)bus. ?n. Width bus = (SUC n)",
      INDUCT_THEN bus_Induct STRIP_ASSUME_TAC THEN
      REWRITE_TAC [Width] THENL
      [EXISTS_TAC "0" THEN REFL_TAC;
       EXISTS_TAC "SUC n" THEN ASM_REWRITE_TAC[]]);;

let Width_Wire = 
    prove_thm
    (`Width_Wire`,
     "!bus:(*)bus. (Width bus = SUC 0) = ?b. bus = Wire b",
     INDUCT_THEN bus_Induct STRIP_ASSUME_TAC THENL
     [REWRITE_TAC [Width] THEN GEN_TAC THEN 
      EXISTS_TAC "x:*" THEN REFL_TAC;
      REWRITE_TAC [Width;INV_SUC_EQ;not_Bus_Wire] THEN
      STRIP_THM_THEN SUBST1_TAC (SPEC "bus:(*)bus" Width_non_zero) THEN
      MATCH_ACCEPT_TAC NOT_SUC]);;

let Width_Bus = 
    prove_thm
    (`Width_Bus`,
     "!bus n. (Width bus = (SUC(SUC n))) = 
	    (?b:*. ?bus'. (Width bus' = (SUC n)) /\ (bus = Bus b bus'))", 
    INDUCT_THEN bus_Induct ASSUME_TAC THENL
    [REWRITE_TAC [Width;INV_SUC_EQ;NOT_EQ_SYM(SPEC_ALL NOT_SUC);
                  not_Wire_Bus];
     REWRITE_TAC [Width;INV_SUC_EQ;Bus_11] THEN
     REPEAT (STRIP_TAC ORELSE EQ_TAC) THENL
     [EXISTS_TAC "x:*" THEN EXISTS_TAC "bus:(*)bus" THEN
      ASM_REWRITE_TAC [];
      ASM_REWRITE_TAC []]]);;


let Hd_bus = 
    new_recursive_definition false bus_axiom `Hd_bus`
      "(!b. Hd_bus (Wire b)  = (b:*)) /\
       (!b bus. Hd_bus (Bus b bus)  = b)";;

let Tl_bus = 
    new_recursive_definition false bus_axiom `Tl_bus`
      "(!b:*. !bus. Tl_bus (Bus b bus)  = bus)";;
