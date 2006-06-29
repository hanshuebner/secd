% SECD verification                                                 %
%                                                                   %
% FILE:        cu_types.ml                                          %
%                                                                   %
% DESCRIPTION:  Declares the wordn types used by the control unit.  %
%               Also defines field selectors, and an increment      %
%               operation.                                          %
%                                                                   %
% USES FILES:   wordn library                                       %
%                                                                   %
% Brian Graham 88.04.21                                             %
%                                                                   %
% Modifications:                                                    %
% 15.04.91 - BtG - updated to HOL12                                 %
% ================================================================= %
new_theory `cu_types`;;

loadt `wordn`;;
load_theorem `bus` `bus_axiom`;;

timer true;;
% ================================================================= %
map (declare_wordn_type true)
     [ 4; % test field of instruction %
       5; % read, write fields %
       9; % mpc width %
       27 % instruction width %
     ];;

% ================================================================= %
% Field selector functions:                                         %
% Note that wordn maps onto :(bool)bus, not :(num->bool)bus.        %
% ================================================================= %
let w27 =
"Word27 (Bus b27 (Bus b26 (Bus b25 (Bus b24 (Bus b23 (Bus b22
        (Bus b21 (Bus b20 (Bus b19 (Bus b18 (Bus b17 (Bus b16
        (Bus b15 (Bus b14 (Bus b13 (Bus b12 (Bus b11 (Bus b10
        (Bus b9  (Bus b8  (Bus b7  (Bus b6  (Bus b5  (Bus b4 
        (Bus b3  (Bus b2  (Wire (b1:bool))))))))))))))))))))))))))))";;

let Word27 = theorem `-` `Word27`;;

let Read_field = new_recursive_definition false Word27 `Read_field`
   "Read_field ^w27 =
      Word5 (Bus b5 (Bus b4 (Bus b3 (Bus b2 (Wire b1)))))"
 ;;

let Write_field = new_recursive_definition false Word27 `Write_field`
   "Write_field ^w27 =
      Word5 (Bus b10 (Bus b9 (Bus b8 (Bus b7 (Wire b6)))))"
   ;;

let Alu_field = new_recursive_definition false Word27 `Alu_field`
   "Alu_field ^w27 =
      Word4 (Bus b14 (Bus b13 (Bus b12 (Wire b11))))"
   ;;

let Test_field = new_recursive_definition false Word27
   `Test_field`
   "Test_field ^w27 =
      Word4 (Bus b18 (Bus b17 (Bus b16 (Wire b15))))"
   ;;

let A_field = new_recursive_definition false Word27 `A_field`
   "A_field ^w27 =
      Word9 (Bus b27 (Bus b26 (Bus b25 (Bus b24 (Bus b23 (Bus b22
            (Bus b21 (Bus b20 (Wire b19)))))))))"
   ;;

% ================================================================= %
% Define an increment function on objects of type :word9.           %
% This is done by tail recursion on buses, with the Inc_9           %
% function converting to from and back to the :word9 type,          %
% as well as selecting the bus returned by inc.                     %
%                                                                   %
% This is an implementation sort of definition, but is sensible     %
% here since the "meaning" is not important, only the value, as     %
% an argument to the ROM defintion.                                 %
% ================================================================= %
let inc = new_recursive_definition false bus_axiom
`inc` "(inc (Wire b) = (Wire (~b),b)) /\ (inc (Bus b bus) = (let
(bs,fg) = (inc bus) in (Bus (fg => ~b | b) bs, (fg /\ b))) )";;

let Inc9 = new_definition
  (`Inc9`,
   "Inc9 = Word9 o FST o inc o Bits9"
  );;

timer false;;
close_theory ();;
print_theory `-`;;

%< These potentially useful theorems are not in fact used ...

let Bits4_Width = prove_thm
(`Bits4_Width`,
 "!b. Width(Bits4 (b:word4)) = 4",
 INDUCT_THEN (theorem `cu_types` `Word4_Induct`) ASSUME_TAC
 THEN REPEAT GEN_TAC 
 THEN port[theorem `cu_types` `Bits4_Word4`]
 THEN prt[definition `bus` `Width`]
 THEN re_conv_tac num_CONV
 THEN REFL_TAC
);;

let Bits5_Width = prove_thm
(`Bits5_Width`,
 "!b. Width(Bits5 (b:word5)) = 5",
 INDUCT_THEN (theorem `cu_types` `Word5_Induct`) ASSUME_TAC
 THEN REPEAT GEN_TAC 
 THEN port[theorem `cu_types` `Bits5_Word5`]
 THEN prt[definition `bus` `Width`]
 THEN re_conv_tac num_CONV
 THEN REFL_TAC
);;

let Bits9_Width = prove_thm
(`Bits9_Width`,
 "!b. Width(Bits9 (b:word9)) = 9",
 INDUCT_THEN (theorem `cu_types` `Word9_Induct`) ASSUME_TAC
 THEN REPEAT GEN_TAC 
 THEN port[theorem `cu_types` `Bits9_Word9`]
 THEN prt[definition `bus` `Width`]
 THEN re_conv_tac num_CONV
 THEN REFL_TAC
);;

let Bits27_Width = prove_thm
(`Bits27_Width`,
 "!b. Width(Bits27 (b:word27)) = 27",
 INDUCT_THEN (theorem `cu_types` `Word27_Induct`) ASSUME_TAC
 THEN REPEAT GEN_TAC 
 THEN port[theorem `cu_types` `Bits27_Word27`]
 THEN prt[definition `bus` `Width`]
 THEN re_conv_tac num_CONV
 THEN REFL_TAC
);;
>%


