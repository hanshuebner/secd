% SECD verification                                                 %
%                                                                   %
% FILE:        val_defs.ml                                          %
%                                                                   %
% DESCRIPTION:  Defines the functions bv, val, Val, and iVal.       %
%                                                                   %
% USES FILES:				                            %
%                                                                   %
% Brian Graham 88.04.21                                             %
%                                                                   %
% Modifications:                                                    %
% 22.02.91 - BtG - moved from dp_types                              %
% 16.04.91 - BtG - updated to HOL12                                 %
% ================================================================= %
new_theory `val_defs`;;

loadt `wordn`;;
load_library `integer`;;
load_theorem `bus`      `bus_axiom`;;

% ================================================================= %
% Data abstraction functions.                                       %
% ================================================================= %
let bv = new_definition
  (`bv`, "bv x = x => 1 | 0");;

let val = new_recursive_definition false bus_axiom `val`
  "(val n (Wire w)    =  n + n + (bv w)          ) /\
   (val n (Bus b bus) =  val (n + n + (bv b)) bus)
  ";;

let Val = new_definition
  (`Val`, "Val = val 0");;

let iVal = new_recursive_definition false bus_axiom `iVal`
  "(iVal (Wire w)    =  neg (INT (bv w))                   ) /\
   (iVal (Bus b bus) =  INT (val 0 bus)  minus
                        INT ((2 EXP (Width bus)) * bv(b))  )
  ";;

timer false;;
close_theory ();;
print_theory `-`;;
