% SECD verification                                                 %
%                                                                   %
% FILE: rt_PADS.ml                                                  %
%                                                                   %
% DESCRIPTION: This is a higher level view of the pads frame,       %
%              much more of a register transfer view of things,     %
%              mainly because of the higher level data              %
%              abstraction used.                                    %
%                                                                   %
% USES FILES:  dp_types.th                                          %
%                                                                   %
% Brian Graham 88.05.12                                             %
%                                                                   %
% Modifications:                                                    %
% 88.06.23 - Changed the idle and error signals to 2 flag signals   %
% 16.04.91 - BtG - updated to HOL12                                 %
% ================================================================= %
new_theory `rt_PADS`;;

loadt `wordn`;;

new_parent `dp_types`;;

load_library `unwind`;;
% ================================================================= %
let mtime = ":num";;
let msig = ":^mtime->bool"
and w14_mvec = ":^mtime->word14"
and w32_mvec = ":^mtime->word32";;
% ================================================================= %
timer true;;
% ============================================================ %
% We treat inputs and outputs as high level signals.           %
%                                                              %
%   note that bidir is asserted LOW:                           %
%     (bidir = HI) => read from pins - read memory mode        %
%     (bidir = LO) => write to memory mode                     %
%                                                              %
% The bus connections are :                                    %
%                  ___________                                 %
% bus_bits ------>|           |                                %
%                 | bidir pad |<------> bus_pins               %
% mem_bits <------|___________|                                %
%                       o                                      %
%                       |                                      %
%                     bidir                                    %
%                                                              %
% ie. mem_bits get the memory value from bus_pins on a rmem.   %
% ============================================================ %
let rt_PF = new_definition
  (`rt_PF`,
   "! (button:^msig)
      (flag0:^msig)         (flag1:^msig)
      (bidir:^msig)         (write_bit:^msig)    (rmem:^msig)
      (bus_bits:^w32_mvec)  (mem_bits:^w32_mvec) (mar_bits:^w14_mvec)

      (button_pin:^msig)
      (flag0_pin:^msig)     (flag1_pin:^msig)
      (write_bit_pin:^msig) (rmem_pin:^msig)
      (bus_pins:^w32_mvec)  (mar_pins:^w14_mvec) 
    .
    rt_PF                                 % chip side %
      button
      flag0         flag1
      bidir         write_bit   rmem
      bus_bits      mem_bits    mar_bits
                                           % pin side %
      button_pin
      flag0_pin     flag1_pin
      write_bit_pin rmem_pin
      bus_pins      mar_pins
     =
    !t:^mtime.
     (button t             = button_pin t) /\
     (flag0_pin t          = flag0 t)      /\
     (flag1_pin t          = flag1 t)      /\
     (write_bit_pin t      = write_bit t)  /\
     (rmem_pin t           = rmem t)       /\
     (bidir t => (mem_bits t = bus_pins t)       % read from memory %
               | (bus_pins t = bus_bits t)) /\   % write to memory  %
     (mar_pins t           = mar_bits t) 
   ");;

close_theory();;

% ================================================================= %
% The following lemma reorders the equations and moves in the       %
% quantified "t", for use in eliminating quantified variables at    %
% a higher level in the proof.                                      %
% ================================================================= %
%<
let rt_PF_lemma = prove_thm
(`rt_PF_lemma`,
 "rt_PF                                 % chip side %
      button
      flag0         flag1
      bidir         write_bit   rmem
      bus_bits      mem_bits    mar_bits
                                           % pin side %
      button_pin
      flag0_pin     flag1_pin
      write_bit_pin rmem_pin
      bus_pins      mar_pins
     =
     (!t:^mtime. button t               = button_pin t)     /\
     (!t:^mtime. flag0 t                = flag0_pin t)      /\
     (!t:^mtime. flag1 t                = flag1_pin t)      /\
     (!t:^mtime. write_bit t            = write_bit_pin t)  /\
     (!t:^mtime. rmem t                 = rmem_pin t)       /\
     (!t:^mtime. bidir t => (mem_bits t = bus_pins t) |
                            (bus_pins t = bus_bits t))     /\
     (!t:^mtime. mar_bits t             = mar_pins t) ",
  port[rt_PF]
  THEN in_conv_tac UNWINDF
  THEN EQ_TAC
  THEN DISCH_THEN (rt o CONJUNCTS)
  );;
>%


% ================================================================= %
% ================================================================= %
let EQ_EXT_EQ = TAC_PROOF
(([], "!(f:* -> **) (g:* -> **).
    (!(x:*). (f:* -> **) x = (g:* -> **) x) = (f = g)"),
 REPEAT GEN_TAC
 THEN EQ_TAC
 THENL
 [ ACCEPT_TAC (SPEC_ALL EQ_EXT)
 ; DISCH_THEN (\th. rt[th])
 ]);;

% ================================================================= %
% This version should make unwinding simpler yet, by eliminating    %
% "t" by use of EXTensionality.                                     %
% ================================================================= %
let PF_lemma = prove_thm
(`PF_lemma`, 
     "rt_PF                                 % chip side %
      button
      flag0         flag1
      bidir         write_bit   rmem
      bus_bits      mem_bits    mar_bits
                                           % pin side %
      button_pin
      flag0_pin     flag1_pin
      write_bit_pin rmem_pin
      bus_pins      mar_pins
     =
     (!t:^mtime.
         bidir t => (mem_bits t = bus_pins t) |
                    (bus_pins t = bus_bits t)) /\
      (button               = button_pin)      /\
      (flag0                = flag0_pin)       /\
      (flag1                = flag1_pin)       /\
      (write_bit            = write_bit_pin)   /\
      (rmem                 = rmem_pin)        /\
      (mar_bits             = mar_pins)        " ,
    SUBST1_TAC (SPEC_ALL rt_PF)
    THEN re_conv_tac FORALL_AND_CONV
    THEN port[EQ_EXT_EQ]
    THEN EQ_TAC
    THEN DISCH_THEN (rt o CONJUNCTS)
    );;

timer false;;
print_theory `-`;;
