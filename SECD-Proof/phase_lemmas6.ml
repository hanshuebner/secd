% SECD verification                                                 %
%                                                                   %
% FILE:         phase_lemmas6.ml                                    %
%                                                                   %
% DESCRIPTION:  proves phase_lemma_256 through phase_lemma_308      %
%               CONS & EQ & ADD & SUB & MUL & DIV & REM &           %
%                  LEQ & STOP instructions                          %
%                                                                   %
% USES FILES:   SYS_proofs.th, phase_proof_fcn.ml                   %
%                                                                   %
% Brian Graham 90.01.03                                             %
%                                                                   %
% Modifications:                                                    %
%                                                                   %
% ================================================================= %
new_theory `phase_lemmas6`;;
new_parent `SYS_proofs`;;

loadt `phase_proof_fcn`;;

proof_loop 256 307;;

% ================================================================= %
% Separate treatment of the theorem for mpc = 308 is required       %
% because the microcode for that address is:                        %
% 		rs wmem			                            %
% Only the cdr field of the 32 bit memory record is written.        %
% The value in the other bits is nondeterminable.  We overcome      %
% this in the singular case where this condition arises (outside    %
% of the gc routines where it may occur again.) by describing       %
% only partly the value returned by the memory from this address.   %
% ================================================================= %
let initial_phase_lemma_308 = phase_proof_fcn (mk_word9_from_num 308);;

% ================================================================= %
% phase_lemma_308 =                                                 %
% .. |- (mpc t = #100110100) ==>                                    %
%       (mpc(SUC t) = #000010110) /\                                %
%       (s0(SUC t) = s0 t) /\                                       %
%       (s1(SUC t) = s1 t) /\                                       %
%       (s2(SUC t) = s2 t) /\                                       %
%       (s3(SUC t) = s3 t) /\                                       %
%       (!a.                                                        %
%         ((a = mar_pins(PRE t)) =>                                 %
%          (cdr_bits(memory(SUC t)a) = s'(PRE t)) |                 %
%          (memory(SUC t)a = memory t a))) /\                       %
%       (rmem_pin t = F) /\                                         %
%       (cdr_bits(bus_pins t) = s'(PRE t)) /\                       %
%       (buf1 t = buf1(PRE t)) /\                                   %
%       (buf2 t = buf2(PRE t)) /\                                   %
%       (mar_pins t = mar_pins(PRE t)) /\                           %
%       (s' t = s'(PRE t)) /\                                       %
%       (e' t = e'(PRE t)) /\                                       %
%       (c' t = c'(PRE t)) /\                                       %
%       (d' t = d'(PRE t)) /\                                       %
%       (free t = free(PRE t)) /\                                   %
%       (x1 t = x1(PRE t)) /\                                       %
%       (x2 t = x2(PRE t)) /\                                       %
%       (car t = car(PRE t)) /\                                     %
%       (arg t = arg(PRE t)) /\                                     %
%       (parent t = parent(PRE t)) /\                               %
%       (root t = root(PRE t)) /\                                   %
%       (y1 t = y1(PRE t)) /\                                       %
%       (y2 t = y2(PRE t)) /\                                       %
%       (write_bit_pin t = F) /\                                    %
%       (flag0_pin t = F) /\                                        %
%       (flag1_pin t = F)                                           %
% ================================================================= %
let phase_lemma_308 = TAC_PROOF
((hyp initial_phase_lemma_308,
  "(mpc t = #100110100) ==>
       (mpc(SUC t) = #000010110) /\
       ((s0:^w9_mvec)(SUC t) = s0 t) /\
       ((s1:^w9_mvec)(SUC t) = s1 t) /\
       ((s2:^w9_mvec)(SUC t) = s2 t) /\
       ((s3:^w9_mvec)(SUC t) = s3 t) /\
       (!a. (a = mar_pins(PRE t))
             => (cdr_bits (memory (SUC t) a) = s(PRE t))
              | (memory (SUC t) a = memory t a)) /\
       (rmem_pin t = F) /\
       (cdr_bits (bus_pins t) = s(PRE t)) /\
       ((buf1:^w32_mvec) t = buf1(PRE t)) /\
       ((buf2:^w32_mvec) t = buf2(PRE t)) /\
       ((mar_pins:^w14_mvec) t = mar_pins(PRE t)) /\
       ((s:^w14_mvec) t = s(PRE t)) /\
       ((e:^w14_mvec) t = e(PRE t)) /\
       ((c:^w14_mvec) t = c(PRE t)) /\
       ((d:^w14_mvec) t = d(PRE t)) /\
       ((free:^w14_mvec) t = free(PRE t)) /\
       ((x1:^w14_mvec) t = x1(PRE t)) /\
       ((x2:^w14_mvec) t = x2(PRE t)) /\
       ((car:^w14_mvec) t = car(PRE t)) /\
       ((arg:^w32_mvec) t = arg(PRE t)) /\
       ((parent:^w14_mvec) t = parent(PRE t)) /\
       ((root:^w14_mvec) t = root(PRE t)) /\
       ((y1:^w14_mvec) t = y1(PRE t)) /\
       ((y2:^w14_mvec) t = y2(PRE t)) /\
       (write_bit_pin t = F) /\
       (flag0_pin t = F) /\
       (flag1_pin t = F)"),
  STRIP_TAC
  THEN IMP_RES_THEN STRIP_ASSUME_TAC initial_phase_lemma_308
  THEN poart[]
  THEN rt[]
  THEN art[definition `rt_SYS` `Store14`]
  THEN in_conv_tac BETA_CONV
  THEN GEN_TAC
  THEN COND_CASES_TAC
  THEN rt[]
  THEN part[]
  THEN REFL_TAC);;

timer false;;

save_thm (`phase_lemma_308`, phase_lemma_308);
tty_write(`phase_lemma_308 is proven (--> 308)
`);;

close_theory();;
print_theory `-`;;
