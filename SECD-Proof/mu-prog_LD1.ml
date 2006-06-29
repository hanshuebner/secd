% SECD verification                                                 %
%                                                                   %
% FILE:         mu-prog_LD1.ml                                      %
%                                                                   %
% DESCRIPTION:  This file proves the theorem pair up to the         %
%               first while loop, proves the execution of the       %
%               while loops, and proves the other microcode         %
%               sequences.  All that should be left to do is        %
%               prove termination and cumulative loop effects,      %
%               and glue the whole thing together.                  %
%                                                                   %
% USES FILES:   mu-prog_proof_fcn.ml, phase_lemmas2.th              %
%                                                                   %
% Brian Graham 90.02.01                                             %
%                                                                   %
% Modifications:                                                    %
%                                                                   %
% ================================================================= %
% ================================================================= %
% The proof of the microprogramming level sequence for the LD       %
% instruction differs from every other instruction because of the   %
% presence of two microcode "while" loops.                          %
%                                                                   %
% The proof strategy is:                                            %
% - prove "_state" and "_Next" theorems up to the first loop.       %
% - prove theorem pair for the loop itself:                         %
%    ... |- (mpc(t+5) = #000111000) /\                              %
%           ...                                                     %
%           (x1(PRE t + 5) = cdr_bits (memory t(x1 (PRE t)))) /\    %
%           ...                                                     %
%           (arg(PRE t + 5) = DEC28(pos_num_of ...)) ...            %
% - do an inductive proof on "n", the number decrimented through    %
%   the loop.  This will give a theorem that looks like:            %
%    ... |- !n.                                                     %
%           (n = pos_num_of(Int_of(atom_bits(memory t(x1(PRE t))))))%
%           ==>                                                     %
%           (mpc(t+(5 * n) = #000111000) /\                         %
%           ...                                                     %
%           (x1(PRE t + (5 * n)) = nth n (cdr_bits o memory t)      %
% 	                               (x1 (PRE t)))) /\            %
%           ...                                                     %
%           (arg(PRE t + (5 * n)) = nth n DEC28 n ...)) ...         %
% - use this to produce the theorem pair at the end of the loop,    %
%   then step to the start of the next loop.                        %
% - repeat the proof steps for the first loop.                      %
% - continue to end of the sequence.                                %
% ================================================================= %
new_theory `mu-prog_LD1`;;
loadt `mu-prog_proof_fcn`;;

let ptheory = `phase_lemmas2`;;
map new_parent 
[  ptheory
; `loop_proofs`
];;

load_theorem `mu-prog_level` `Start_lem`;;

let f = prove_next_step ptheory;;

let base =    (theorem `mu-prog_init_proofs` `toc_LD_state`,
               theorem `mu-prog_init_proofs` `toc_LD_nonmajor`);;

% ================================================================= %
% This is just the first part of the LD sequence, to the start      %
% of the WHILE loop.                                                %
% ================================================================= %
let base = (f (f (f (f (f (f (f (f (f base)))))))));;

save_thm (`base`, uncurry CONJ base);;
% ================================================================= %
% To recover this from storage, :                                   %
%  let base = (\th. CONJUNCT1 th, CONJUNCT2 th)(theorem `-` `base`) %
% ================================================================= %

% ================================================================= %
% snd_thm :                                                         %
% |- !t''. (PRE t) < t'' /\ t'' < t ==> ~is_major_state mpc t''     %
% ================================================================= %
let snd_thm = SPECL ["t:^mtime"; "is_major_state mpc"] Start_lem;;

% ================================================================= %
% The first loop - proven just like a subroutine...                 %
% ================================================================= %
let loop1_state,loop1_nonmajor =
  (f o f o f o f o f)
  (CONJ (ASSUME "(mpc (t:^mtime)) = ^(mk_word9_from_num 56)")
        (ASSUME "(atom_bits(arg(PRE t)) = ZERO28) = F"),
   snd_thm)
 ;;
save_thm (`loop1_state`, loop1_state);;
save_thm (`loop1_nonmajor`, loop1_nonmajor);;

% ================================================================= %
% Step wise, this loop is identical to loop1.                       %
% ================================================================= %
let loop2_state,loop2_nonmajor =
  (f o f o f o f o f)
  (CONJ (ASSUME "(mpc (t:^mtime)) = ^(mk_word9_from_num 72)")
        (ASSUME "(atom_bits(arg(PRE t)) = ZERO28) = F"),
   snd_thm)
 ;;
save_thm (`loop2_state`, loop2_state);;
save_thm (`loop2_nonmajor`, loop2_nonmajor);;

% ================================================================= %
% The first loop exit - proven just like a subroutine...            %
% ================================================================= %
let loop1_exit_state,loop1_exit_nonmajor =
  (f o f o f o f o f o f o f o f o f o f o f o f)
  (CONJ (ASSUME "(mpc (t:^mtime)) = ^(mk_word9_from_num 56)")
        (ASSUME "(atom_bits(arg(PRE t)) = ZERO28) = T"),
   snd_thm)
 ;;
save_thm (`loop1_exit`, reformat loop1_exit_state loop1_exit_nonmajor);;

% ================================================================= %
% The second loop exit - proven just like a subroutine...           %
% ================================================================= %
let loop2_exit_state,loop2_exit_nonmajor =
  stepper f
  (CONJ (ASSUME "(mpc (t:^mtime)) = ^(mk_word9_from_num 72)")
        (ASSUME "(atom_bits(arg(PRE t)) = ZERO28) = T"),
   snd_thm)
 ;;
save_thm (`loop2_exit`, reformat loop2_exit_state loop2_exit_nonmajor);;

% ================================================================= %
% The end of the sequence - proven just like a subroutine...        %
% ================================================================= %
let tail_state,tail_nonmajor =
  stepper f
  (CONJ (ASSUME "(mpc (t:^mtime)) = ^(mk_word9_from_num 81)")
        (REFL "T"),
   snd_thm)
 ;;
save_thm (`tail`, reformat tail_state tail_nonmajor);;

timer false;;
close_theory ();;
print_theory `-`;;
