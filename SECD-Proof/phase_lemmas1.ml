% SECD verification                                                 %
%                                                                   %
% FILE:         phase_lemmas1.ml                                    %
%                                                                   %
% DESCRIPTION:  proves phase_lemma_46 through phase_lemma_0         %
%               init, jump table, idle & error loops, startup,      %
%               and top of cycle code.                              %
%                                                                   %
% USES FILES:   SYS_proofs.th, phase_proof_fcn.ml                   %
%                                                                   %
% Brian Graham 90.01.03                                             %
%                                                                   %
% Modifications:                                                    %
% ================================================================= %
new_theory `phase_lemmas1`;;
new_parent `SYS_proofs`;;

loadt `phase_proof_fcn`;;

proof_loop 0 46;;

timer false;;
close_theory();;
print_theory `-`;;
