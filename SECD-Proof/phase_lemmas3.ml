% SECD verification                                                 %
%                                                                   %
% FILE:         phase_lemmas3.ml                                    %
%                                                                   %
% DESCRIPTION:  proves phase_lemma_97 through phase_lemma_155       %
%               LDF & AP & RTN instructions                         %
%                                                                   %
% USES FILES:   SYS_proofs.th, phase_proof_fcn.ml                   %
%                                                                   %
% Brian Graham 90.01.03                                             %
%                                                                   %
% Modifications:                                                    %
%                                                                   %
% ================================================================= %
new_theory `phase_lemmas3`;;
new_parent `SYS_proofs`;;

loadt `phase_proof_fcn`;;

proof_loop 97 155;;

timer false;;
close_theory();;
print_theory `-`;;
