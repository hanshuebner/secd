% SECD verification                                                 %
%                                                                   %
% FILE:         phase_lemmas2.ml                                    %
%                                                                   %
% DESCRIPTION:  proves phase_lemma_96 through phase_lemma_47        %
%               LD & LDC instructions                               %
%                                                                   %
% USES FILES:   SYS_proofs.th, phase_proof_fcn.ml                   %
%                                                                   %
% Brian Graham 90.01.03                                             %
%                                                                   %
% Modifications:                                                    %
% ================================================================= %
new_theory `phase_lemmas2`;;
new_parent `SYS_proofs`;;

loadt `phase_proof_fcn`;;

proof_loop 47 96;;

timer false;;
close_theory();;
print_theory `-`;;
