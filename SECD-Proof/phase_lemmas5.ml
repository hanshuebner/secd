% SECD verification                                                 %
%                                                                   %
% FILE:         phase_lemmas5.ml                                    %
%                                                                   %
% DESCRIPTION:  proves phase_lemma_220 through phase_lemma_255      %
%               Join & CAR & CDR & ATOM instructions                %
%                                                                   %
% USES FILES:   SYS_proofs.th, phase_proof_fcn.ml                   %
%                                                                   %
% Brian Graham 90.01.03                                             %
%                                                                   %
% Modifications:                                                    %
%                                                                   %
% ================================================================= %
new_theory `phase_lemmas5`;;
new_parent `SYS_proofs`;;

loadt `phase_proof_fcn`;;

proof_loop 220 255;;

timer false;;
close_theory();;
print_theory `-`;;
