% SECD verification                                               %
%                                                                 %
% FILE:         phase_lemmas7.ml                                  %
%                                                                 %
% DESCRIPTION:  proves phase_lemma_309 through phase_lemma_336    %
%               PreOperation, PostOperation, Consx1x2, &          %
%               Numberbuf routines                                %
%                                                                 %
% USES FILES:   SYS_proofs.th, phase_proof_fcn.ml                 %
%                                                                 %
% Brian Graham 90.01.03                                           %
%                                                                 %
% Modifications:                                                  %
% 90.02.22 - BtG - started from 309 instead of 308.               %
%=================================================================%
new_theory `phase_lemmas7`;;
new_parent `SYS_proofs`;;

loadt `phase_proof_fcn`;;

proof_loop 309 336;;

timer false;;
close_theory();;
print_theory `-`;;
