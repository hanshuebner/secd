% SECD verification                                                 %
%                                                                   %
% FILE:         phase_lemmas4.ml                                    %
%                                                                   %
% DESCRIPTION:  proves phase_lemma_156 through phase_lemma_219      %
%               DUM & RAP & SEL instructions                        %
%                                                                   %
% USES FILES:   SYS_proofs.th, phase_proof_fcn.ml                   %
%                                                                   %
% Brian Graham 90.01.03                                             %
%                                                                   %
% Modifications:                                                    %
%                                                                   %
% ================================================================= %
new_theory `phase_lemmas4`;;
new_parent `SYS_proofs`;;

loadt `phase_proof_fcn`;;

proof_loop 156 219;;

timer false;;
close_theory();;
print_theory `-`;;
