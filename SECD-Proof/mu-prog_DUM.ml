new_theory `mu-prog_DUM`;;
loadt `mu-prog_proof_fcn`;;


let ptheory = `phase_lemmas4`;;
new_parent ptheory;;

let DUM_state,DUM_Next =
 save_seq_proof
   ptheory
   (theorem `mu-prog_init_proofs` `toc_DUM_state`,
    theorem `mu-prog_init_proofs` `toc_DUM_nonmajor`)
   (`DUM_state`,`DUM_Next`);;

timer false;;
close_theory ();;
print_theory `-`;;

