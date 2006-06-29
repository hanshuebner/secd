new_theory `mu-prog_LEQ`;;
loadt `mu-prog_proof_fcn`;;


let ptheory = `phase_lemmas6`;;
new_parent ptheory;;

let LEQ_state,LEQ_Next =
 save_seq_proof
   ptheory
   (theorem `mu-prog_init_proofs` `toc_LEQ_state`,
    theorem `mu-prog_init_proofs` `toc_LEQ_nonmajor`)
   (`LEQ_state`,`LEQ_Next`);;

close_theory ();;

print_theory `-`;;

