new_theory `mu-prog_SUB`;;
loadt `mu-prog_proof_fcn`;;

let ptheory = `phase_lemmas6`;;
new_parent ptheory;;

let SUB_state,SUB_Next =
 save_seq_proof
   ptheory
   (theorem `mu-prog_init_proofs` `toc_SUB_state`,
    theorem `mu-prog_init_proofs` `toc_SUB_nonmajor`)
   (`SUB_state`,`SUB_Next`);;

timer false;;
close_theory ();;
print_theory `-`;;

