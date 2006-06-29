new_theory `mu-prog_JOIN`;;
loadt `mu-prog_proof_fcn`;;


let ptheory = `phase_lemmas5`;;
new_parent ptheory;;

let JOIN_state,JOIN_Next =
 save_seq_proof
   ptheory
   (theorem `mu-prog_init_proofs` `toc_JOIN_state`,
    theorem `mu-prog_init_proofs` `toc_JOIN_nonmajor`)
   (`JOIN_state`,`JOIN_Next`);;

timer false;;
close_theory ();;
print_theory `-`;;

