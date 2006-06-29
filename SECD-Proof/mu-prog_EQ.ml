new_theory `mu-prog_EQ`;;
loadt `mu-prog_proof_fcn`;;


let ptheory = `phase_lemmas6`;;
new_parent ptheory;;

let EQ_state,EQ_Next =
 save_seq_proof
   ptheory
   (theorem `mu-prog_init_proofs` `toc_EQ_state`,
    theorem `mu-prog_init_proofs` `toc_EQ_nonmajor`)
   (`EQ_state`,`EQ_Next`);;

timer false;;
close_theory ();;
print_theory `-`;;

