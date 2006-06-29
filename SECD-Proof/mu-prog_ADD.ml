new_theory `mu-prog_ADD`;;
loadt `mu-prog_proof_fcn`;;


let ptheory = `phase_lemmas6`;;
new_parent ptheory;;

let ADD_state,ADD_Next =
 save_seq_proof
   ptheory
   (theorem `mu-prog_init_proofs` `toc_ADD_state`,
    theorem `mu-prog_init_proofs` `toc_ADD_nonmajor`)
   (`ADD_state`,`ADD_Next`);;

timer false;;
close_theory ();;
print_theory `-`;;

