new_theory `mu-prog_SEL`;;
loadt `mu-prog_proof_fcn`;;


let ptheory = `phase_lemmas4`;;
new_parent ptheory;;

let SEL_state,SEL_Next =
 save_seq_proof
   ptheory
   (theorem `mu-prog_init_proofs` `toc_SEL_state`,
    theorem `mu-prog_init_proofs` `toc_SEL_nonmajor`)
   (`SEL_state`,`SEL_Next`);;

timer false;;
close_theory ();;
print_theory `-`;;

