new_theory `mu-prog_CDR`;;
loadt `mu-prog_proof_fcn`;;


let ptheory = `phase_lemmas5`;;
new_parent ptheory;;

let CDR_state,CDR_Next =
 save_seq_proof
   ptheory
   (theorem `mu-prog_init_proofs` `toc_CDR_state`,
    theorem `mu-prog_init_proofs` `toc_CDR_nonmajor`)
   (`CDR_state`,`CDR_Next`);;

timer false;;
close_theory ();;
print_theory `-`;;

