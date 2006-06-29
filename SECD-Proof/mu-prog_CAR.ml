new_theory `mu-prog_CAR`;;
loadt `mu-prog_proof_fcn`;;


let ptheory = `phase_lemmas5`;;
new_parent ptheory;;

let CAR_state,CAR_Next =
 save_seq_proof
   ptheory
   (theorem `mu-prog_init_proofs` `toc_CAR_state`,
    theorem `mu-prog_init_proofs` `toc_CAR_nonmajor`)
   (`CAR_state`,`CAR_Next`);;

timer false;;
close_theory ();;
print_theory `-`;;

