new_theory `mu-prog_CONS`;;
loadt `mu-prog_proof_fcn`;;


let ptheory = `phase_lemmas6`;;
new_parent ptheory;;

let CONS_state,CONS_Next =
 save_seq_proof
   ptheory
   (theorem `mu-prog_init_proofs` `toc_CONS_state`,
    theorem `mu-prog_init_proofs` `toc_CONS_nonmajor`)
   (`CONS_state`,`CONS_Next`);;

timer false;;
close_theory ();;
print_theory `-`;;

