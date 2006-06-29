new_theory `mu-prog_STOP`;;

let ptheory = `phase_lemmas6`;;
new_parent ptheory;;

loadt `mu-prog_proof_fcn`;;
 
let STOP_state,STOP_Next =
 save_seq_proof
   ptheory
   (theorem `mu-prog_init_proofs` `toc_STOP_state`,
    theorem `mu-prog_init_proofs` `toc_STOP_nonmajor`)
   (`STOP_state`,`STOP_Next`);;

timer false;;
close_theory ();;
print_theory `-`;;

