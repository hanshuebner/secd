new_theory `mu-prog_RTN`;;
loadt `mu-prog_proof_fcn`;;


let ptheory = `phase_lemmas3`;;
new_parent ptheory;;

let RTN_state,RTN_Next =
 save_seq_proof
   ptheory
   (theorem `mu-prog_init_proofs` `toc_RTN_state`,
    theorem `mu-prog_init_proofs` `toc_RTN_nonmajor`)
   (`RTN_state`,`RTN_Next`);;

timer false;;
close_theory ();;
print_theory `-`;;

