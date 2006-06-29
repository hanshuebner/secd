new_theory `mu-prog_ATOM`;;
loadt `mu-prog_proof_fcn`;;


let ptheory = `phase_lemmas5`;;
new_parent ptheory;;

let ATOM_state,ATOM_Next =
 save_seq_proof
   ptheory
   (theorem `mu-prog_init_proofs` `toc_ATOM_state`,
    theorem `mu-prog_init_proofs` `toc_ATOM_nonmajor`)
   (`ATOM_state`,`ATOM_Next`);;

timer false;;
close_theory ();;
print_theory `-`;;

