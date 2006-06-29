new_theory `mu-prog_LDF`;;
loadt `mu-prog_proof_fcn`;;


let ptheory = `phase_lemmas3`;;
new_parent ptheory;;

let LDF_state,LDF_Next =
 save_seq_proof
   ptheory
   (theorem `mu-prog_init_proofs` `toc_LDF_state`,
    theorem `mu-prog_init_proofs` `toc_LDF_nonmajor`)
   (`LDF_state`,`LDF_Next`);;


timer false;;
close_theory ();;
print_theory `-`;;

