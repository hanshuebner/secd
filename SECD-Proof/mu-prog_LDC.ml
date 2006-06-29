new_theory `mu-prog_LDC`;;
loadt `mu-prog_proof_fcn`;;


let ptheory = `phase_lemmas2`;;
new_parent ptheory;;

let LDC_state,LDC_Next =
 save_seq_proof
   ptheory
   (theorem `mu-prog_init_proofs` `toc_LDC_state`,
    theorem `mu-prog_init_proofs` `toc_LDC_nonmajor`)
   (`LDC_state`,`LDC_Next`);;


timer false;;
close_theory ();;
print_theory `-`;;
