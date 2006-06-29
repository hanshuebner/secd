% ================================================================= %
% Works for terms with existential quantifier as first or           %
% second term in a conjunction.                                     %
% ================================================================= %
let MOVE_EXISTS_OUT_CONV t =
 (let t1,t2 = dest_conj t
 in
 is_exists t2 =>
    RIGHT_AND_EXISTS_CONV t |
    (let thm1 = RIGHT_AND_EXISTS_CONV (mk_conj (t2,t1))
     in
     let v,t3,t4 = ((I # dest_conj) o dest_exists o snd o dest_eq o concl) thm1
     in
     SUBST [SPECL [t2;t1]CONJ_SYM,"x:bool" ;
            (MK_EXISTS o (GEN v) o (SPECL [t3;t4])) CONJ_SYM,"y:bool"
           ]
           "x:bool=y"
           thm1)) ? failwith `MOVE_EXISTS_OUT_CONV`;;


let mmeoc = MOVE_EXISTS_OUT_CONV;;
