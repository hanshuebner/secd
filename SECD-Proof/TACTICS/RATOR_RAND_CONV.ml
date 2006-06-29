%----------------------------------------------------------------
|   RAND_CONV conv "t1 t2" applies conv to t2
----------------------------------------------------------------%
let RAND_CONV conv tm =
 (let rator,rand = dest_comb tm
  in
  MK_COMB (REFL rator, conv rand)
 ) ? failwith `RAND_CONV`;;


%----------------------------------------------------------------
|   RATOR_CONV conv "t1 t2" applies conv to t1
----------------------------------------------------------------%
let RATOR_CONV conv tm =
 (let rator,rand = dest_comb tm
  in
  MK_COMB (conv rator, REFL rand)
 ) ? failwith `RATOR_CONV`;;


%----------------------------------------------------------------
|  examples in using these...
----------------------------------------------------------------%
let LHS_CONV = RATOR_CONV o RAND_CONV;;

let RHS_CONV = RAND_CONV;;

