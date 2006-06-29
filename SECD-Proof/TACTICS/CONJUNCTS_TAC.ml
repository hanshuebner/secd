let CONJUNCTS_TAC (asl,t) =
  ACCEPT_TAC (CONJUNCTS_CONV (dest_eq t))(asl,t);;
