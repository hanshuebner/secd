let load_all_axioms theory  =
    map (load_axiom theory) (map fst (axioms theory));;

let load_all_definitions theory  =
    map (load_definition theory) (map fst (definitions theory));;

let load_all_theorems theory  =
    map (load_theorem theory) (map fst (theorems theory));;

let load_all theory =
    (load_all_axioms theory ;
     load_all_definitions theory ;
     load_all_theorems theory
     );;

% I think this makes redundant definitions, and this can
be simply defined by:

let load_all theory =
    (load_theorems theory;
		   load_definitions theory;
		   load_axioms theory);;

%
