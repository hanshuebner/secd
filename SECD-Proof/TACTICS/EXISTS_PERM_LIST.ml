%------------------------------------------------------------------------
| FILE		: EXISTS_PERM_LIST.ml
|
| DESCRIPTION	: A set containing a derived rule, a conversion and
|                 a tactic which allows you to change the order of
|                 any number of existentially quantified variables.
|
|                 This rule also allows you to discard any existentially
|                 quantified variables which are not present in the term.
|
|                 [any order containing v1 v2 v3 ... vn]
|                 ?v1 v2 v3 ... vn.  tm
|                 -----------------------------------
|                 ? {new ordered v1 v2 v3 ... vn}. tm
|
| READS FILES   : <none>
| 
| WRITES FILES  : <none>
| 
| DATE          : 28.Jun.89
| AUTHOR        : I. S. Dhingra
------------------------------------------------------------------------%

let EXISTS_PERM_LIST new_l th =
    let old_l,tm = strip_exists (concl th)
    in
    letrec build_exists l thm =      % note: builds exists in rev order%
        (null l) => thm
                  | build_exists
                      (tl l)
                      (EXISTS ("?^(hd l). ^(concl thm)", (hd l)) thm)
    in
    let new_thm = build_exists (rev new_l) (ASSUME tm)
    in
    letrec build_result l old_tm old_thm new_thm =
        (length l=0)=>MP (DISCH (concl old_thm) new_thm) old_thm |
        (length l=1)=>CHOOSE ((hd l), old_thm) new_thm    |
                      let tm' = mk_exists ((hd l), old_tm)
                      in
                      build_result (tl l)
                                   tm'
                                   old_thm 
                                   (CHOOSE ((hd l),(ASSUME tm')) new_thm)
    in
    build_result (rev old_l) tm th new_thm;;

%------------------------------------------------------------------------
|   #ASSUME "? a b c d e. a/\b/\c/\d/\e";;
|   |- ?a b c d e f g. a /\ b /\ c /\ d /\ e
|   
|   #EXISTS_PERM_LIST ["e:bool"; "c:bool"; "a:bool"; "d:bool"; "b:bool"] it;;
|   . |- ?e c a d b. a /\ b /\ c /\ d /\ e
|   
|   #ASSUME "?a b c : num.  a = SUC b";;
|   . |- ?a b c. a = SUC b
|   
|   #EXISTS_PERM_LIST ["b:num"; "a:num"] it;;
|   . |- ?b a. a = SUC b
|   
|   #EXISTS_PERM_LIST ["b:num"] it;;
|   evaluation failed     CHOOSE 
|   
|   #
------------------------------------------------------------------------%


let EXISTS_PERM_LIST_CONV l t =
  (let th1 = EXISTS_PERM_LIST l (ASSUME t)
   in
   let l' = (fst o strip_exists) t
   in
   let t' = concl th1
   in
   let th2 = EXISTS_PERM_LIST l' (ASSUME t')
   in
   IMP_ANTISYM_RULE (DISCH t th1) (DISCH t' th2)
  ) ? failwith `EXISTS_PERM_LIST_CONV`;;

let EXISTS_PERM_LIST_TAC l = CONV_TAC (ONCE_DEPTH_CONV (EXISTS_PERM_LIST_CONV l));;
