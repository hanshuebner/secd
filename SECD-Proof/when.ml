%------------------------------------------------------------------------
| FILE		: when.ml
| 
| DESCRIPTION	: Defines the predicates `Next`, `Inf`, `IsTimeOf`
|		  and `TimeOf` and derives several major theorems
|		  which provide a basis for temporal abstraction.
|
|		  These predicates and theorems are taken from
|		  T.Melham's paper, "Abstraction Mechanisms for
|		  Hardware Verification", Hardware Verification
|		  Workshop, University of Calgary, January 1987.
|
| Modified:
| 06.08.91 - BtG - updated to HOL2                                
------------------------------------------------------------------------%

new_theory `when`;;

let Next = new_definition
  (`Next`, 
   "Next t1 t2 f  =  (t1<t2)  /\
                     ( f t2)  /\
                 !t. (t1<t )  /\  (t<t2)  ==>  ~f t"
  );;

let IsTimeOf = new_prim_rec_definition
  (`IsTimeOf`,
  "(IsTimeOf      0  f t  =  f t  /\  !t'.  (t'<t) ==> ~f t') /\
   (IsTimeOf (SUC n) f t  =  ?t'.  IsTimeOf n f t' /\
                                   Next t' t f              )"
  );;

let TimeOf = new_definition
  (`TimeOf`,
   "TimeOf f n  =  @t. IsTimeOf n f t"
  );;

let when = new_infix_definition
  (`when`,
   "when (s:num->*) (p:num->bool)  =  \n. s (TimeOf p n)"
  );;

let Inf = new_definition
  (`Inf`,
   "Inf f =  !t. ?t'.  (t<t') /\ (f t')"
  );;

%------------------------------------------------------------------------
| Define "LEAST P" to represent that P has a smallest element.
------------------------------------------------------------------------%
let LEAST = new_definition
  (`LEAST`,
   "LEAST P  =  ?x. P x  /\  (!y. y<x ==> ~P y)"
 );;

close_theory();;
timer true;;
%------------------------------------------------------------------------
|  The first assumption which matches the term  tm  is undischarged
|  (c) ISD--Aug.1989.
------------------------------------------------------------------------%
let MATCH_UNDISCH_TAC tm =
  (FIRST_ASSUM \th. UNDISCH_TAC (if  (can (match tm) (concl th))
                                then (concl th)
                                else fail
                               ) ? NO_TAC
  )
  ORELSE FAIL_TAC `MATCH_UNDISCH_TAC`;;

%------------------------------------------------------------------------
|   wop = |- !P.  (?n. P n)  ==>  LEAST P
------------------------------------------------------------------------%
let wop = prove_thm
  (`wop`,
   "!P. (?n. P n)  ==>  LEAST P",
   REWRITE_TAC [WOP; LEAST]
  );;

%------------------------------------------------------------------------
|   Inf_EXISTS = |- !f.  Inf f  ==>  ?n.  f n
------------------------------------------------------------------------%
let Inf_EXISTS = prove_thm
  (`Inf_EXISTS`,
   "!f.  Inf f  ==>  ?n.  f n",
   PURE_REWRITE_TAC [Inf]
   THEN REPEAT STRIP_TAC
   THEN FIRST_ASSUM (STRIP_ASSUME_TAC  o (SPEC "t:num"))
   THEN EXISTS_TAC "t':num"
   THEN FIRST_ASSUM ACCEPT_TAC
  );;

%------------------------------------------------------------------------
|   Inf_LEAST = |- !f.  Inf f  ==>  LEAST f
------------------------------------------------------------------------%
let Inf_LEAST = prove_thm
  (`Inf_LEAST`,
   "!f.  Inf f  ==>  LEAST f",
   REPEAT STRIP_TAC
   THEN IMP_RES_TAC Inf_EXISTS
   THEN IMP_RES_TAC wop
  );;

%------------------------------------------------------------------------
|   Inf_Next = |- !f. Inf f ==> !t. f t ==> ?t'. Next t t' f
------------------------------------------------------------------------%
let Inf_Next = prove_thm
  (`Inf_Next`,
   "!f. Inf f ==> !t. f t ==> ?t'. Next t t' f",
   PURE_REWRITE_TAC [Inf; Next]
   THEN GEN_TAC
   THEN DISCH_THEN (\th0. X_GEN_TAC "v:num"
                          THEN STRIP_TAC
                          THEN X_CHOOSE_THEN "n:num" STRIP_ASSUME_TAC
                                   (MATCH_MP wop' (SPEC "v:num" th0)))
   THEN EXISTS_TAC "n:num"
   THEN ASM_REWRITE_TAC []
   THEN REPEAT STRIP_TAC
   THEN RES_THEN (STRIP_ASSUME_TAC o (REWRITE_RULE[DE_MORGAN_THM]))
   THEN RES_TAC
  )
where wop' =
 CONV_RULE (DEPTH_CONV BETA_CONV) (SPEC (( mk_abs
                                         o dest_exists
                                         o snd
                                         o dest_forall
                                         o rhs
                                         o concl
                                         o SPEC_ALL
                                         ) Inf)
                                        WOP
                                  );;

%------------------------------------------------------------------------
|   Next_ADD1 = |- !f t.  f (t+1)  ==>  Next t (t+1) f
------------------------------------------------------------------------%
let Next_ADD1 = prove_thm
  (`Next_ADD1`,
   "!f t.  f (t+1)  ==>  Next t (t+1) f",
   REWRITE_TAC [ Next
               ; SYM (SPEC_ALL ADD1)
               ; LESS_SUC_REFL
               ]
   THEN REPEAT STRIP_TAC
   THENL [ FIRST_ASSUM ACCEPT_TAC
         ; IMP_RES_THEN
             (STRIP_ASSUME_TAC o (CONV_RULE (ONCE_DEPTH_CONV SYM_CONV)))
             LESS_NOT_EQ
          THEN IMP_RES_TAC LESS_SUC_IMP
          THEN IMP_RES_TAC LESS_ANTISYM
         ]
  );;

%------------------------------------------------------------------------
|   Next_INCREAST = |- !f t1 t2.   ~f(t1+1)       ==>
|                               Next (t1+1) t2 f  ==>  Next t1 t2 f
------------------------------------------------------------------------%
let Next_INCREASE = prove_thm
  (`Next_INCREASE`,
   "!f t1 t2.   ~f(t1+1)       ==>
             Next (t1+1) t2 f  ==>  Next t1 t2 f",
   PURE_REWRITE_TAC [Next; SYM (SPEC_ALL ADD1)]
   THEN REPEAT STRIP_TAC
   THENL [ IMP_RES_TAC SUC_LESS
         ; FIRST_ASSUM ACCEPT_TAC
         ; MATCH_UNDISCH_TAC "~^(genvar":bool")"
           THEN IMP_RES_TAC (PURE_REWRITE_RULE [LESS_OR_EQ] LESS_OR)
           THEN RES_TAC
           THEN ASM_REWRITE_TAC []
        ]
  );;

%------------------------------------------------------------------------
|   Next_IDENTITY = |- !t1 t2 f.   Next t1 t2 f  ==>
|                           !t3.   Next t1 t3 f  ==>  (t2 = t3)
------------------------------------------------------------------------%
let Next_IDENTITY = prove_thm
  (`Next_IDENTITY`,
   "!t1 t2 f.   Next t1 t2 f  ==>
          !t3.  Next t1 t3 f  ==>  (t2 = t3)",
   PURE_REWRITE_TAC [Next]
   THEN REPEAT STRIP_TAC
   THEN PURE_ONCE_REWRITE_TAC
          [(SYM o SPEC_ALL o hd o CONJUNCTS) NOT_CLAUSES]
   THEN DISCH_TAC
   THEN STRIP_ASSUME_TAC
          (SPECL ["t2:num"; "t3:num"]
                 (REWRITE_RULE [DE_MORGAN_THM] LESS_ANTISYM))
   THENL [ ALL_TAC
         ; RULE_ASSUM_TAC (CONV_RULE (ONCE_DEPTH_CONV SYM_CONV))
         ]
   THEN IMP_RES_TAC LESS_CASES_IMP
   THEN RES_TAC
  );;

%------------------------------------------------------------------------
|   IsTimeOf_TRUE = |- !n f t.  IsTimeOf n f t ==> f t
------------------------------------------------------------------------%
let IsTimeOf_TRUE = prove_thm
  (`IsTimeOf_TRUE`,
   "!n f t.  IsTimeOf n f t ==> f t",
   INDUCT_TAC
   THEN REWRITE_TAC [IsTimeOf; Next]
   THEN REPEAT STRIP_TAC
  );;

%------------------------------------------------------------------------
|   IsTimeOf_EXISTS = |- !f. Inf f ==> !n. ?t. IsTimeOf n f t
------------------------------------------------------------------------%
let IsTimeOf_EXISTS = prove_thm
  (`IsTimeOf_EXISTS`,
   "!f. Inf f ==> !n. ?t. IsTimeOf n f t",
   GEN_TAC
   THEN DISCH_TAC
   THEN INDUCT_TAC
   THENL [ IMP_RES_TAC Inf_EXISTS
           THEN IMP_RES_THEN
                  (ASSUME_TAC o (PURE_REWRITE_RULE [LEAST]))
                  Inf_LEAST
           THEN ASM_REWRITE_TAC [IsTimeOf]
         ; FIRST_ASSUM STRIP_ASSUME_TAC
           THEN IMP_RES_TAC IsTimeOf_TRUE
           THEN IMP_RES_TAC Inf_Next
           THEN FIRST_ASSUM STRIP_ASSUME_TAC
           THEN REWRITE_TAC [IsTimeOf]
           THEN EXISTS_TAC "t':num"
           THEN EXISTS_TAC "t:num"
           THEN ASM_REWRITE_TAC []
         ]
  );;

%------------------------------------------------------------------------
|   TimeOf_DEFINED = |- !f. Inf f ==> (!n. IsTimeOf n f (TimeOf f n))
------------------------------------------------------------------------%
let TimeOf_DEFINED = save_thm
  (`TimeOf_DEFINED`, ( GEN_ALL
                     o DISCH_ALL
                     o GEN_ALL
                     o (REWRITE_RULE [SYM(SPEC_ALL TimeOf)])
                     o CONV_RULE (DEPTH_CONV BETA_CONV)
                     o (REWRITE_RULE [EXISTS_DEF])
                     o SPEC_ALL
                     o UNDISCH_ALL
                     o SPEC_ALL
                     ) IsTimeOf_EXISTS
  );;

%------------------------------------------------------------------------
|   TimeOf_TRUE = |- !f. Inf f ==> (!n. f (TimeOf f n))
------------------------------------------------------------------------%
let TimeOf_TRUE = save_thm
  (`TimeOf_TRUE`, ( GEN_ALL
                  o DISCH_ALL
                  o GEN_ALL
                  o (MATCH_MP IsTimeOf_TRUE)
                  o SPEC_ALL
                  o UNDISCH_ALL
                  o SPEC_ALL
                  ) TimeOf_DEFINED
  );;

%------------------------------------------------------------------------
|   IsTimeOf_IDENTITY =
|   |- !n f t1 t2. IsTimeOf n f t1 /\ IsTimeOf n f t2 ==> (t1 = t2)
------------------------------------------------------------------------%
let IsTimeOf_IDENTITY = prove_thm
  (`IsTimeOf_IDENTITY`,
   "!n f t1 t2. IsTimeOf n f t1 /\ IsTimeOf n f t2 ==> (t1 = t2)",
   INDUCT_TAC
   THEN PURE_REWRITE_TAC [IsTimeOf; Next]
   THEN X_GEN_TAC "f:num->bool"
   THEN X_GEN_TAC "t1:num"
   THEN X_GEN_TAC "t2:num"
   THEN REPEAT STRIP_TAC
   THENL [ ALL_TAC
         ; RES_THEN (TRY o IMP_RES_THEN
             (\th. EVERY_ASSUM
                     (STRIP_ASSUME_TAC o (\thm. SUBS [th] thm? thm))))
         ]
   THEN STRIP_ASSUME_TAC
          (SPECL ["t2:num"; "t1:num"]
                 (REWRITE_RULE [LESS_OR_EQ] LESS_CASES))
   THEN RES_TAC
  );;

%-----------------------------------------------------------------------
|   TimeOf_INCREASING =
|   |- !f. Inf f  ==>  !n. (TimeOf f n) < (TimeOf f (n+1))
-----------------------------------------------------------------------%
let TimeOf_INCREASING = prove_thm
  (`TimeOf_INCREASING`,
   "!f. Inf f ==> (!n. (TimeOf f n) < (TimeOf f(n+1)))",
   GEN_TAC
   THEN DISCH_TAC
   THEN X_GEN_TAC "n:num"
   THEN IMP_RES_TAC Inf_Next
   THEN IMP_RES_THEN (STRIP_ASSUME_TAC o (SPEC "n:num")) TimeOf_DEFINED
   THEN IMP_RES_THEN
         ( CHOOSE_THEN ( STRIP_ASSUME_TAC
                       o (\thl. CONJ (el 1 thl) (el 2 thl))
                       o CONJUNCTS
                       )
         o (REWRITE_RULE [IsTimeOf; Next])
         o (SPEC "SUC n")
         ) TimeOf_DEFINED
   THEN MATCH_UNDISCH_TAC "x<y"
   THEN IMP_RES_TAC IsTimeOf_TRUE
   THEN IMP_RES_n_THEN 2
         (\th. ONCE_REWRITE_TAC[ADD1; th]) IsTimeOf_IDENTITY
  );;

%-----------------------------------------------------------------------
|   TimeOf_INTERVAL =
|   |- !f. Inf f ==> 
|      !n t. (TimeOf f n)<t  /\  t<(TimeOf f (n+1)) ==> ~f t
-----------------------------------------------------------------------%
let TimeOf_INTERVAL = prove_thm
  (`TimeOf_INTERVAL`,
   "!f. Inf f ==> 
    !n t. (TimeOf f n)<t  /\  t<(TimeOf f (n+1)) ==> ~f t",
   GEN_TAC
   THEN DISCH_TAC
   THEN X_GEN_TAC "n:num"
   THEN X_GEN_TAC "t:num"
   THEN IMP_RES_TAC Inf_Next
   THEN IMP_RES_THEN (STRIP_ASSUME_TAC o (SPEC "n:num")) TimeOf_DEFINED
   THEN IMP_RES_THEN
         ( CHOOSE_THEN ( STRIP_ASSUME_TAC
                       o (\thl.  CONJ (el 1 thl) (SPEC "t:num" (el 4 thl)))
                       o CONJUNCTS
                       )
         o (REWRITE_RULE [IsTimeOf; Next])
         o (SPEC "SUC n")
         ) TimeOf_DEFINED
   THEN FIRST_ASSUM (UNDISCH_TAC o concl)
   THEN IMP_RES_TAC IsTimeOf_TRUE
   THEN IMP_RES_n_THEN 2  (\th. ONCE_REWRITE_TAC[ADD1; th])  IsTimeOf_IDENTITY
  );;

%-----------------------------------------------------------------------
|   TimeOf_Next = |- !f. Inf f ==> !n. Next (TimeOf f n) (TimeOf f (n+1)) f
-----------------------------------------------------------------------%
let TimeOf_Next = prove_thm
  (`TimeOf_Next`,
   "!f. Inf f ==> !n. Next (TimeOf f n) (TimeOf f (n+1)) f",
   PURE_REWRITE_TAC [Next]
   THEN REPEAT STRIP_TAC
   THENL [ IMP_RES_THEN (\th. REWRITE_TAC [th]) TimeOf_INCREASING
         ; IMP_RES_THEN (\th. REWRITE_TAC [th]) TimeOf_TRUE
         ; IMP_RES_TAC TimeOf_INTERVAL THEN RES_TAC
         ]
  );;

% ================================================================= %
% by BtG:                                                           %
%    a useful form of lemma once the definition of Next is          %
%    proven satisfied by the lower level definition.                %
% ================================================================= %
let TimeOf_Next_lemma = prove_thm
(`TimeOf_Next_lemma`,
 "Inf f ==>
    (!t. (Next (TimeOf f t) ((TimeOf f t) + x) f) ==>
         (TimeOf f (SUC t) = ((TimeOf f t) + x)))",
 STRIP_TAC
 THEN GEN_TAC
 THEN IMP_RES_THEN (ASSUME_TAC o (SPEC "t:num")) TimeOf_Next
 THEN STRIP_TAC
 THEN IMP_RES_TAC Next_IDENTITY
 THEN PURE_ONCE_REWRITE_TAC[ADD1]
 THEN FIRST_ASSUM ACCEPT_TAC
 );;

timer false;;
print_theory `when`;;
%<----------------------------------------------------------------------
The Theory when
Parents --  HOL     wop     
Constants --
  Next ":num -> (num -> ((num -> bool) -> bool))"
  IsTimeOf ":num -> ((num -> bool) -> (num -> bool))"
  TimeOf ":(num -> bool) -> (num -> num)"
  Inf ":(num -> bool) -> bool"     
Curried Infixes --
  when ":(num -> *) -> ((num -> bool) -> (num -> *))"     
Definitions --
  Next
    |- !t1 t2 f.
        Next t1 t2 f =
        t1 < t2 /\ f t2 /\ (!t. t1 < t /\ t < t2 ==> ~f t)
  IsTimeOf_DEF
    |- IsTimeOf =
       PRIM_REC
       (\f t. f t /\ (!t'. t' < t ==> ~f t'))
       (\g00004 n f t. ?t'. g00004 f t' /\ Next t' t f)
  TimeOf  |- !f n. TimeOf f n = (@t. IsTimeOf n f t)
  when    |- !s p. s when p = (\n. s(TimeOf p n))
  Inf     |- !f. Inf f = (!t. ?t'. t < t' /\ f t')
Theorems --
  IsTimeOf
    |- (!  f t. IsTimeOf 0 f t = f t /\ (!t'. t' < t ==> ~f t')) /\
       (!n f t. IsTimeOf(SUC n)f t = (?t'. IsTimeOf n f t' /\ Next t' t f))
  Inf_EXISTS  |- !f. Inf f ==> (?n. f n)
  Inf_LEAST   |- !f. Inf f ==> LEAST f
  Inf_Next    |- !f. Inf f ==> (!t. f t ==> (?t'. Next t t' f))
  Next_ADD1   |- !f t. f(t + 1) ==> Next t(t + 1)f
  Next_INCREASE
    |- !f t1 t2. ~f(t1 + 1) ==> Next(t1 + 1)t2 f ==> Next t1 t2 f
  Next_IDENTITY
    |- !t1 t2 f. Next t1 t2 f ==> (!t3. Next t1 t3 f ==> (t2 = t3))
  IsTimeOf_TRUE    |- !n f t. IsTimeOf n f t ==> f t
  IsTimeOf_EXISTS  |- !f. Inf f ==> (!n. ?t. IsTimeOf n f t)
  TimeOf_DEFINED   |- !f. Inf f ==> (!n. IsTimeOf n f(TimeOf f n))
  TimeOf_TRUE      |- !f. Inf f ==> (!n. f(TimeOf f n))
  IsTimeOf_IDENTITY
    |- !n f t1 t2. IsTimeOf n f t1 /\ IsTimeOf n f t2 ==> (t1 = t2)
  TimeOf_INCREASING
    |- !f. Inf f ==> (!n. (TimeOf f n) < (TimeOf f(n + 1)))
  TimeOf_INTERVAL
    |- !f. Inf f ==>
        (!n t. (TimeOf f n) < t /\ t < (TimeOf f(n + 1)) ==> ~f t)
  TimeOf_Next  |- !f. Inf f ==> (!n. Next(TimeOf f n)(TimeOf f(n + 1))f)
*************************************--------------------------------->%
