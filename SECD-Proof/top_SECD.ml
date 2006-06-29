% SECD verification                                                 %
%                                                                   %
% FILE:         top_SECD.ml                                         %
%                                                                   %
% DESCRIPTION: An attempt to define the behaviour of the SECD       %
%              system (chip plus memory), in terms of how memory    %
%              is altered by each machine instruction.              %
%                                                                   %
% USES FILES:  abstract_mem_type.th, cu_types.th, dp_types.th       %
%                                                                   %
% Brian Graham 88.08.24                                             %
%                                                                   %
% Modifications:                                                    %
% 89.10.11 - removed time parameter from top level.                 %
% 16.04.91 - BtG - updated to HOL12                                 %
% ================================================================= %
new_theory `top_SECD`;;

loadt `wordn`;;

map new_parent [ `abstract_mem_type`
               ; `cu_types`
               ; `dp_types`
               ];;

load_all `abstract_mem_type`;;
load_definition `modulo_ops` `pos_num_of`;;
% ================================================================= %
let ctime = ":num";;
let csig = ":^ctime->bool"
and w9_cvec = ":^ctime->word9"
and w14_cvec = ":^ctime->word14"
and w27_cvec = ":^ctime->word27"
and w32_cvec = ":^ctime->word32";;
%=================================================================%
% Handy types for interactive use.                                %
%=================================================================%
let M = ":(word14,atom)mfsexp_mem";;
let M_csig = ":^ctime->^M" ;;

let S = ":(word14#word14)+atom"
and C = ":word14";;

let state = ":bool#bool";;
let state_csig = ":^ctime->^state";;
% ================================================================= %
timer true;;
%=================================================================%
% A higher order iterative function.                              %
%=================================================================%
let nth = new_prim_rec_definition
  (`nth`,
  "(nth    0   (fcn:(*->*)) (x:*) = x                ) /\
   (nth (SUC n) fcn          x    = fcn (nth n fcn x))"
  );;

let LD_   = "INT 1"
and LDC_  = "INT 2"
and LDF_  = "INT 3"
and AP_   = "INT 4"
and RTN_  = "INT 5"
and DUM_  = "INT 6"
and RAP_  = "INT 7"
and SEL_  = "INT 8"
and JOIN_ = "INT 9"
and CAR_  = "INT 10"
and CDR_  = "INT 11"
and ATOM_ = "INT 12"
and CONS_ = "INT 13"
and EQ_   = "INT 14"
and ADD_  = "INT 15"
and SUB_  = "INT 16"
and MUL_  = "INT 17"
and DIV_  = "INT 18"
and REM_  = "INT 19"
and LEQ_  = "INT 20"
and STOP_ = "INT 21";;

%=================================================================%
% State will be described by a boolean pair.                      %
% Initially, only 4 states are defined, being:                    %
%       idle                                                      %
%       top_of_cycle                                              %
%       error0                                                    %
%       error1                                                    %
%=================================================================%
let idle = new_definition
  (`idle`, "idle = (F,F)");;

let top_of_cycle = new_definition
  (`top_of_cycle`, "top_of_cycle = (F,T)");;

let error0 = new_definition
  (`error0`, "error0 = (T,F)");;

let error1 = new_definition
  (`error1`, "error1 = (T,T)");;

% ================================================================= %
% Useful in top level proof.                                        %
% ================================================================= %
let states_distinct = prove_thm
(`states_distinct`,
 "(~(idle = error0)) /\
  (~(idle = error1)) /\
  (~(idle = top_of_cycle)) /\
  (~(error0 = error1)) /\
  (~(error0 = top_of_cycle)) /\
  (~(error1 = top_of_cycle))",
 port [idle; error0; error1; top_of_cycle]
 THEN rt[PAIR_EQ]
 );;

%=================================================================%
% Extract the cell component from the triple returned from        %
% M_Cons, Car, Cdr, etc.                                          %
%=================================================================%
let cell_of = new_definition
  (`cell_of`, "cell_of (a:*,b:**,c:***) = a");;

%=================================================================%
% Extract the memory component from the triple returned from      %
% M_Cons, Car, Cdr, etc.                                          %
%=================================================================%
let mem_of = new_definition
  (`mem_of`, "mem_of (a:*,b:**,c:***) = b");;

%=================================================================%
% Extract the free component from the triple returned from        %
% M_Cons, Car, Cdr, etc.                                          %
%=================================================================%
let free_of = new_definition
  (`free_of`, "free_of (a:*,b:**,c:***) = c");;

%=================================================================%
% Extract the memory and free components from the triple returned %
% from M_Cons, Car, Cdr, etc.                                     %
%=================================================================%
let mem_free_of = new_definition
  (`mem_free_of`, "mem_free_of (a:*,b:**,c:***) = (b,c)");;

map new_definition
    [ `Mul`,  "Mul(w:^C, x:^C, y:^M, z:^C)  =  M_Dec(w,y,z)" ;
      `Div`,  "Div(w:^C, x:^C, y:^M, z:^C)  =  M_Dec(w,y,z)" ;
      `Rem`,  "Rem(w:^C, x:^C, y:^M, z:^C)  =  M_Dec(w,y,z)"
    ];;

%=================================================================%
% The state transition definitions for each of the 21 machine     %
% instructions follows.                                           %
%=================================================================%
%=================================================================%
%                         n          b                            %
%       s = M_Cons (car((cdr )(car((cdr ) e))), s)                  %
%       c = cdr (cdr (c))                                         %
%=================================================================%
let LD_trans = new_definition
(`LD_trans`,
 "LD_trans (s:^C,e:^C,c:^C,d:^C,free:^C,MEM:^M) =
        let m = pos_num_of (M_int_of (M_CAR(M_CAR(M_CDR(c,MEM,free)))))
        in
        let n = pos_num_of (M_int_of (M_CDR(M_CAR(M_CDR (c,MEM,free)))))
        in
        let cell_mem_free =             % returns (cell,(MEM,free)) %
          M_Cons_tr (s,
                   M_CAR (nth n M_CDR
                            (M_CAR (nth m M_CDR
                                      (e, MEM,free)))))
        in 
        (cell_of cell_mem_free,
         e,
         M_Cdr (M_CDR (c, mem_free_of cell_mem_free)),
         d,
         free_of cell_mem_free,
         mem_of cell_mem_free,
         top_of_cycle)");;

%=================================================================%
%       s = M_Cons (car (cdr (c)), s)                               %
%       c = cdr (cdr (c))                                         %
%=================================================================%
let LDC_trans = new_definition
(`LDC_trans`,
 "LDC_trans (s:^C,e:^C,c:^C,d:^C,free:^C,MEM:^M) =
        let cell_mem_free =
            M_Cons_tr (s, M_CAR(M_CDR(c,MEM,free)))
        in
        (cell_of cell_mem_free,
         e,
         M_Cdr(M_CDR (c,mem_free_of cell_mem_free)),
         d,
         free_of cell_mem_free,
         mem_of cell_mem_free,
         top_of_cycle)");;

%=================================================================%
%       s = cons (cons (car(cdr(c)),e), s)                        %
%       c = cdr (cdr (c))                                         %
%=================================================================%
let LDF_trans = new_definition
(`LDF_trans`,
 "LDF_trans (s:^C,e:^C,c:^C,d:^C,free:^C,MEM:^M) =
        let cell_mem_free =
            M_Cons_tr (s, M_Cons_tr (e, M_CAR(M_CDR(c,MEM,free))))
        in
        (cell_of cell_mem_free,
         e,
         M_Cdr(M_CDR (c,mem_free_of cell_mem_free)),
         d,
         free_of cell_mem_free,
         mem_of cell_mem_free,
         top_of_cycle)");;

%=================================================================%
%       d = cons (cdr(cdr(s)), cons(e, cons(cdr(c),d)))           %
%       e = cons (car(cdr(s)), cdr(car(s)))                       %
%       c = car (car (s))                                         %
%       s = NIL                                                   %
% This needs some thought yet.  What is the type of Nil?          %
%=================================================================%
let AP_trans = new_definition
(`AP_trans`,
 "AP_trans (s:^C,e:^C,c:^C,d:^C,free:^C,MEM:^M) =
        let cell_mem_free = M_Cons(e, M_Cons_tr(d,M_CDR(c,MEM,free)))
        in
        let d_mem_free = M_Cons_tr(cell_of cell_mem_free,
                                 M_CDR(M_CDR(s,mem_free_of cell_mem_free)))
        in
        let e_mem_free = M_Cons (M_Car (M_CDR (s,mem_free_of d_mem_free)),
                               M_CDR (M_CAR (s,mem_free_of d_mem_free)))
        in
        (NIL_addr,
         cell_of e_mem_free,
         M_Car (M_CAR (s,mem_free_of e_mem_free)),
         cell_of d_mem_free,
         free_of e_mem_free,
         mem_of e_mem_free,
         top_of_cycle)");;

%=================================================================%
%       s = cons (car(s), car(d))                                 %
%       e = car (cdr(d))                                          %
%       c = car (cdr (cdr(d)))                                    %
%       d = cdr (cdr (cdr(d)))                                    %
%=================================================================%
let RTN_trans = new_definition
(`RTN_trans`,
 "RTN_trans (s:^C,e:^C,c:^C,d:^C,free:^C,MEM:^M) =
        let s_mem_free = M_Cons (M_Car (s,MEM,free),
                               M_CAR (d,MEM,free))
        in
        (cell_of s_mem_free,
         M_Car(M_CDR(d,mem_free_of s_mem_free)),
         M_Car(M_CDR(M_CDR(d,mem_free_of s_mem_free))),
         M_Cdr(M_CDR(M_CDR(d,mem_free_of s_mem_free))),
         free_of s_mem_free,
         mem_of  s_mem_free,
         top_of_cycle)");;

%=================================================================%
%       e = cons (Nil, e)                                         %
%       c = cdr (c)                                               %
%=================================================================%
let DUM_trans = new_definition
(`DUM_trans`,
 "DUM_trans (s:^C,e:^C,c:^C,d:^C,free:^C,MEM:^M) =
        let e_mem_free = M_Cons (NIL_addr,e,MEM,free)
        in
        (s,
         cell_of e_mem_free,
         M_Cdr(c,mem_free_of e_mem_free),
         d,
         free_of e_mem_free,
         mem_of  e_mem_free,
         top_of_cycle)");;

%=================================================================%
%       d = cons (cdr(cdr(s)), cons(cdr(e), cons(cdr(c),d)))      %
%       e = M_Rplaca (cdr(car(s)), car(cdr(s)))                   %
%       c = car (car (s))                                         %
%       s = NIL                                                   %
%=================================================================%
let RAP_trans = new_definition
(`RAP_trans`,
 "RAP_trans (s:^C,e:^C,c:^C,d:^C,free:^C,MEM:^M) =
        let cell1_mem_free = M_Cons_tr(d,M_CDR(c,MEM,free))
        in
        let cell2_mem_free = M_Cons_tr(cell_of cell1_mem_free,
                                  M_CDR(e,mem_free_of cell1_mem_free))
        in
        let d_mem_free = M_Cons_tr (cell_of cell2_mem_free,
                                  M_CDR(M_CDR(s,mem_free_of cell2_mem_free)))
        in
        let e_mem_free = M_Rplaca (M_Cdr (M_CAR (s,mem_free_of d_mem_free)),
                                 M_CAR(M_CDR (s,mem_free_of d_mem_free)))
        in
        (NIL_addr,
         cell_of e_mem_free,
         M_Car(M_CAR(s,mem_free_of e_mem_free)),
         cell_of d_mem_free,
         free_of e_mem_free,
         mem_of  e_mem_free,
         top_of_cycle)");;

%=================================================================%
%       d = cons (cdr(cdr(cdr(c))), d)                            %
%       c = (mem[True] = mem[car(s)]) => car(cdr(c))    |         %
%                                        car(cdr(cdr(c)))         %
%       s = cdr(s)                                                %
%=================================================================%
let SEL_trans = new_definition
(`SEL_trans`,
 "SEL_trans (s:^C,e:^C,c:^C,d:^C,free:^C,MEM:^M) =
        let d_mem_free = M_Cons_tr (d,M_CDR(M_CDR(M_CDR(c,MEM,free))))
        in
        let cond = M_is_T (M_CAR (s,mem_free_of d_mem_free))
        in
        (M_Cdr (s, mem_free_of d_mem_free),
         e,
         (cond => M_Car(M_CDR (c,mem_free_of d_mem_free))     |
                  M_Car(M_CDR(M_CDR(c,mem_free_of d_mem_free)))),
         cell_of d_mem_free,
         free_of d_mem_free,
         mem_of  d_mem_free,
         top_of_cycle)");;

%=================================================================%
%       c = car(d)                                                %
%       d = cdr(d)                                                %
%=================================================================%
let JOIN_trans = new_definition
(`JOIN_trans`,
 "JOIN_trans (s:^C,e:^C,c:^C,d:^C,free:^C,MEM:^M) =
        (s,
         e,
         M_Car(d,MEM,free),
         M_Cdr(d,MEM,free),
         free,
         MEM,
         top_of_cycle)");;

%=================================================================%
%       s = cons (car(car(s)), cdr(s))                            %
%       c = cdr(c)                                                %
%=================================================================%
let CAR_trans = new_definition
(`CAR_trans`,
 "CAR_trans (s:^C,e:^C,c:^C,d:^C,free:^C,MEM:^M) =
        let s_mem_free = M_Cons (M_Car(M_CAR (s,MEM,free)),
                               M_CDR(s,MEM,free))
        in
        (cell_of s_mem_free,
         e,
         M_Cdr(c,mem_free_of s_mem_free),
         d,
         free_of s_mem_free,
         mem_of  s_mem_free,
         top_of_cycle)");;

%=================================================================%
%       s = cons (cdr(car(s)), cdr(s))                            %
%       c = cdr(c)                                                %
%=================================================================%
let CDR_trans = new_definition
(`CDR_trans`,
 "CDR_trans (s:^C,e:^C,c:^C,d:^C,free:^C,MEM:^M) =
        let s_mem_free = M_Cons (M_Cdr(M_CAR (s,MEM,free)),
                               M_CDR(s,MEM,free))
        in
        (cell_of s_mem_free,
         e,
         M_Cdr(c,mem_free_of s_mem_free),
         d,
         free_of s_mem_free,
         mem_of  s_mem_free,
         top_of_cycle)");;

%=================================================================%
%       s = cons ((ATOM(mem[car(s)]) => True | False, cdr(s))     %
%       c = cdr(c)                                                %
%=================================================================%
let ATOM_trans = new_definition
(`ATOM_trans`,
 "ATOM_trans (s:^C,e:^C,c:^C,d:^C,free:^C,MEM:^M) =
        let s_mem_free = M_Cons ((M_Atom (M_CAR (s,MEM,free))=>
                                        T_addr|F_addr),
                               M_CDR(s,MEM,free))
        in
        (cell_of s_mem_free,
         e,
         M_Cdr(c,mem_free_of s_mem_free),
         d,
         free_of s_mem_free,
         mem_of  s_mem_free,
         top_of_cycle)");;

%=================================================================%
%       s = cons (cons (car(s), car(cdr(s))), cdr(cdr(s)))        %
%       c = cdr (c)                                               %
%=================================================================%
let CONS_trans = new_definition
(`CONS_trans`,
 "CONS_trans (s:^C,e:^C,c:^C,d:^C,free:^C,MEM:^M) =
        let cell_mem_free = M_Cons (M_Car (s,MEM,free),
                                       M_CAR(M_CDR(s,MEM,free)))
        in
        let s_mem_free = M_Cons(cell_of cell_mem_free,
                              M_CDR(M_CDR(s,mem_free_of cell_mem_free)))
        in
        (cell_of s_mem_free,
         e,
         M_Cdr(c,mem_free_of s_mem_free),
         d,
         free_of s_mem_free,
         mem_of  s_mem_free,
         top_of_cycle)");;

%=================================================================%
%       s = cons ((mem[car(cdr(s))]=mem[car(s)]) =>               %
%                       True | False, cdr(cdr(s)))                %
%       c = cdr(c)                                                %
%=================================================================%
let EQ_trans = new_definition
(`EQ_trans`,
 "EQ_trans (s:^C,e:^C,c:^C,d:^C,free:^C,MEM:^M) =
        let s_mem_free = M_Cons ((M_Eq(M_Car(M_CDR(s,MEM,free)),
                                  M_CAR(s,MEM,free))=>T_addr|F_addr),
                               M_CDR(M_CDR(s,MEM,free)))
        in
        (cell_of s_mem_free,
         e,
         M_Cdr(c,mem_free_of s_mem_free),
         d,
         free_of s_mem_free,
         mem_of  s_mem_free,
         top_of_cycle)");;

%=================================================================%
%       s = cons (M_Add (mem[car(cdr(s))],                          %
%                        mem[car(s)]), cdr(cdr(s)))               %
%       c = cdr (c)                                               %
%=================================================================%
let ADD_trans = new_definition
(`ADD_trans`,
 "ADD_trans (s:^C,e:^C,c:^C,d:^C,free:^C,MEM:^M) =
        let arg1 = M_Car(M_CDR(s,MEM,free))
        in
        let arg2 = M_Car(s,MEM,free)
        in
        let cell_mem_free = M_Add (arg1,arg2,MEM,free)
        in
        let s_mem_free = M_Cons (cell_of cell_mem_free,
                               M_CDR(M_CDR(s,mem_free_of cell_mem_free)))
        in
        (cell_of s_mem_free,
         e,
         M_Cdr(c,mem_free_of s_mem_free),
         d,
         free_of s_mem_free,
         mem_of  s_mem_free,
         top_of_cycle)");;

%=================================================================%
%       s = cons (M_Sub (mem[car(cdr(s))],                          %
%                        mem[car(s)]), cdr(cdr(s)))               %
%       c = cdr (c)                                               %
%=================================================================%
let SUB_trans = new_definition
(`SUB_trans`,
 "SUB_trans (s:^C,e:^C,c:^C,d:^C,free:^C,MEM:^M) =
        let arg1 = M_Car(M_CDR(s,MEM,free))
        in
        let arg2 = M_Car(s,MEM,free)
        in
        let cell_mem_free = M_Sub (arg1,arg2,MEM,free)
        in
        let s_mem_free = M_Cons (cell_of cell_mem_free,
                               M_CDR(M_CDR(s,mem_free_of cell_mem_free)))
        in
        (cell_of s_mem_free,
         e,
         M_Cdr(c,mem_free_of s_mem_free),
         d,
         free_of s_mem_free,
         mem_of  s_mem_free,
         top_of_cycle)");;

%=================================================================%
%       s = cons (Mul (mem[car(cdr(s))],                          %
%                        mem[car(s)]), cdr(cdr(s)))               %
%       c = cdr (c)                                               %
%=================================================================%
let MUL_trans = new_definition
(`MUL_trans`,
 "MUL_trans (s:^C,e:^C,c:^C,d:^C,free:^C,MEM:^M) =
        let arg1 = M_Car(M_CDR(s,MEM,free))
        in
        let arg2 = M_Car(s,MEM,free)
        in
        let cell_mem_free = Mul (arg1,arg2,MEM,free)
        in
        let s_mem_free = M_Cons (cell_of cell_mem_free,
                               M_CDR(M_CDR(s,mem_free_of cell_mem_free)))
        in
        (cell_of s_mem_free,
         e,
         M_Cdr(c,mem_free_of s_mem_free),
         d,
         free_of s_mem_free,
         mem_of  s_mem_free,
         top_of_cycle)");;

%=================================================================%
%       s = cons (Div (mem[car(cdr(s))],                          %
%                        mem[car(s)]), cdr(cdr(s)))               %
%       c = cdr (c)                                               %
%=================================================================%
let DIV_trans = new_definition
(`DIV_trans`,
 "DIV_trans (s:^C,e:^C,c:^C,d:^C,free:^C,MEM:^M) =
        let arg1 = M_Car(M_CDR(s,MEM,free))
        in
        let arg2 = M_Car(s,MEM,free)
        in
        let cell_mem_free = Div (arg1,arg2,MEM,free)
        in
        let s_mem_free = M_Cons (cell_of cell_mem_free,
                               M_CDR(M_CDR(s,mem_free_of cell_mem_free)))
        in
        (cell_of s_mem_free,
         e,
         M_Cdr(c,mem_free_of s_mem_free),
         d,
         free_of s_mem_free,
         mem_of  s_mem_free,
         top_of_cycle)");;

%=================================================================%
%       s = cons (Rem (mem[car(cdr(s))],                          %
%                        mem[car(s)]), cdr(cdr(s)))               %
%       c = cdr (c)                                               %
%=================================================================%
let REM_trans = new_definition
(`REM_trans`,
 "REM_trans (s:^C,e:^C,c:^C,d:^C,free:^C,MEM:^M) =
        let arg1 = M_Car(M_CDR(s,MEM,free))
        in
        let arg2 = M_Car(s,MEM,free)
        in
        let cell_mem_free = Rem (arg1,arg2,MEM,free)
        in
        let s_mem_free = M_Cons (cell_of cell_mem_free,
                               M_CDR(M_CDR(s,mem_free_of cell_mem_free)))
        in
        (cell_of s_mem_free,
         e,
         M_Cdr(c,mem_free_of s_mem_free),
         d,
         free_of s_mem_free,
         mem_of  s_mem_free,
         top_of_cycle)");;

%=================================================================%
%       s = cons ((mem[car(cdr(s))]<=mem[car(s)]) =>              %
%                         True|False, cdr(cdr(s)))                %
%       c = cdr (c)                                               %
%=================================================================%
let LEQ_trans = new_definition
(`LEQ_trans`,
 "LEQ_trans (s:^C,e:^C,c:^C,d:^C,free:^C,MEM:^M) =
        let arg1 = M_Car(M_CDR(s,MEM,free))
        in
        let arg2 = M_Car(s,MEM,free)
        in
        let s_mem_free = M_Cons ((M_Leq (arg1,arg2,MEM,free)=>
                                    T_addr|F_addr),
                               M_CDR(M_CDR(s,MEM,free)))
        in
        (cell_of s_mem_free,
         e,
         M_Cdr(c,mem_free_of s_mem_free),
         d,
         free_of s_mem_free,
         mem_of  s_mem_free,
         top_of_cycle)"
 );;

%<
This definition is not usable.  Replacement follows ...
%=================================================================%
%       s = car(s)                                                %
%       cdr(mem[num]) = car(s)                                    %
%    NOTE: the car bits are undefined value                       %
%=================================================================%
let STOP_trans = new_definition
(`STOP_trans`,
 "STOP_trans (s:^C,e:^C,c:^C,d:^C,free:^C,MEM:^M) =
        let new_s = M_Car (s,MEM,free)
        in
        (new_s,
         e,
         c,
         d,
         free,
         (@m. REP_mfsexp_mem m =
            (\a. (a = NUM_addr) => (F,F), INL (@v. SND v = new_s) |
                                 REP_mfsexp_mem MEM a)),
         idle)");;
>%
%=================================================================%
%       s = car(s)                                                %
%       cdr(mem[num]) = car(s)                                    %
%    NOTE: the car, rt, and gc bits are undefined values!         %
%=================================================================%
let STOP_trans_relation = new_definition
(`STOP_trans_relation`,
 "STOP_trans_relation ((s':^C,e':^C,c':^C,d':^C,free':^C,MEM':^M,state'),
                       (s:^C,e:^C,c:^C,d:^C,free:^C,MEM:^M)) =
        (s' = M_Car (s, MEM, free)) /\
        (e' = e) /\
        (c' = c) /\
        (d' = d) /\
        (free' = free) /\
        (!a. (a = NUM_addr) => (!z. M_is_cons(a, MEM', z) ==>
                                    (M_Cdr(a, MEM', z) = s'))
                             | (REP_mfsexp_mem MEM' a = REP_mfsexp_mem MEM a)) /\
        (state' = idle)"
 );;

%=================================================================%
% Returns the 4 main registers, free pointer, memory, plus a      %
% state value that relates to the fsm.                            %
% It expects the instruction value to be in the range:            %
%       INT 1 to INT 21.                                          %
%=================================================================%
let NEXT = new_definition
(`NEXT`,
 "NEXT ((s':^C,e':^C,c':^C,d':^C,free':^C,MEM':^M,state'),
        (s:^C,e:^C,c:^C,d:^C,free:^C,MEM:^M)) =
  let instr = M_int_of (M_CAR (c, MEM, free))
  in
  (
   (instr = ^LD_)   =>   ((s',e',c',d',free',MEM',state') =
                          (LD_trans   (s,e,c,d,free,MEM))) |
   (instr = ^LDC_)  =>   ((s',e',c',d',free',MEM',state') =
                          (LDC_trans  (s,e,c,d,free,MEM))) |
   (instr = ^LDF_)  =>   ((s',e',c',d',free',MEM',state') =
                          (LDF_trans  (s,e,c,d,free,MEM))) |
   (instr = ^AP_)   =>   ((s',e',c',d',free',MEM',state') =
                          (AP_trans   (s,e,c,d,free,MEM))) |
   (instr = ^RTN_)  =>   ((s',e',c',d',free',MEM',state') =
                          (RTN_trans  (s,e,c,d,free,MEM))) |
   (instr = ^DUM_)  =>   ((s',e',c',d',free',MEM',state') =
                          (DUM_trans  (s,e,c,d,free,MEM))) |
   (instr = ^RAP_)  =>   ((s',e',c',d',free',MEM',state') =
                          (RAP_trans  (s,e,c,d,free,MEM))) |
   (instr = ^SEL_)  =>   ((s',e',c',d',free',MEM',state') =
                          (SEL_trans  (s,e,c,d,free,MEM))) |
   (instr = ^JOIN_) =>   ((s',e',c',d',free',MEM',state') =
                          (JOIN_trans (s,e,c,d,free,MEM))) |
   (instr = ^CAR_)  =>   ((s',e',c',d',free',MEM',state') =
                          (CAR_trans  (s,e,c,d,free,MEM))) |
   (instr = ^CDR_)  =>   ((s',e',c',d',free',MEM',state') =
                          (CDR_trans  (s,e,c,d,free,MEM))) |
   (instr = ^ATOM_) =>   ((s',e',c',d',free',MEM',state') =
                          (ATOM_trans (s,e,c,d,free,MEM))) |
   (instr = ^CONS_) =>   ((s',e',c',d',free',MEM',state') =
                          (CONS_trans (s,e,c,d,free,MEM))) |
   (instr = ^EQ_)   =>   ((s',e',c',d',free',MEM',state') =
                          (EQ_trans   (s,e,c,d,free,MEM))) |
   (instr = ^ADD_)  =>   ((s',e',c',d',free',MEM',state') =
                          (ADD_trans  (s,e,c,d,free,MEM))) |
   (instr = ^SUB_)  =>   ((s',e',c',d',free',MEM',state') =
                          (SUB_trans  (s,e,c,d,free,MEM))) |
   (instr = ^MUL_)  =>   ((s',e',c',d',free',MEM',state') =
                          (MUL_trans  (s,e,c,d,free,MEM))) |
   (instr = ^DIV_)  =>   ((s',e',c',d',free',MEM',state') =
                          (DIV_trans  (s,e,c,d,free,MEM))) |
   (instr = ^REM_)  =>   ((s',e',c',d',free',MEM',state') =
                          (REM_trans  (s,e,c,d,free,MEM))) |
   (instr = ^LEQ_)  =>   ((s',e',c',d',free',MEM',state') =
                          (LEQ_trans  (s,e,c,d,free,MEM))) |
%  (instr = ^STOP_) %    (STOP_trans_relation((s',e',c',d',free',MEM',state'),
                                              (s,e,c,d,free,MEM)))
  )"
 );;

%=================================================================%
% The clock signal is not used, so is omitted for now.  If I      %
% want to extend the behavioural description to include shift     %
% registers, then both clock signals will need to be added        %
% (or use the clock and its inverse).  They should be abstracted  %
% from rt level such that the rt_SYS_clocked signal holds for     %
% every point in the interval between points of ctime.  Also      %
% required will be a change to the abstraction points of mtime,   %
% to allow some points when the SR_clocks operate.                %
%                                                                 %
% Note that the reset input has been eliminated already, since it %
% is asserted when we may not be in a major state.  The top level %
% specification will only hold if we are properly initialized...  %
%                                                                 %
% 89.08.30 - reintroduced a parameter "t", so that the            %
%            constraints in the proof statement can limit us to   %
%            those times when we are in a major state, rather     %
%            than trying to prove the spec holds for times        %
%            beginning at other states.                           %
% 89.10.11 - eliminated t parameter again - clearer thinking      %
%            prevails.                                            %
%=================================================================%
let SYS_spec = new_definition
(`SYS_spec`,
 "SYS_spec (MEM:^M_csig)
           (s:^w14_cvec) (e:^w14_cvec) (c:^w14_cvec) (d:^w14_cvec)
           (free:^w14_cvec)
           (button_pin:^csig)
           (state:^state_csig)
  =
  (state 0 = idle) /\
           
 !t:^ctime.
  (\(s', e', c', d', free', MEM', state').
   (state t = idle)
    => (button_pin t
       => ((s', e', c', d', free', MEM', state') =
           (M_Cdr(M_CAR(NUM_addr, MEM t, free t)),
            NIL_addr,
            M_Car(M_CAR(NUM_addr, MEM t, free t)),
            NIL_addr,
            M_Cdr(NUM_addr, MEM t, free t),
            MEM t, 
            top_of_cycle))
        | ((s', e', c', d', free', MEM', state') =
           (s t, e t, c t, d t, free t, MEM t, idle)))
     |
   (state t = error0)
    => (button_pin t
        => ((s', e', c', d', free', MEM', state') =
            (s t, e t, c t, d t, free t, MEM t, error1))
         | ((s', e', c', d', free', MEM', state') =
            (s t, e t, c t, d t, free t, MEM t, error0)))
     |
   (state t = error1) 
    => (button_pin t
        => ((s', e', c', d', free', MEM', state') =
            (s t, e t, c t, d t, free t, MEM t, error1))
         | ((s', e', c', d', free', MEM', state') =
            (s t, e t, c t, d t, free t, MEM t, idle)))
     |  % (state = top_of_cycle) %
   (NEXT ((s', e', c', d', free', MEM', state'),
          (s t, e t, c t, d t, free t, MEM t))
   )
  )

  (s (SUC t),
   e (SUC t),
   c (SUC t),
   d (SUC t),
   free (SUC t),
   MEM (SUC t),
   state (SUC t))"
 );;

timer false;;
close_theory ();;
print_theory `-`;;
