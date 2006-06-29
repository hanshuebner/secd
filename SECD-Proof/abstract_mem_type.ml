% SECD verification                                                 %
%                                                                   %
% FILE:         abstract_mem_type.ml                                %
%                                                                   %
% DESCRIPTION: I am attempting here to define memories as per       %
%              Ian Mason's work on the Semantics of Destructive     %
%              Lisp.                                                %
%              This differs from the original attempt in that the   %
%              selector functions also have "free" as an argument,  %
%              although they apply the identity to it, never        %
%              changing the free pointer.  This eases composition   %
%              of cons'es and selector functions (car's cdr's).     %
%                                                                   %
%              This third revision alters the definition of the     %
%              memory function type.  This time the codomain of     %
%              the memory function is domain squared or atom.       %
%              This relieves the problem of a different mapping     %
%              for atoms that was implied by ian's work, where      %
%              perhaps the pointer and atom are stored in same      %
%              field width, rather than placing atom in a           %
%              separate cell, as the secd implementation does.      %
%                                                                   %
% Brian Graham 88.08.17                                             %
%                                                                   %
% Modifications                                                     %
% 89.05.25 - converted to hol88 type package                        %
% 08.04.91 - BtG - updated to HOL12                                 %
% ================================================================= %
new_theory `abstract_mem_type`;;

loadt `wordn`;;
load_library `integer`;;

new_parent `modulo_ops`;;

timer true;;
%=================================================================%
% General theory of Memory Structures:                            %
% ************************************                            %
% C - the set of cells of memory                                  %
% A - the set of atoms :                                          %
%     includes (a subset of) the integers                         %
%     symbols - including NIL, TRUE, FALSE                        %
% C and A are disjoint.                                           %
%                                                                 %
% V - the set of memory values: V = C U A                         %
%                                                                 %
% mu - a memory, which is a function from finite subset of C      %
%      to the set of sequences of memory values: V* = (A U C)*    %
% (This is a most general definition.  In lisp we typically have  %
%  sequences of length 2 in cons cells.)                          %
%                                                                 %
% delta(mu) = domain of mu                                        %
%                                                                 %
% mu is in [delta(mu) -> (delta(mu) U A)*]                        %
%                                                                 %
% M(A,C) - the set of all memories over A and C                   %
%                                                                 %
% [v0, ..., vn-1],mu - a memory object, consists of a memory      %
%    mu in M, and a sequence s.t. vi is in (delta(mu) U A)        %
%    (Intuitively, a memory and a set of values which EXIST in    %
% 		 that memory).                                    %
%=================================================================%

%=================================================================%
% Theory of S-expression Memories:                                %
% ********************************                                %
% A - includes Z (the integers), NIL, TRUE, FALSE, and unlimited  %
%     collection of non-numeric atoms.                            %
%                                                                 %
% mu - is in (delta(mu) -> (A U (delta(mu)^2)))                   %
%                                                                 %
% O = (Car, Cdr, Cons, Rplaca, Rplacd, Atom, Add, Sub, Mul, Dec,  %
% 	  Div, Rem, Eq, Leq, ...                                  %
% All operations except Cons are obvious.  Cons will enlarge the  %
% domain (delta(mu)) of the memory, by selecting a new location   %
% from free storage, and installing the arguments as its contents.%
% Free storage is just (C - delta(mu)).                           %
%                                                                 %
% cons([v0,v1];mu) = c;mu0                                        %
% 	where c is not in delta(mu), and                          %
% 	      mu0 = mu{c<-[v0,v1]}                                %
%                                                                 %
% Rplaca and Rplacd update the contents of a location in memory,  %
% but do not change the domain.                                   %
%=================================================================%

%=================================================================%
% Implementation of S-expression Memories:                        %
% ****************************************                        %
% I want to define a memory as a function from some domain to     %
% (the domain squared Union some other set (atom)).               %
% Thus it will be a type of two type variables, delta (for domain)%
% and alpha (for the set of atoms).  Thus we want:                %
%      delta -> (delta^2 U alpha)                                 %
%                                                                 %
% Now, the same idea for a memory with mark and field bits for    %
% garbage collection: mfsexp.                                     %
%                                                                 %
% For simplicity, a free list pointer will be included as an      %
% argument to all functions on mfsexp_mem's.  Thus, the domain    %
% of the function will not change, as done in the theory above.   %
% Rather, the domain stays constant, and the cells not in the     %
% domain of the theoretical version of the function, will be in   %
% the free list.                                                  %
% This makes the allocation of cells explicit, and this is        %
% really not an essential part of the specification - we don't    %
% care what shape the free list is in, as long as the relevant    %
% data structures are correctly manipulated.                      %
%                                                                 %
% Memory is mapped onto an existing (function) type, and is       %
% defined in 2 steps:                                             %
%   1. define a recognizer function on the existing type.         %
%   2. show the type is nonempty.                                 %
%=================================================================%
let IS_mfsexp_mem = new_definition
  (`IS_mfsexp_mem`,
   "IS_mfsexp_mem (rep_mfsexpmem:*->((bool#bool)#((*#*)+**))) =
    !cell:*. ?m f.
             (?a d:*. rep_mfsexpmem cell = (m,f),INL(a,d)) \/
             (? z:**. rep_mfsexpmem cell = (m,f),INR z)"
  );;

let EXISTS_mfsexp_mem = prove_thm
  (`EXISTS_mfsexp_mem`,
   "?m:*->((bool#bool)#((*#*)+**)). IS_mfsexp_mem m",
   EXISTS_TAC "(\a:*. ((F,F),(INL (a,a)):(*#*)+**))"
   THEN port [IS_mfsexp_mem]
   THEN in_conv_tac BETA_CONV
   THEN GEN_TAC
   THEN REPEAT (EXISTS_TAC "F")
   THEN DISJ1_TAC
   THEN REPEAT (EXISTS_TAC "(cell):*")
   THEN MATCH_ACCEPT_TAC (REFL "x:*")
  );;

%=================================================================%
% mfsexp_mem_TY_DEF = |- ?rep. TYPE_DEFINITION IS_mfsexp_mem rep  %
%=================================================================%
let mfsexp_mem_TY_DEF = new_type_definition
  (`mfsexp_mem`,
   "IS_mfsexp_mem:(* -> ((bool#bool)#((*#*)+**)))->bool",
   EXISTS_mfsexp_mem
  );;

%=================================================================%
% Get the set of lemmas that Tom Melham's type package provides.  %
%=================================================================%
% loadt `wordn/new_ty_lem`;; %

let mfsexp_mem_ISO_DEF =
 define_new_type_bijections
  `mfsexp_mem_ISO_DEF` `ABS_mfsexp_mem` `REP_mfsexp_mem` mfsexp_mem_TY_DEF;;

%=================================================================%
% The type of memory that we want has:                            %
%       domain:    :word14                                        %
%       range:     :(bool # bool) # ((word14 # word14) + atoms)   %
% The set of atoms includes:                                      %
%       integers                                                  %
%       symbols                                                   %
% Among the symbols are the constants: NIL, TRUE, and FALSE.      %
% (Note that the special values for TRUE and FALSE are not        %
%  typical for Lisp implementations, but are used by LispKit.     %
%  These values are used by 4 machine instructions:               %
%       SEL, ATOM, EQ, and LEQ.)                                  %
%                                                                 %
% Symbols other than those listed above can occur as arguments to %
% the compiled program.  In the machine (and the actual memory)   %
% they are represented by numbers.  Program variables, on the     %
% other hand, are not directly represented in the memory, but     %
% instead, references to the variable are compiled into a LD      %
% instruction with arguments that enable it to locate the         %
% position where the value bound to the variable is stored.  Thus %
% variables are not represented in the set of atoms.              %
%                                                                 %
% It may not be useful to define a new type for atoms, instead    %
% of using the type ":integer+num" (?) alone.                     %
%=================================================================%

%=================================================================%
% atom_thm =                                                      %
% |- !f0 f1. ?! fn. (!i. fn(Int i) = f0 i) /\                     %
%                   (!n. fn(Symb n) = f1 n)                       %
%=================================================================%
let atom_thm = define_type
   `atom_thm`
   `atom = Int integer | Symb num`;;

%=================================================================%
% |- !P. (!i. P(Int i)) /\ (!n. P(Symb n)) ==> (!a. P a)          %
%=================================================================%
let atom_Induct = save_thm
  (`atom_Induct`, prove_induction_thm atom_thm);;

%=================================================================%
% |- !i n. ~(Int i = Symb n)                                      %
%=================================================================%
let NOT_Int_Symb = save_thm
(`NOT_Int_Symb`, prove_constructors_distinct atom_thm);;

%=================================================================%
% |- (!i i'. (Int i = Int i') = (i = i')) /\                      %
%    (!n n'. (Symb n = Symb n') = (n = n'))                       %
%=================================================================%
let Int_11, Symb_11 =
let th = prove_constructors_one_one atom_thm
in
(save_thm (`Int_11`, CONJUNCT1 th),
 save_thm (`Symb_11`, CONJUNCT2 th));;

%=================================================================%
% |- !a. (?i. a = Int i) \/ (?n. a = Symb n)                      %
%=================================================================%
let atom_cases = save_thm
  (`atom_cases`, prove_cases_thm atom_Induct);;


let int_of_atom = new_recursive_definition false atom_thm
   `int_of_atom`
   "int_of_atom (Int i) = i";;

let symb_of_atom = new_recursive_definition false atom_thm
   `symb_of_atom`
   "symb_of_atom (Symb s) = s";;

let atom_is_int = new_recursive_definition false atom_thm
   `atom_is_int`
  "(atom_is_int (Symb s) = F) /\
   (atom_is_int (Int  i) = T)   ";;

let atom_is_symb = new_recursive_definition false atom_thm
   `atom_is_symb`
  "(atom_is_symb (Symb s) = T) /\
   (atom_is_symb (Int  i) = F)   ";;

%=================================================================%
% Built-in constants:                                             %
%=================================================================%
let NIL_atom = new_definition (`NIL_atom`,"NIL_atom:atom = Symb 0")
and T_atom   = new_definition (`T_atom`,  "T_atom  :atom = Symb 1")
and F_atom   = new_definition (`F_atom`,  "F_atom  :atom = Symb 2");;

%%
%=================================================================%
% M_Car:(C#M#C) -> C                                              %
%=================================================================%
let M_Car = new_definition
  (`M_Car`,
   "M_Car (x:*, MEM:(*,**)mfsexp_mem,free:*) =
            FST (OUTL (SND (REP_mfsexp_mem MEM x)))"
  );;

%=================================================================%
% M_CAR:(C#M#C) -> (C#M#C)                                        %
%=================================================================%
let M_CAR = new_definition
  (`M_CAR`,
   "M_CAR (x, MEM:(*,**)mfsexp_mem,free:*) =
            M_Car (x, MEM, free), MEM, free"
  );;

%=================================================================%
% M_Cdr:(C#M#C) -> C                                              %
%=================================================================%
let M_Cdr = new_definition
  (`M_Cdr`,
   "M_Cdr (x:*, MEM:(*,**)mfsexp_mem,free:*) =
            SND (OUTL (SND (REP_mfsexp_mem MEM x)))"
  );;

%=================================================================%
% M_CDR:(C#M#C) -> (C#M#C)                                        %
%=================================================================%
let M_CDR = new_definition
  (`M_CDR`,
   "M_CDR (x, MEM:(*,**)mfsexp_mem,free:*) =
           M_Cdr (x, MEM, free), MEM, free"
  );;

%=================================================================%
% M_Atom:(C#M#C) -> bool                                          %
%=================================================================%
let M_Atom = new_definition
  (`M_Atom`,
   "!(v:*) (MEM:(*,**)mfsexp_mem) (free:*).
    M_Atom (v,MEM,free) = ISR(SND(REP_mfsexp_mem MEM v))"
  );;

%%
%=================================================================%
% This definition will not suffice for the next stage when        %
% garbage collection is attempted.  Garbage collection is         %
% performed at a lower level, protecting structures accessible    %
% from various registers not seen at this level.  The function    %
% should have a set of pointers as arguments, aside from the      %
% free list pointer.                                              %
%=================================================================%
new_constant 
(`M_garbage_collect`, ":((*,**)mfsexp_mem#*)->((*,**)mfsexp_mem#*)");;

%=================================================================%
% This version allows composition of Cons's, with one added       %
% argument each time.  Keeps track of the state of memory and     %
% free pointer nicely as well!                                    %
%                                                                 %
% M_Cons:(C#C#M#C) -> (C#M#C)                                     %
%=================================================================%
let M_Cons = new_definition
  (`M_Cons`,
   "M_Cons (x:*, y:*, MEM:(*,**)mfsexp_mem, free:*) =
         let (Mem,Free) = (M_Atom (free,MEM,free)         =>
                           (M_garbage_collect (MEM, free)) |
                           (MEM, free))
         in
         ( Free,
           (@m. REP_mfsexp_mem m = 
             (\a. (a=Free) => (F,F),INL(x,y) |
                              REP_mfsexp_mem Mem a)),
           M_Cdr (Free, Mem, Free)
         )"
  );;

%=================================================================%
% Transposes order of arguments only.  Useful for composing.      %
%=================================================================%
let M_Cons_tr = new_definition
  (`M_Cons_tr`,
   "M_Cons_tr (x:*,y:*, MEM:(*,**)mfsexp_mem, free:*) =
         M_Cons (y,x,MEM,free)"
  );;

%=================================================================%
% Very similar to the definition of a new function as done in     %
% M_Cons, the destructive replace operations are simpler.         %
%=================================================================%
%=================================================================%
% M_Rplaca:(C#C#M#C) -> (C#M#C)                                   %
%=================================================================%
let M_Rplaca = new_definition
  (`M_Rplaca`,
   "M_Rplaca (c:*,v:*, MEM:(*,**)mfsexp_mem,free:*) =
        ( c,
          (@m. REP_mfsexp_mem m =
             (\a:*. (a = c) => (F,F),INL(v, M_Cdr(a, MEM, free)) |
                               REP_mfsexp_mem MEM a)),
         free
        )"
  );;
%=================================================================%
% M_Rplacd:(C#C#M#C) -> (C#M#C)                                   %
%=================================================================%
let M_Rplacd = new_definition
  (`M_Rplacd`,
   "M_Rplacd (c:*,v:*, MEM:(*,**)mfsexp_mem,free:*) =
        ( c,
          (@m. REP_mfsexp_mem m =
             (\a:*. (a = c) => (F,F),INL(M_Car(a, MEM, free),v) |
                                REP_mfsexp_mem MEM a)),
          free
        )"
  );;
%%
%=================================================================%
% The functions to get the values of the fields is fairly simple, %
% but should also be defined for constants!  Here they are not.   %
% This is not a vital issue, until garbage collection is tackled. %
%                                                                 %
% The comment above doesn't seem correct!!!                       %
%=================================================================%
let M_mark = new_definition
  (`M_mark`,
   "M_mark (p:*) (MEM:(*,**)mfsexp_mem) =
     (FST o FST) ((REP_mfsexp_mem MEM) p)"
  );;

let M_field = new_definition
  (`M_field`,
   "M_field (p:*) (MEM:(*,**)mfsexp_mem) =
     SND (FST ((REP_mfsexp_mem MEM) p))"
  );;

let M_stripped = new_definition
  (`M_stripped`,
   "M_stripped (p:*) (MEM:(*,**)mfsexp_mem) =
     SND ((REP_mfsexp_mem MEM) p)"
  );;
%=================================================================%
% The functions to set the gc bits are similar to the destructive %
% replace operations.                                             %
%=================================================================%
let M_setm = new_definition
  (`M_setm`,
   "M_setm (b:bool, c:*, MEM:(*,**)mfsexp_mem,free:*) =
            (@ m. REP_mfsexp_mem m =
              \a. (a = c) =>
                   (b,M_field c MEM), (M_stripped c MEM) |
                   REP_mfsexp_mem MEM a)"
  );;

let M_setf = new_definition
  (`M_setf`,
   "M_setf (b:bool, c:*, MEM:(*,**)mfsexp_mem, free:*) =
            (@ m. REP_mfsexp_mem m =
              \a. (a = c) =>
                   (M_mark c MEM,b), (M_stripped c MEM) |
                   REP_mfsexp_mem MEM a)"
  );;

%=================================================================%
% There are only a few remaining operations to define.            %
% These are :                                                     %
%  int (???)                                                      %
%  dec                                                            %
%  eq, leq                                                        %
% add, sub                                                        %
% (mul, div, rem) ???                                             %
% These may or may not be necessary for what we need to do.       %
%=================================================================%

%=================================================================%
% First some useful selectors and predicates.                     %
%=================================================================%
let M_atom_of = new_definition
  (`M_atom_of`,
   "!(v:*) (MEM:(*,atom)mfsexp_mem) (free:*).
    M_atom_of (v,MEM,free) = OUTR(SND(REP_mfsexp_mem MEM v))"
  );;

let M_int_of = new_definition
  (`M_int_of`,
   "!(v:*) (MEM:(*,atom)mfsexp_mem) (free:*).
    M_int_of (v,MEM,free) = int_of_atom (M_atom_of (v,MEM,free))"
  );;

%=================================================================%
% M_is_cons:(C#M#C) -> bool                                       %
%=================================================================%
let M_is_cons = new_definition
  (`M_is_cons`,
   "!(v:*) (MEM:(*,**)mfsexp_mem) (free:*).
    M_is_cons (v,MEM,free) = ISL(SND(REP_mfsexp_mem MEM v))"
  );;

let M_is_T = new_definition
  (`M_is_T`,
   "!(v:*) (MEM:(*,atom)mfsexp_mem) (free:*).
    M_is_T (v,MEM,free) = (M_atom_of (v,MEM,free) = T_atom)"
  );;

%=================================================================%
% New int values may be produced and stored in the memory, BUT,   %
% it is impossible to create new symbols!  Thus we never store    %
% a Symbol atom in memory.  Instead, the symbols are used in      %
% data structures that may be built up by using pointers to the   %
% symbols, wherever they are located.                             %
% The 3 symbolic constants are in reserved memory locations:      %
% this is a constraint on the memory state.  This permits using   %
% the address of the constant locations, instead of the constants %
% themselves!                                                     %
%=================================================================%
let M_store_int = new_definition
  (`M_store_int`,
   "M_store_int (i:integer, MEM:(*,atom)mfsexp_mem,free:*) =
     let (Mem,Free) = M_Atom (free,MEM,free)        =>
                        M_garbage_collect (MEM,free) |
                        (MEM,free)
     in
     ( Free,
       (@m. REP_mfsexp_mem m =
	    (\a. (a = Free) => (F,F),INR (Int i) |
			       REP_mfsexp_mem Mem a)),
       M_Cdr (Free,Mem,Free)
     )"
  );;

%=================================================================%
% Now, the required functions.                                    %
%=================================================================%
let M_Dec = new_definition
  (`M_Dec`,
   "M_Dec (v:*,MEM:(*,atom)mfsexp_mem,free:*)  =
      M_store_int (modulo_28_Dec (M_int_of (v,MEM,free)), MEM, free)"
  );;

%=================================================================%
% Note that EQ is only defined for atoms:                         %
%       at least one of the arg's must be an atom                 %
% The default case when neither are atoms returns an expression   %
% which cannot be evaluated.  This attempts to approximate        %
% undefinedness.                                                  %
%                                                                 %
% Revised 89.09.06 - the definition more closely approximates the %
%                    style of definition used by the rt level in  %
%                    the flagsunit.                               %
%=================================================================%
let M_Eq = new_definition
  (`M_Eq`,
   "M_Eq (x:*,y:*,MEM:(*,atom)mfsexp_mem,free:*)  =
      let Atom_x = M_Atom(x,MEM,free)
      and Atom_y = M_Atom(y,MEM,free)
      in
      ((Atom_x /\ ~Atom_y)
       => F
       | (~Atom_x /\ Atom_y)
         => F
          | (M_atom_of(x,MEM,free) = M_atom_of(y,MEM,free)))"
  );;

let M_Leq = new_definition
  (`M_Leq`,
   "M_Leq (x:*,y:*,MEM:(*,atom)mfsexp_mem,free:*) =
        let x_val = M_int_of (x,MEM,free)
        in
        let y_val = M_int_of (y,MEM,free)
        in
        ((x_val below y_val) \/ (x_val = y_val))"
  );;

let M_Add = new_definition
  (`M_Add`,
   "M_Add (x:*,y:*,MEM:(*,atom)mfsexp_mem,free:*) =
        let x_val = M_int_of (x,MEM,free)
        in
        let y_val = M_int_of (y,MEM,free)
        in
        M_store_int (x_val modulo_28_Add y_val, MEM, free)"
  );;

let M_Sub = new_definition
  (`M_Sub`,
   "M_Sub (x:*,y:*,MEM:(*,atom)mfsexp_mem,free:*) =
        let x_val = M_int_of (x,MEM,free)
        in
        let y_val = M_int_of (y,MEM,free)
        in
        M_store_int (x_val modulo_28_Sub y_val, MEM, free)"
  );;

timer false;;
close_theory ();;
print_theory `-`;;
