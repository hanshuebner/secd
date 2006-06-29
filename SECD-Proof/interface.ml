% SECD verification                                                 %
%                                                                   %
% FILE:        interface.ml                                         %
%                                                                   %
% DESCRIPTION: This includes definitions used by components at      %
%              the rt level view of the host machine.               %
%                                                                   %
% USES FILES:                                                       %
%                                                                   %
% Brian Graham 89.09.05                                             %
%                                                                   %
% Modifications:                                                    %
% 16.04.91 - BtG - updated to HOL12                                 %
% ================================================================= %
new_theory `interface`;;

let mtime = ":num";;
let msig = ":^mtime->bool";;

timer true;;
%-------------------- define one_asserted_12 -----------------%
% this is used by the ALU: only one operation at a time...   %

let one_asserted_12 = new_definition
  (`one_asserted_12`,
   "!a b c d e f g h i j k l:^msig.
    one_asserted_12 a b c d e f g h i j k l =
      !t. 
          (a t ==> (~b t /\ ~c t /\ ~d t /\ ~e t /\ ~f t /\ ~g t
                         /\ ~h t /\ ~i t /\ ~j t /\ ~k t /\ ~l t)) /\
          (b t ==> (~a t /\ ~c t /\ ~d t /\ ~e t /\ ~f t /\ ~g t
                         /\ ~h t /\ ~i t /\ ~j t /\ ~k t /\ ~l t)) /\
          (c t ==> (~a t /\ ~b t /\ ~d t /\ ~e t /\ ~f t /\ ~g t
                         /\ ~h t /\ ~i t /\ ~j t /\ ~k t /\ ~l t)) /\
          (d t ==> (~a t /\ ~b t /\ ~c t /\ ~e t /\ ~f t /\ ~g t
                         /\ ~h t /\ ~i t /\ ~j t /\ ~k t /\ ~l t)) /\
          (e t ==> (~a t /\ ~b t /\ ~c t /\ ~d t /\ ~f t /\ ~g t
                         /\ ~h t /\ ~i t /\ ~j t /\ ~k t /\ ~l t)) /\
          (f t ==> (~a t /\ ~b t /\ ~c t /\ ~d t /\ ~e t /\ ~g t
                         /\ ~h t /\ ~i t /\ ~j t /\ ~k t /\ ~l t)) /\
          (g t ==> (~a t /\ ~b t /\ ~c t /\ ~d t /\ ~e t /\ ~f t
                         /\ ~h t /\ ~i t /\ ~j t /\ ~k t /\ ~l t)) /\
          (h t ==> (~a t /\ ~b t /\ ~c t /\ ~d t /\ ~e t /\ ~f t
                         /\ ~g t /\ ~i t /\ ~j t /\ ~k t /\ ~l t)) /\
          (i t ==> (~a t /\ ~b t /\ ~c t /\ ~d t /\ ~e t /\ ~f t
                         /\ ~g t /\ ~h t /\ ~j t /\ ~k t /\ ~l t)) /\
          (j t ==> (~a t /\ ~b t /\ ~c t /\ ~d t /\ ~e t /\ ~f t
                         /\ ~g t /\ ~h t /\ ~i t /\ ~k t /\ ~l t)) /\
          (k t ==> (~a t /\ ~b t /\ ~c t /\ ~d t /\ ~e t /\ ~f t
                         /\ ~g t /\ ~h t /\ ~i t /\ ~j t /\ ~l t)) /\
          (l t ==> (~a t /\ ~b t /\ ~c t /\ ~d t /\ ~e t /\ ~f t
                         /\ ~g t /\ ~h t /\ ~i t /\ ~j t /\ ~k t))"
  );;

%< Not needed at this level ...

let one_asserted_23 = new_definition
  (`one_asserted_23`,
   "!a b c d e f g h i j k l m n p q r s u v w x y :^msig.
    one_asserted_23 a b c d e f g h i j k l m n p q r s u v w x y =
      !t. 
          (a t ==> (~b t /\ ~c t /\ ~d t /\ ~e t /\ ~f t /\ ~g t /\
                    ~h t /\ ~i t /\ ~j t /\ ~k t /\ ~l t /\ ~m t /\
                    ~n t /\ ~p t /\ ~q t /\ ~r t /\ ~s t /\ ~u t /\
                    ~v t /\ ~w t /\ ~x t /\ ~y t))                 /\
          (b t ==> (~a t /\ ~c t /\ ~d t /\ ~e t /\ ~f t /\ ~g t /\
                    ~h t /\ ~i t /\ ~j t /\ ~k t /\ ~l t /\ ~m t /\
                    ~n t /\ ~p t /\ ~q t /\ ~r t /\ ~s t /\ ~u t /\
                    ~v t /\ ~w t /\ ~x t /\ ~y t))                 /\
          (c t ==> (~a t /\ ~b t /\ ~d t /\ ~e t /\ ~f t /\ ~g t /\
                    ~h t /\ ~i t /\ ~j t /\ ~k t /\ ~l t /\ ~m t /\
                    ~n t /\ ~p t /\ ~q t /\ ~r t /\ ~s t /\ ~u t /\
                    ~v t /\ ~w t /\ ~x t /\ ~y t))                 /\
          (d t ==> (~a t /\ ~b t /\ ~c t /\ ~e t /\ ~f t /\ ~g t /\
                    ~h t /\ ~i t /\ ~j t /\ ~k t /\ ~l t /\ ~m t /\
                    ~n t /\ ~p t /\ ~q t /\ ~r t /\ ~s t /\ ~u t /\
                    ~v t /\ ~w t /\ ~x t /\ ~y t))                 /\
          (e t ==> (~a t /\ ~b t /\ ~c t /\ ~d t /\ ~f t /\ ~g t /\
                    ~h t /\ ~i t /\ ~j t /\ ~k t /\ ~l t /\ ~m t /\
                    ~n t /\ ~p t /\ ~q t /\ ~r t /\ ~s t /\ ~u t /\
                    ~v t /\ ~w t /\ ~x t /\ ~y t))                 /\
          (f t ==> (~a t /\ ~b t /\ ~c t /\ ~d t /\ ~e t /\ ~g t /\
                    ~h t /\ ~i t /\ ~j t /\ ~k t /\ ~l t /\ ~m t /\
                    ~n t /\ ~p t /\ ~q t /\ ~r t /\ ~s t /\ ~u t /\
                    ~v t /\ ~w t /\ ~x t /\ ~y t))                 /\
          (g t ==> (~a t /\ ~b t /\ ~c t /\ ~d t /\ ~e t /\ ~f t /\
                    ~h t /\ ~i t /\ ~j t /\ ~k t /\ ~l t /\ ~m t /\
                    ~n t /\ ~p t /\ ~q t /\ ~r t /\ ~s t /\ ~u t /\
                    ~v t /\ ~w t /\ ~x t /\ ~y t))                 /\
          (h t ==> (~a t /\ ~b t /\ ~c t /\ ~d t /\ ~e t /\ ~f t /\
                    ~g t /\ ~i t /\ ~j t /\ ~k t /\ ~l t /\ ~m t /\
                    ~n t /\ ~p t /\ ~q t /\ ~r t /\ ~s t /\ ~u t /\
                    ~v t /\ ~w t /\ ~x t /\ ~y t))                 /\
          (i t ==> (~a t /\ ~b t /\ ~c t /\ ~d t /\ ~e t /\ ~f t /\
                    ~g t /\ ~h t /\ ~j t /\ ~k t /\ ~l t /\ ~m t /\
                    ~n t /\ ~p t /\ ~q t /\ ~r t /\ ~s t /\ ~u t /\
                    ~v t /\ ~w t /\ ~x t /\ ~y t))                 /\
          (j t ==> (~a t /\ ~b t /\ ~c t /\ ~d t /\ ~e t /\ ~f t /\
                    ~g t /\ ~h t /\ ~i t /\ ~k t /\ ~l t /\ ~m t /\
                    ~n t /\ ~p t /\ ~q t /\ ~r t /\ ~s t /\ ~u t /\
                    ~v t /\ ~w t /\ ~x t /\ ~y t))                 /\
          (k t ==> (~a t /\ ~b t /\ ~c t /\ ~d t /\ ~e t /\ ~f t /\
                    ~g t /\ ~h t /\ ~i t /\ ~j t /\ ~l t /\ ~m t /\
                    ~n t /\ ~p t /\ ~q t /\ ~r t /\ ~s t /\ ~u t /\
                    ~v t /\ ~w t /\ ~x t /\ ~y t))                 /\
          (l t ==> (~a t /\ ~b t /\ ~c t /\ ~d t /\ ~e t /\ ~f t /\
                    ~g t /\ ~h t /\ ~i t /\ ~j t /\ ~k t /\ ~m t /\
                    ~n t /\ ~p t /\ ~q t /\ ~r t /\ ~s t /\ ~u t /\
                    ~v t /\ ~w t /\ ~x t /\ ~y t))                 /\
          (m t ==> (~a t /\ ~b t /\ ~c t /\ ~d t /\ ~e t /\ ~f t /\
                    ~g t /\ ~h t /\ ~i t /\ ~j t /\ ~k t /\ ~l t /\
                    ~n t /\ ~p t /\ ~q t /\ ~r t /\ ~s t /\ ~u t /\
                    ~v t /\ ~w t /\ ~x t /\ ~y t))                 /\
          (n t ==> (~a t /\ ~b t /\ ~c t /\ ~d t /\ ~e t /\ ~f t /\
                    ~g t /\ ~h t /\ ~i t /\ ~j t /\ ~k t /\ ~l t /\
                    ~m t /\ ~p t /\ ~q t /\ ~r t /\ ~s t /\ ~u t /\
                    ~v t /\ ~w t /\ ~x t /\ ~y t))                 /\
          (p t ==> (~a t /\ ~b t /\ ~c t /\ ~d t /\ ~e t /\ ~f t /\
                    ~g t /\ ~h t /\ ~i t /\ ~j t /\ ~k t /\ ~l t /\
                    ~m t /\ ~n t /\ ~q t /\ ~r t /\ ~s t /\ ~u t /\
                    ~v t /\ ~w t /\ ~x t /\ ~y t))                 /\
          (q t ==> (~a t /\ ~b t /\ ~c t /\ ~d t /\ ~e t /\ ~f t /\
                    ~g t /\ ~h t /\ ~i t /\ ~j t /\ ~k t /\ ~l t /\
                    ~m t /\ ~n t /\ ~p t /\ ~r t /\ ~s t /\ ~u t /\
                    ~v t /\ ~w t /\ ~x t /\ ~y t))                 /\
          (r t ==> (~a t /\ ~b t /\ ~c t /\ ~d t /\ ~e t /\ ~f t /\
                    ~g t /\ ~h t /\ ~i t /\ ~j t /\ ~k t /\ ~l t /\
                    ~m t /\ ~n t /\ ~p t /\ ~q t /\ ~s t /\ ~u t /\
                    ~v t /\ ~w t /\ ~x t /\ ~y t))                 /\
          (s t ==> (~a t /\ ~b t /\ ~c t /\ ~d t /\ ~e t /\ ~f t /\
                    ~g t /\ ~h t /\ ~i t /\ ~j t /\ ~k t /\ ~l t /\
                    ~m t /\ ~n t /\ ~p t /\ ~q t /\ ~r t /\ ~u t /\
                    ~v t /\ ~w t /\ ~x t /\ ~y t))                 /\
          (u t ==> (~a t /\ ~b t /\ ~c t /\ ~d t /\ ~e t /\ ~f t /\
                    ~g t /\ ~h t /\ ~i t /\ ~j t /\ ~k t /\ ~l t /\
                    ~m t /\ ~n t /\ ~p t /\ ~q t /\ ~r t /\ ~s t /\
                    ~v t /\ ~w t /\ ~x t /\ ~y t))                 /\
          (v t ==> (~a t /\ ~b t /\ ~c t /\ ~d t /\ ~e t /\ ~f t /\
                    ~g t /\ ~h t /\ ~i t /\ ~j t /\ ~k t /\ ~l t /\
                    ~m t /\ ~n t /\ ~p t /\ ~q t /\ ~r t /\ ~s t /\ 
                    ~u t /\ ~w t /\ ~x t /\ ~y t))          /\
          (w t ==> (~a t /\ ~b t /\ ~c t /\ ~d t /\ ~e t /\ ~f t /\
                    ~g t /\ ~h t /\ ~i t /\ ~j t /\ ~k t /\ ~l t /\
                    ~m t /\ ~n t /\ ~p t /\ ~q t /\ ~r t /\ ~s t /\
                    ~u t /\ ~v t /\ ~x t /\ ~y t))                 /\
          (x t ==> (~a t /\ ~b t /\ ~c t /\ ~d t /\ ~e t /\ ~f t /\
                    ~g t /\ ~h t /\ ~i t /\ ~j t /\ ~k t /\ ~l t /\
                    ~m t /\ ~n t /\ ~p t /\ ~q t /\ ~r t /\ ~s t /\
                    ~u t /\ ~v t /\ ~w t /\ ~y t))                 /\
          (y t ==> (~a t /\ ~b t /\ ~c t /\ ~d t /\ ~e t /\ ~f t /\
                    ~g t /\ ~h t /\ ~i t /\ ~j t /\ ~k t /\ ~l t /\
                    ~m t /\ ~n t /\ ~p t /\ ~q t /\ ~r t /\ ~s t /\
                    ~u t /\ ~v t /\ ~w t /\ ~x t))
 "
  );;
>%

let ID_THM = save_thm
(`ID_THM`,
 GEN_ALL (RIGHT_BETA (REFL "(\f:*.f)x"))
 );;

timer false;;
close_theory ();;
print_theory `-`;;

%=================================================================%
% These definitions are possible alternatives to the above        %
% very specialized ones.                                          %
%=================================================================%
 
%
let one_asserted_fun = new_list_rec_definition
(`one_asserted_fun`,
 "(one_asserted_fun [] f = T) /\
  (one_asserted_fun (CONS h t) f =
          f => (~h /\ (one_asserted_fun t f))
            |  (one_asserted_fun t h))");;

let one_asserted = new_definition
(`one_asserted`, "one_asserted l = one_asserted_fun l F");;
%
