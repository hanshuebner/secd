new_theory `simplify`;;

timer true;;

map new_parent
 [ `mu-prog_LD`
 ; `mu-prog_LDC`
 ; `mu-prog_LDF`
 ; `mu-prog_AP`
 ; `mu-prog_RTN`
 ; `mu-prog_DUM`
 ; `mu-prog_RAP`
 ; `mu-prog_SEL`
 ; `mu-prog_JOIN`
 ; `mu-prog_CAR`
 ; `mu-prog_CDR`
 ; `mu-prog_ATOM`
 ; `mu-prog_CONS`
 ; `mu-prog_EQ`
 ; `mu-prog_ADD`
 ; `mu-prog_SUB`
 ; `mu-prog_LEQ`
 ; `mu-prog_STOP`
 ];;

let mtime = ":num";;
let w14_mvec = ":^mtime->word14";;
% ================================================================= %
% A conversion to abstract out a term.                              %
%                                                                   %
% Usage:                                                            %
% ******                                                            %
% BETA_INV_CONV : ((term # term) -> conv)                           %
%                                                                   %
%                   t[t2]                                           %
%       ------------------------------(t1,t2)                       %
%        |- t[t2] = (\t1.t[t1/t2]) t2                               %
%                                                                   %
% Example:                                                          %
% ********                                                          %
% #BETA_INV_CONV ("t1:num", "SUC t") "PRE(SUC t)";;                 %
% |- PRE(SUC t) = (\t1. PRE t1)(SUC t)                              %
% ================================================================= %
let BETA_INV_CONV (t1,t2) trm =
 (SYM o RIGHT_BETA)
 (REFL(mk_comb (mk_abs(t1,subst [t1,t2] trm), t2)));;

% ================================================================= %
% Permit introduction of "LET" bindings anywhere...                 %
% ================================================================= %
let LET_THM = prove_thm
(`LET_THM`,
 "LET (f:*->**) (x:*) = f x",
 port[LET_DEF]
 THEN in_conv_tac BETA_CONV
 THEN REFL_TAC);;

% ================================================================= %
% A conversion(al) for getting at the body of an abstraction.       %
% ================================================================= %
let ABS_CONV conv tm =
 (let bv,body = dest_abs tm in
  let bodyth = conv body in
  (ABS bv bodyth)) ? failwith `ABS_CONV`;;

let mem1 = "mem1:word14->word32";;
let mem2 = "mem2:word14->word32";;
let mem3 = "mem3:word14->word32";;
let mem4 = "mem4:word14->word32";;
	     
letrec crafty_RULE vt_list conv th =
  (vt_list = [])
  => th
   | crafty_RULE (tl vt_list)
                 (RATOR_CONV o RAND_CONV o ABS_CONV o conv)
                 ((CONV_RULE
                   o conv)
                  (BETA_INV_CONV (fst(hd vt_list), snd(hd vt_list))
                   THENC REWR_CONV (SYM_RULE LET_THM))
                  th)
 ;;

%  %
% ================================================================= %
% First the hardest one as an example:                              %
%                                                                   %
% ......                                                            %
% |- let mem1 =                                                     %
%           Store14                                                 %
%           (free t)                                                %
%           (bus32_cons_append                                      %
%            #00                                                    %
%            RT_CONS                                                %
%            (cdr_bits(memory t(c t)))                              %
%            (d  t))                                                %
%           (memory t)                                              %
%    in                                                             %
%    let mem2 =                                                     %
%          Store14                                                  %
%          (cdr_bits(memory t(free t)))                             %
%          (bus32_cons_append                                       %
%           #00                                                     %
%           RT_CONS                                                 %
%           (cdr_bits(mem1(e  t)))                                  %
%           (free t))                                               %
%          mem1                                                     %
%    in                                                             %
%    let mem3 =                                                     %
%          Store14                                                  %
%          (cdr_bits(mem1(cdr_bits(memory t(free t)))))             %
%          (bus32_cons_append                                       %
%           #00                                                     %
%           RT_CONS                                                 %
%           (cdr_bits(mem2(cdr_bits(mem2(s  t)))))                  %
%           (cdr_bits(memory t(free t))))                           %
%          mem2                                                     %
%    in                                                             %
%    let mem4 =                                                     %
%          Store14                                                  %
%          (cdr_bits(mem3(car_bits(mem3(s  t)))))                   %
%          (bus32_cons_append                                       %
%           #00                                                     %
%           RT_CONS                                                 %
%           (car_bits(mem3(cdr_bits(mem3(s  t)))))                  %
%           (cdr_bits                                               %
%            (mem3(cdr_bits(mem3(car_bits(mem3(s  t))))))))         %
%          mem3                                                     %
%    in                                                             %
%    ((mpc(t + 48) = #000101011) /\                                 %
%     (memory(t + 48) = mem4) /\                                    %
%     (s (t + 48) = NIL_addr) /\                                    %
%     (e (t + 48) = cdr_bits(mem3(car_bits(mem3(s  t))))) /\        %
%     (c (t + 48) = car_bits(mem4(car_bits(mem4(s  t))))) /\        %
%     (d (t + 48) = cdr_bits(mem1(cdr_bits(memory t(free t))))) /\  %
%     (free(t + 48) =                                               %
%      cdr_bits                                                     %
%      (mem2(cdr_bits(mem1(cdr_bits(memory t(free t))))))))         %
% ================================================================= %
let m1_expr = 
  "Store14 (free (t:^mtime))
           (bus32_cons_append 
            #00 
            RT_CONS
            (cdr_bits(memory t(c  t)))
            (d  t))
           (memory t)";;
let m2_expr =
  "Store14 (cdr_bits(memory (t:^mtime)(free t)))
           (bus32_cons_append 
            #00 
            RT_CONS
            (cdr_bits(mem1(e  t)))
            (free t))
           mem1";;
let m3_expr =
  "Store14 (cdr_bits(mem1(cdr_bits(memory (t:^mtime)((free:^mtime->word14) t)))))
           (bus32_cons_append 
            #00 
            RT_CONS
            (cdr_bits(mem2(cdr_bits(mem2(s  t)))))
            (cdr_bits(memory t(free t))))
           mem2";;
let m4_expr =
  "Store14 (cdr_bits(mem3(car_bits(mem3((s:^mtime->word14) t)))))
           (bus32_cons_append 
            #00 
            RT_CONS
            (car_bits(mem3(cdr_bits(mem3(s t)))))
            (cdr_bits(mem3(cdr_bits(mem3(car_bits(mem3(s t))))))))
           mem3";;

let reduced_RAP_state = save_thm
(`reduced_RAP_state`,
 crafty_RULE [mem1,m1_expr; mem2,m2_expr; mem3,m3_expr; mem4,m4_expr]
             I
             (theorem `mu-prog_RAP` `RAP_state`)
);;

% ================================================================= %
% LD                                                                %
% ================================================================= %
let m,m_expr =  ("m:num",
 "pos_num_of(iVal(Bits28(atom_bits(memory (t:^mtime)
                         (car_bits(memory t
                          (car_bits(memory t
                           (cdr_bits(memory t(c t)))))))))))");;
let n,n_expr =  ("n:num",
 "pos_num_of(iVal(Bits28(atom_bits(memory (t:^mtime)
                         (cdr_bits(memory t
                          (car_bits(memory t
                           (cdr_bits(memory t(c t)))))))))))");;
let m1_expr = 
 "Store14 (free (t:^mtime))
          (bus32_cons_append 
           #00 
           RT_CONS
           (car_bits
            (memory t
             (nth n
                  (cdr_bits o (memory t))
                  (car_bits
                   (memory t
                    (nth m
                         (cdr_bits o (memory t))
                         (e t)))))))
           (s t))
          (memory t)";;


let reduced_LD_state = save_thm
(`reduced_LD_state`,
 crafty_RULE [m, m_expr; n, n_expr; mem1,m1_expr]
             I
             (theorem `mu-prog_LD` `LD_state`)
);;

% ================================================================= %
% LDC                                                               %
% ================================================================= %
let m1_expr =
"Store14 (free (t:^mtime))
         (bus32_cons_append 
          #00 
          RT_CONS
          (car_bits(memory t(cdr_bits(memory t(c t)))))
          (s t))
         (memory t)";;

let reduced_LDC_state = save_thm
(`reduced_LDC_state`,
 crafty_RULE [mem1,m1_expr]
             I
             (theorem `mu-prog_LDC` `LDC_state`)
);;
% ================================================================= %
% LDF                                                               %
% ================================================================= %
let m1_expr =
"Store14 ((free:^w14_mvec) t)
         (bus32_cons_append 
          #00 
          RT_CONS
          (car_bits(memory t(cdr_bits(memory t(c t)))))
          (e t))
         (memory t)";;

let m2_expr = 
"Store14 (cdr_bits(memory (t:^mtime)(free t)))
         (bus32_cons_append #00 RT_CONS(free t)(s t))
         mem1";;

let reduced_LDF_state = save_thm
(`reduced_LDF_state`,
 crafty_RULE [mem1,m1_expr; mem2, m2_expr]
             I
             (theorem `mu-prog_LDF` `LDF_state`)
);;

% ================================================================= %
% AP                                                                %
% ================================================================= %
let m1_expr = 
  "Store14 (free (t:^mtime))
           (bus32_cons_append 
            #00 
            RT_CONS
            (cdr_bits(memory t(c t)))
            (d t))
           (memory t)";;
let m2_expr =
  "Store14 (cdr_bits(memory (t:^mtime)(free t)))
           (bus32_cons_append #00 RT_CONS(e t)(free t))
           mem1";;
let m3_expr =
  "Store14 (cdr_bits(mem1(cdr_bits(memory (t:^mtime)((free:^mtime->word14) t)))))
           (bus32_cons_append 
            #00 
            RT_CONS
            (cdr_bits(mem2(cdr_bits(mem2(s t)))))
            (cdr_bits(memory t(free t))))
           mem2";;
let m4_expr =
  "Store14 (cdr_bits(mem2(cdr_bits(mem1(cdr_bits(memory t((free:^w14_mvec) (t:^mtime))))))))
           (bus32_cons_append 
            #00 
            RT_CONS
            (car_bits(mem3(cdr_bits(mem3(s t)))))
            (cdr_bits(mem3(car_bits(mem3(s t))))))
           mem3";;

%<         developing the correct let bound expressions ...

let tm' = (snd o dest_abs o fst o dest_comb o snd o dest_eq o concl)
          (BETA_INV_CONV (mem1,m1_expr)
			 (concl (theorem `mu-prog_AP` `AP_state`)));;
let tm'' = (snd o dest_abs o fst o dest_comb o snd o dest_eq o concl)
          (BETA_INV_CONV (mem2,m2_expr) tm');;
let tm''' = (snd o dest_abs o fst o dest_comb o snd o dest_eq o concl)
          (BETA_INV_CONV (mem3,m3_expr) tm'');;
let tm'''' = (snd o dest_abs o fst o dest_comb o snd o dest_eq o concl)
          (BETA_INV_CONV (mem4,m4_expr) tm''');;
>%

let reduced_AP_state = save_thm
(`reduced_AP_state`,
 crafty_RULE [mem1,m1_expr; mem2,m2_expr; mem3,m3_expr; mem4,m4_expr]
             I
             (theorem `mu-prog_AP` `AP_state`)
);;

% ================================================================= %
% RTN                                                               %
% ================================================================= %
let m1_expr =
"Store14 ((free:^w14_mvec) t)
         (bus32_cons_append 
          #00 
          RT_CONS
          (car_bits(memory t(s t)))
          (car_bits(memory t(d t))))
         (memory t)";;

let reduced_RTN_state = save_thm
(`reduced_RTN_state`,
 crafty_RULE [mem1,m1_expr]
             I
             (theorem `mu-prog_RTN` `RTN_state`)
);;

% ================================================================= %
% DUM                                                               %
% ================================================================= %
let m1_expr =
"Store14 ((free:^w14_mvec) t)
         (bus32_cons_append 
          #00 
          RT_CONS
          NIL_addr
          (e t))
         (memory t)";;

let reduced_DUM_state = save_thm
(`reduced_DUM_state`,
 crafty_RULE [mem1,m1_expr]
             I
             (theorem `mu-prog_DUM` `DUM_state`)
);;

% ================================================================= %
% SEL                                                               %
% ================================================================= %
let m1_expr =
"Store14 ((free:^w14_mvec) t)
         (bus32_cons_append 
          #00 
          RT_CONS
          (cdr_bits(memory t(cdr_bits(memory t(cdr_bits(memory t(c t)))))))
          (d t))
         (memory t)";;

let reduced_SEL_state = save_thm
(`reduced_SEL_state`,
 crafty_RULE [mem1,m1_expr]
             I
             (theorem `mu-prog_SEL` `SEL_state`)
);;

% ================================================================= %
% JOIN                                                              %
% ================================================================= %

% ================================================================= %
% CAR                                                               %
% ================================================================= %
let m1_expr =
"Store14 ((free:^w14_mvec) t)
         (bus32_cons_append 
          #00 
          RT_CONS
          (car_bits(memory t(car_bits(memory t(s t)))))
          (cdr_bits(memory t(s t))))
         (memory t)";;

let reduced_CAR_state = save_thm
(`reduced_CAR_state`,
 crafty_RULE [mem1,m1_expr]
             I
             (theorem `mu-prog_CAR` `CAR_state`)
);;

% ================================================================= %
% CDR                                                               %
% ================================================================= %
let m1_expr =
"Store14 ((free:^w14_mvec) t)
         (bus32_cons_append 
          #00 
          RT_CONS
          (cdr_bits(memory t(car_bits(memory t(s t)))))
          (cdr_bits(memory t(s t))))
         (memory t)";;

let reduced_CDR_state = save_thm
(`reduced_CDR_state`,
 crafty_RULE [mem1,m1_expr]
             I
             (theorem `mu-prog_CDR` `CDR_state`)
);;

% ================================================================= %
% ATOM                                                              %
% ================================================================= %
let m1_expr =
"Store14 ((free:^w14_mvec) t)
         (bus32_cons_append 
          #00 
          RT_CONS
          T_addr
          (cdr_bits(memory t(s t))))
         (memory t)";;

let m2_expr = 
"Store14 ((free:^w14_mvec) t)
         (bus32_cons_append 
          #00 
          RT_CONS
          F_addr
          (cdr_bits(memory t(s t))))
         (memory t)";;

let reduced_ATOM_state = save_thm
(`reduced_ATOM_state`,
 crafty_RULE [mem1,m1_expr; mem2, m2_expr]
             I
             (theorem `mu-prog_ATOM` `ATOM_state`)
);;

% ================================================================= %
% CONS                                                              %
% ================================================================= %
let m1_expr =
"Store14 ((free:^w14_mvec) t)
         (bus32_cons_append 
          #00 
          RT_CONS
          (car_bits(memory t(s t)))
          (car_bits(memory t(cdr_bits(memory t(s t))))))
         (memory t)";;

let m2_expr = 
"Store14 (cdr_bits(memory (t:^mtime)(free t)))
         (bus32_cons_append
          #00
          RT_CONS
          (free t)
          (cdr_bits (mem1(cdr_bits (mem1(s t))))))
         mem1";;

let reduced_CONS_state = save_thm
(`reduced_CONS_state`,
 crafty_RULE [mem1,m1_expr; mem2, m2_expr]
             I
             (theorem `mu-prog_CONS` `CONS_state`)
);;


% ================================================================= %
% EQ                                                                %
% ================================================================= %
let m1_expr =
"Store14 ((free:^w14_mvec) t)
         (bus32_cons_append 
          #00 
          RT_CONS
          T_addr
          (cdr_bits(memory t(cdr_bits(memory t(s t))))))
         (memory t)";;

let m2_expr = 
"Store14 ((free:^w14_mvec) t)
         (bus32_cons_append 
          #00 
          RT_CONS
          F_addr
          (cdr_bits(memory t(cdr_bits(memory t(s t))))))
         (memory t)";;

let reduced_EQ_state = save_thm
(`reduced_EQ_state`,
 crafty_RULE [mem1,m1_expr; mem2, m2_expr]
             I
             (theorem `mu-prog_EQ` `EQ_state`)
);;

% ================================================================= %
% ADD                                                               %
% ================================================================= %
let m1_expr =
"Store14 ((free:^w14_mvec) t)
         (ADD28
          (atom_bits
           (memory t(car_bits(memory t(cdr_bits(memory t(s t)))))))
          (atom_bits(memory t(car_bits(memory t(s t))))))
         (memory t)";;

let m2_expr = 
"Store14 (cdr_bits(memory (t:^mtime)(free t)))
         (bus32_cons_append
          #00
          RT_CONS
          (free t)
          (cdr_bits (mem1(cdr_bits(mem1(s t))))))
         mem1";;

let reduced_ADD_state = save_thm
(`reduced_ADD_state`,
 crafty_RULE [mem1,m1_expr; mem2, m2_expr]
             I
             (theorem `mu-prog_ADD` `ADD_state`)
);;

% ================================================================= %
% SUB                                                               %
% ================================================================= %
let m1_expr =
"Store14 ((free:^w14_mvec) t)
         (SUB28
          (atom_bits
           (memory t(car_bits(memory t(cdr_bits(memory t(s t)))))))
          (atom_bits(memory t(car_bits(memory t(s t))))))
         (memory t)";;

let m2_expr = 
"Store14 (cdr_bits(memory (t:^mtime)(free t)))
         (bus32_cons_append
          #00
          RT_CONS
          (free t)
          (cdr_bits (mem1(cdr_bits(mem1(s t))))))
         mem1";;

let reduced_SUB_state = save_thm
(`reduced_SUB_state`,
 crafty_RULE [mem1,m1_expr; mem2, m2_expr]
             I
             (theorem `mu-prog_SUB` `SUB_state`)
);;

% ================================================================= %
% LEQ                                                               %
% ================================================================= %
let m1_expr =
"Store14 ((free:^w14_mvec) t)
         (bus32_cons_append 
          #00 
          RT_CONS
          T_addr
          (cdr_bits(memory t(cdr_bits(memory t(s t))))))
         (memory t)";;

let m2_expr = 
"Store14 ((free:^w14_mvec) t)
         (bus32_cons_append 
          #00 
          RT_CONS
          F_addr
          (cdr_bits(memory t(cdr_bits(memory t(s t))))))
         (memory t)";;

let reduced_LEQ_state = save_thm
(`reduced_LEQ_state`,
 crafty_RULE [mem1,m1_expr; mem2, m2_expr]
             I
             (theorem `mu-prog_LEQ` `LEQ_state`)
);;

% ================================================================= %
% STOP                                                              %
% ================================================================= %

timer false;;
close_theory ();;
print_theory `-`;;
