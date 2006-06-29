%                                                                   %
% FILE: DP_proofs.ml                                                %
%                                                                   %
% DESCRIPTION: This proves some properties of the register-         %
%              transfer definition of the datapath.                 %
%                                                                   %
% USES FILES:  rt_DP.th,                                            %
%              wordn library                                        %
%                                                                   %
% Brian Graham 04.10.89                                             %
%                                                                   %
% Modifications:                                                    %
% 16.10.89 - BtG - make this into an equality proof, so that        %
%                  the next level can substitute directly.          %
% 21.11.91 - BtG - updated to HOL2.                                 %
% ================================================================= %
new_theory `DP_proofs`;;

loadf `wordn`;;

map new_parent [ `rt_DP`
	       ; `constraints`
               ];;

load_all `rt_DP`;;
load_definition `constraints` `clock_constraint`;;
load_theorem `interface` `ID_THM`;;

load_library `unwind`;;

loadt `BINDER_EQ_TAC`;;

let CONJUNCTS_TAC (asl,t) =
  ACCEPT_TAC (CONJUNCTS_CONV (dest_eq t))(asl,t);;
% ================================================================= %
let mtime = ":num";;

let msig = ":^mtime->bool"
and w2_mvec = ":^mtime->word2"
and w14_mvec = ":^mtime->word14"
and w28_mvec = ":^mtime->word28"
and w32_mvec = ":^mtime->word32";;
% ================================================================= %

timer true;;
% ================================================================= %
% First, unfold the datapath, and see how simplified an expression  %
% can be obtained.                                                  %
% ================================================================= %
let DP_unwound_lemma = prove_thm
(`DP_unwound_lemma`,
 "(one_asserted_12 
    replcar 
    replcdr 
    sub 
    add 
    dec 
    mul 
    div 
    rem 
    setbit30 
    setbit31 
    resetbit30 
    resetbit31) ==>
 (clock_constraint SYS_Clocked) ==>
 (DP bus_bits mem_bits SYS_Clocked
     rmem 
     mar      wmar      rmar      rnum rnil rtrue rfalse
     s        ws        rs
     e        we        re
     c        wc        rc
     d        wd        rd
     free     wfree     rfree
     parent   wparent   rparent
     root     wroot     rroot
     y1       wy1       ry1
     x1       wx1       rx1
     x2       wx2       rx2
     y2       wy2       ry2       rcons
     car      wcar      rcar
     atomflag bit30flag bit31flag zeroflag nilflag eqflag leqflag
     arg      warg      rarg
     buf1     wbuf1     rbuf1
     buf2     wbuf2     rbuf2
     replcar  replcdr   sub add dec mul div rem
     setbit30 setbit31  resetbit30 resetbit31
     ralu =
   ?alu.
    !t.
    (rmem t   ==> (bus_bits t           = mem_bits t))      /\
    (rmar t   ==> (cdr_bits(bus_bits t) = mar t))           /\
    (rmar t   ==> (car_bits(bus_bits t) = ZEROS14))         /\
    (rnum t   ==> (cdr_bits(bus_bits t) = NUM_addr))        /\
    (rnum t   ==> (car_bits(bus_bits t) = ZEROS14))         /\
    (rnil t   ==> (cdr_bits(bus_bits t) = NIL_addr))        /\
    (rtrue t  ==> (cdr_bits(bus_bits t) = T_addr))          /\
    (rfalse t ==> (cdr_bits(bus_bits t) = F_addr))          /\
    (rs t     ==> (cdr_bits(bus_bits t) = s  t))            /\
    (re t     ==> (cdr_bits(bus_bits t) = e  t))            /\
    (rc t     ==> (cdr_bits(bus_bits t) = c  t))            /\
    (rd t     ==> (cdr_bits(bus_bits t) = d  t))            /\
    (rfree t  ==> (cdr_bits(bus_bits t) = free t))          /\
    (rx1 t    ==> (cdr_bits(bus_bits t) = x1 t))            /\
    (rx2 t    ==> (cdr_bits(bus_bits t) = x2 t))            /\
    (rparent t ==> (cdr_bits(bus_bits t) = parent t))        /\
    (rroot t  ==> (cdr_bits(bus_bits t) = root t))          /\
    (ry1 t    ==> (cdr_bits(bus_bits t) = y1 t))            /\
    (ry2 t    ==> (cdr_bits(bus_bits t) = y2 t))            /\

    ((rcons t ==> (garbage_bits(bus_bits t)  = #00))        /\
     (rcons t ==> (rec_type_bits(bus_bits t) = RT_CONS))    /\
     (rcons t ==> (car_bits(bus_bits t)      = x1 t))       /\
     (rcons t ==> (cdr_bits(bus_bits t)      = x2 t)))      /\

    (rcar t  ==> (cdr_bits(bus_bits t) = car  t))           /\
    (rarg t  ==> (bus_bits t           = arg  t))           /\
    (rbuf1 t ==> (bus_bits t           = buf1 t))           /\
    (rbuf2 t ==> (bus_bits t           = buf2 t))           /\

    (ralu t  ==> (bus_bits t           = alu  t))           /\

    (sub t ==> (alu t = SUB28(atom_bits(arg t))
                                 (atom_bits(bus_bits t))))      /\
    (add t ==> (alu t = ADD28(atom_bits(arg t))
                                 (atom_bits(bus_bits t))))      /\
    (dec t ==> (alu t = DEC28(atom_bits(arg t))))      /\
    (mul t ==> (alu t = DEC28(atom_bits(arg t))))      /\
    (div t ==> (alu t = DEC28(atom_bits(arg t))))      /\
    (rem t ==> (alu t = DEC28(atom_bits(arg t))))      /\
    (replcar    t ==> (alu t = REPLCAR(arg t)(y2 t)))  /\
    (replcdr    t ==> (alu t = REPLCDR(arg t)(y2 t)))  /\
    (setbit31   t ==> (alu t = SETBIT31(arg t)))       /\
    (setbit30   t ==> (alu t = SETBIT30(arg t)))       /\
    (resetbit31 t ==> (alu t = RESETBIT31(arg t)))     /\
    (resetbit30 t ==> (alu t = RESETBIT30(arg t)))     /\
    (buf1 t = (wbuf1 t => alu t | buf1 (PRE t))) /\
    (buf2 t = (wbuf2 t => alu t | buf2 (PRE t))) /\

    (mar    t = (wmar t    => cdr_bits(bus_bits t)| mar  (PRE t))) /\
    (s      t = (ws t      => cdr_bits(bus_bits t)| s    (PRE t))) /\
    (e      t = (we t      => cdr_bits(bus_bits t)| e    (PRE t))) /\
    (c      t = (wc t      => cdr_bits(bus_bits t)| c    (PRE t))) /\
    (d      t = (wd t      => cdr_bits(bus_bits t)| d    (PRE t))) /\
    (free   t = (wfree t   => cdr_bits(bus_bits t)| free (PRE t))) /\
    (x1     t = (wx1 t     => cdr_bits(bus_bits t)| x1   (PRE t))) /\
    (x2     t = (wx2 t     => cdr_bits(bus_bits t)| x2   (PRE t))) /\
    (car    t = (wcar t    => car_bits(bus_bits t)| car  (PRE t))) /\
    (arg    t = (warg t    =>          bus_bits t | arg  (PRE t))) /\
    (parent t = (wparent t => cdr_bits(bus_bits t)|parent(PRE t))) /\
    (root   t = (wroot t   => cdr_bits(bus_bits t)| root (PRE t))) /\
    (y1     t = (wy1 t     => cdr_bits(bus_bits t)| y1   (PRE t))) /\
    (y2     t = (wy2 t     => cdr_bits(bus_bits t)| y2   (PRE t))) /\

    (atomflag  t = is_atom(bus_bits t))                      /\
    (bit30flag t = field_bit(bus_bits t))                    /\
    (bit31flag t = mark_bit(bus_bits t))                     /\
    (zeroflag  t = (atom_bits(bus_bits t) = ZERO28))         /\
    (nilflag   t = (cdr_bits(bus_bits t) = NIL_addr))        /\
    (eqflag    t = (bus_bits t = arg t))                     /\
    (leqflag   t = LEQ_prim(arg t)(bus_bits t)))",

 SUBST1_TAC (SPEC_ALL DP)
 THEN DISCH_THEN
      (\th.  port[ READ_MEM; MAR; NUM; Nil; TRUE; FALSE;
                   S_reg; E_reg; C_reg; D_reg; 
                   FREE_reg; PARENT_reg; ROOT_reg; Y1_reg; X1_reg;
                   X2_reg; Y2_reg; ARG_reg; BUF1_reg; BUF2_reg;
                   Cons; CAR_reg; FLAGSUNIT;
		   (rr [th] (SPEC_ALL ALU))])
 THEN port[ register; busgate ]
 THEN DISCH_THEN
  (\th. port
       (map 
        ((rr [porr [clock_constraint] th])
         o (SPEC "SYS_Clocked:num->bool")
         o (GEN "clocked:num->bool")
         o SPEC_ALL)
         [ reg ]))
 THEN BINDER_EQ_TAC
 THEN in_conv_tac let_CONV
 THEN BETA_TAC
 THEN in_conv_tac AND_FORALL_CONV
 THEN BINDER_EQ_TAC
 THEN CONJUNCTS_TAC
 );;

timer false;;
close_theory ();;
print_theory `-`;;
