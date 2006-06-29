% SECD verification                                                 %
%                                                                   %
% FILE:         SECD_proofs.ml                                      %
%                                                                   %
% DESCRIPTION:  Unfolds the top level imp view of the SECD chip.    %
%                                                                   %
% USES FILES:   rt_SECD.th                                          %
%               CU_proofs.th                                        %
%               DP_proofs.th                                        %
%               MOVE_EXISTS_OUT_CONV.ml                             %
%               EXISTS_PERM_LIST.ml                                 %
%               BINDER_EQ_TAC.ml                                    %
%               SPLIT_CONJUNCTS.ml                                  %
%               CONJUNCTS_TAC.ml                                    %
%                                                                   %
% Brian Graham 06.11.89                                             %
%                                                                   %
% Modifications:                                                    %
% 21.11.91 - BtG - updated to HOL2                                  %
% ================================================================= %
new_theory `SECD_proofs`;;

loadf `wordn`;;

map new_parent [ `rt_SECD`
	       ; `CU_proofs`
	       ; `DP_proofs`
               ];;

let mtime = ":num";;

let msig = ":^mtime->bool"
and w9_mvec = ":^mtime->word9"
and w14_mvec = ":^mtime->word14"
and w27_mvec = ":^mtime->word27"
and w32_mvec = ":^mtime->word32";;

% ================================================================= %
% A number of useful tactics and conversions are used :             %
% ================================================================= %
load_library `unwind`;;
map loadt
[ `MOVE_EXISTS_OUT_CONV`
; `EXISTS_PERM_LIST`
; `BINDER_EQ_TAC`
; `SPLIT_CONJUNCTS`
; `CONJUNCTS_TAC`
];;

load_theorem `rt_PADS` `PF_lemma`;;
load_theorem `DP_proofs` `DP_unwound_lemma`;;
load_theorem `CU_proofs` `alucntl_one_asserted_lemma`;;
% ================================================================= %
letrec my_conjuncts w =
 (let a,b = dest_conj w in a . my_conjuncts b) ? [w];;

let my_FRONT_CONJ_CONV tm =
 let al = my_conjuncts tm
 in
 FRONT_CONJ_CONV al (el (length al) al);;

timer true;;
% ================================================================= %
% At one level up, we want to eliminate the one-asserted property   %
% in the unfolding above.                                           %
% ================================================================= %
let interface_elim_lemma = TAC_PROOF
(([],"!a' d' b' b''.
      (a'==>d') ==> (d'==>(b':bool = b''))
              ==>
              (a' /\ b' /\ c' = a' /\ b'' /\ c')"),
 REPEAT GEN_TAC
 THEN DISCH_THEN
 (\th1. DISCH_THEN
  (\th2. ASSUME_TAC (IMP_TRANS th1 th2)))
 THEN EQ_TAC
 THEN STRIP_TAC
 THEN RES_TAC
 THEN art[]);;

% ================================================================= %
% Load earlier theorems.  Note the theorems loaded are specialized  %
% right away for their use later:                                   %
% - DP_lemma puts the Clock_constraint" on the asm list.            %
% - one_asserted_lemma is specialized for substitution.             %
% - both are used in lemma, to eliminate the one-asserted           %
%   property in the definition of the ALU in the DP.  This          %
%   property has been proven from the CU implementation, and by     %
%   using the interface elim lemma, is eliminated from the          %
%   rewritten form.                                                 %
% ================================================================= %
let DP_lemma =
  (\th. let a1,a2,ccl = ((I # dest_imp) o dest_imp) (concl th)
   in
   (DISCH a1 (UNDISCH_ALL th)))
  DP_unwound_lemma;;

let one_asserted_lemma =
  (SPEC "Opcode arg" o (GEN "opcode:^w9_mvec")) 
  alucntl_one_asserted_lemma;;

let lemma =
  (MATCH_MP 
   (MATCH_MP interface_elim_lemma (one_asserted_lemma))
   DP_lemma) ;;

% ================================================================= %

% ================================================================= %
% ================================================================= %
% The initial goal will serve to unfold the definition, and try out %
% various simplifications.  Fundamental objectives:                 %
% * eliminate the "one_asserted_12 constraint from DP definition    %
% * replace hidden wires that are in or out pad connections         %
% ================================================================= %
let SECD_lemma = prove_thm
(`SECD_lemma`,
 "(clock_constraint SYS_Clocked) ==>
   (SECD
    (SYS_Clocked:^mtime->bool) 
    (mpc:^w9_mvec)
    (s0:^w9_mvec)         (s1:^w9_mvec)
    (s2:^w9_mvec)         (s3:^w9_mvec)
    (button_pin:^msig)   
    (flag0_pin:^msig)     (flag1_pin:^msig) 
    (write_bit_pin:^msig) (rmem_pin:^msig)
    (bus_pins:^w32_mvec)  (mar_pins:^w14_mvec) 
    (s :^w14_mvec)        (e :^w14_mvec)
    (c :^w14_mvec)        (d :^w14_mvec)
    (free:^w14_mvec) 
    (x1:^w14_mvec)        (x2:^w14_mvec)
    (y1:^w14_mvec)        (y2:^w14_mvec)
    (car:^w14_mvec)
    (root:^w14_mvec)      (parent:^w14_mvec)
    (buf1:^w32_mvec)      (buf2:^w32_mvec)
    (arg:^w32_mvec) = 

    ? 
      (atomflag:^msig)  (bit30flag:^msig) (bit31flag:^msig)
      (zeroflag:^msig)  (nilflag:^msig)   (eqflag:^msig)
      (leqflag:^msig)
      (ralu:^msig)      (rarg:^msig)
      (rbuf1:^msig)     (rbuf2:^msig)     (rcar:^msig)
      (rs:^msig)        (re:^msig)        (rc:^msig)
      (rd:^msig)        (rmar:^msig)      (rx1:^msig)
      (rx2:^msig)       (rfree:^msig)     (rparent:^msig)
      (rroot:^msig)     (ry1:^msig)       (ry2:^msig)
      (rnum:^msig)      (rnil:^msig)      (rtrue:^msig) 
      (rfalse:^msig)    (rcons:^msig)
      (bidir:^msig)
      (warg:^msig)      (wbuf1:^msig)
      (wbuf2:^msig)     (wcar:^msig)      (ws:^msig)
      (we:^msig)        (wc:^msig)        (wd:^msig)
      (wmar:^msig)      (wx1:^msig)       (wx2:^msig)
      (wfree:^msig)     (wparent:^msig)   (wroot:^msig)
      (wy1:^msig)       (wy2:^msig)
      (dec:^msig)       (add:^msig)       (sub:^msig)
      (mul:^msig)       (div:^msig)       (rem:^msig)
      (setbit30:^msig)  (setbit31:^msig)  (resetbit31:^msig)
      (replcar:^msig)   (replcdr:^msig)   (resetbit30:^msig)
      (bus_bits:^w32_mvec) (mem_bits:^w32_mvec)
      (alu:^w32_mvec)
      .

    (CU  SYS_Clocked
         button_pin
         mpc s0 s1 s2 s3
         (Opcode arg)
         atomflag bit30flag bit31flag zeroflag nilflag eqflag leqflag
         flag0_pin flag1_pin
         ralu rmem_pin rarg rbuf1 rbuf2 rcar rs re rc rd rmar rx1 rx2
         rfree rparent rroot ry1 ry2 rnum rnil rtrue rfalse rcons
         write_bit_pin bidir
         warg wbuf1 wbuf2 wcar ws we wc wd wmar wx1 wx2
         wfree wparent wroot wy1 wy2
         dec add sub mul div rem
         setbit30 setbit31 resetbit31 replcar replcdr resetbit30) /\
   (!t.
    (rmem_pin t   ==> (bus_bits t           = mem_bits t))      /\
    (rmar t       ==> (cdr_bits(bus_bits t) = mar_pins t))      /\
    (rmar t       ==> (car_bits(bus_bits t) = ZEROS14))         /\
    (rnum t       ==> (cdr_bits(bus_bits t) = NUM_addr))        /\
    (rnum t       ==> (car_bits(bus_bits t) = ZEROS14))         /\
    (rnil t       ==> (cdr_bits(bus_bits t) = NIL_addr))        /\
    (rtrue t      ==> (cdr_bits(bus_bits t) = T_addr))          /\
    (rfalse t     ==> (cdr_bits(bus_bits t) = F_addr))          /\
    (rs t         ==> (cdr_bits(bus_bits t) = s  t))            /\
    (re t         ==> (cdr_bits(bus_bits t) = e  t))            /\
    (rc t         ==> (cdr_bits(bus_bits t) = c  t))            /\
    (rd t         ==> (cdr_bits(bus_bits t) = d  t))            /\
    (rfree t      ==> (cdr_bits(bus_bits t) = free t))          /\
    (rx1 t        ==> (cdr_bits(bus_bits t) = x1 t))            /\
    (rx2 t        ==> (cdr_bits(bus_bits t) = x2 t))            /\
    (rparent t    ==> (cdr_bits(bus_bits t) = parent t))        /\
    (rroot t      ==> (cdr_bits(bus_bits t) = root t))          /\
    (ry1 t        ==> (cdr_bits(bus_bits t) = y1 t))            /\
    (ry2 t        ==> (cdr_bits(bus_bits t) = y2 t))            /\
    ((rcons t     ==> (garbage_bits(bus_bits t)  = #00))        /\
     (rcons t     ==> (rec_type_bits(bus_bits t) = RT_CONS))    /\
     (rcons t     ==> (car_bits(bus_bits t)      = x1 t))       /\
     (rcons t     ==> (cdr_bits(bus_bits t)      = x2 t)))      /\
    (rcar t       ==> (cdr_bits(bus_bits t) = car  t))          /\
    (rarg t       ==> (bus_bits t           = arg  t))          /\
    (rbuf1 t      ==> (bus_bits t           = buf1 t))          /\
    (rbuf2 t      ==> (bus_bits t           = buf2 t))          /\
    (ralu t       ==> (bus_bits t           = alu  t))          /\
    (sub t        ==> (alu t = SUB28(atom_bits(arg t))
                                    (atom_bits(bus_bits t))))   /\
    (add t        ==> (alu t = ADD28(atom_bits(arg t))
                                    (atom_bits(bus_bits t))))   /\
    (dec t        ==> (alu t = DEC28(atom_bits(arg t))))        /\
    (mul t        ==> (alu t = DEC28(atom_bits(arg t))))        /\
    (div t        ==> (alu t = DEC28(atom_bits(arg t))))        /\
    (rem t        ==> (alu t = DEC28(atom_bits(arg t))))        /\
    (replcar    t ==> (alu t = REPLCAR(arg t)(y2 t)))           /\
    (replcdr    t ==> (alu t = REPLCDR(arg t)(y2 t)))           /\
    (setbit31   t ==> (alu t = SETBIT31(arg t)))                /\
    (setbit30   t ==> (alu t = SETBIT30(arg t)))                /\
    (resetbit31 t ==> (alu t = RESETBIT31(arg t)))              /\
    (resetbit30 t ==> (alu t = RESETBIT30(arg t)))              /\
    (buf1     t = (wbuf1   t=> alu t | buf1(PRE t)))        /\
    (buf2     t = (wbuf2   t=> alu t | buf2(PRE t)))        /\

    (mar_pins t = (wmar    t=> cdr_bits(bus_bits t)| mar_pins(PRE t))) /\
    (s        t = (ws      t=> cdr_bits(bus_bits t)| s  (PRE t))) /\
    (e        t = (we      t=> cdr_bits(bus_bits t)| e  (PRE t))) /\
    (c        t = (wc      t=> cdr_bits(bus_bits t)| c  (PRE t))) /\
    (d        t = (wd      t=> cdr_bits(bus_bits t)| d  (PRE t))) /\
    (free     t = (wfree   t=> cdr_bits(bus_bits t)| free(PRE t)))/\
    (x1       t = (wx1     t=> cdr_bits(bus_bits t)| x1 (PRE t))) /\
    (x2       t = (wx2     t=> cdr_bits(bus_bits t)| x2 (PRE t))) /\
    (car      t = (wcar    t=> car_bits(bus_bits t)| car(PRE t))) /\
    (arg      t = (warg    t=>          bus_bits t | arg (PRE t))) /\
    (parent   t = (wparent t=> cdr_bits(bus_bits t)| parent (PRE t))) /\
    (root     t = (wroot   t=> cdr_bits(bus_bits t)| root (PRE t))) /\
    (y1       t = (wy1     t=> cdr_bits(bus_bits t)| y1 (PRE t))) /\
    (y2       t = (wy2     t=> cdr_bits(bus_bits t)| y2 (PRE t))) /\

    (atomflag  t    = is_atom        (bus_bits t))             /\
    (bit30flag t    = field_bit      (bus_bits t))             /\
    (bit31flag t    = mark_bit       (bus_bits t))             /\
    (zeroflag  t    = (atom_bits     (bus_bits t) = ZERO28))   /\
    (nilflag   t    = (cdr_bits      (bus_bits t) = NIL_addr)) /\
    (eqflag    t    =                (bus_bits t = arg t))     /\
    (leqflag   t    = LEQ_prim(arg t)(bus_bits t))             /\

    (bidir t => (mem_bits t = bus_pins t) |
                (bus_pins t = bus_bits t))))",

  SUBST1_TAC (SPEC_ALL (definition `rt_SECD` `SECD`))
  THEN port[PF_lemma]				% set up to remove quantified vars %
  THEN STRIP_TAC				% constraint on asm list for lemma %
  THEN port[lemma]				% eliminate one-assertedness       %
  THEN CONV_TAC (ONCE_DEPTH_CONV		% move "alu" to outermost level    %
		  (LHS_CONV (DEPTH_CONV (CHANGED_CONV mmeoc))))
  THEN CONV_TAC (LHS_CONV (EXISTS_PERM_LIST_CONV	% rearrange quantifier order       %
  ["atomflag:^msig";    "bit30flag:^msig";    "bit31flag:^msig";
   "zeroflag:^msig";     "nilflag:^msig";      "eqflag:^msig";
   "leqflag:^msig";
   "ralu:^msig";    "rarg:^msig";    "rbuf1:^msig";   "rbuf2:^msig";
   "rcar:^msig";    "rs:^msig";      "re:^msig";      "rc:^msig";
   "rd:^msig";      "rmar:^msig";    "rx1:^msig";     "rx2:^msig";
   "rfree:^msig";   "rparent:^msig"; "rroot:^msig";   "ry1:^msig";
   "ry2:^msig";     "rnum:^msig";    "rnil:^msig";    "rtrue:^msig";
   "rfalse:^msig";  "rcons:^msig";
   "bidir:^msig";
   "warg:^msig";    "wbuf1:^msig";   "wbuf2:^msig";   "wcar:^msig";
   "ws:^msig";      "we:^msig";      "wc:^msig";      "wd:^msig";
   "wmar:^msig";    "wx1:^msig";     "wx2:^msig";     "wfree:^msig";
   "wparent:^msig"; "wroot:^msig";   "wy1:^msig";     "wy2:^msig";
   "dec:^msig";      "add:^msig";      "sub:^msig";
   "mul:^msig";      "div:^msig";      "rem:^msig";
   "setbit30:^msig"; "setbit31:^msig"; "resetbit31:^msig";
   "replcar:^msig";  "replcdr:^msig";  "resetbit30:^msig";
   "bus_bits:^w32_mvec";
   "mem_bits:^w32_mvec";
   "alu:^w32_mvec";
   "mar_bits:^w14_mvec";
   "button:^msig";
   "flag0:^msig"; "flag1:^msig";
   "write_bit:^msig"; "rmem:^msig"]))
  THEN REPEAT BINDER_EQ_TAC			       % strip off matching quantifiers %

% unwinding is made tricky because there are two equations for mar_bits:
    (!t.mar_bits t = (wmar t => cdr_bits(bus_bits t) | mar_bits(PRE t)))
               ^                                              ^^^^^
    (mar_bits = mar_pins)
  The first can diverge!  We use the second equation only for unwinding,
  using a rather elaborate predicate to pick out the desired unwind equations.
%
  THEN CONV_TAC
       (LHS_CONV
	(DEPTH_EXISTS_CONV
	 (REDEPTH_CONV(CHANGED_CONV FORALL_AND_CONV)
	  THENC (UNWIND_CONV
                 (\tm. ((is_eq tm) &
                        ((fst o dest_var o fst o dest_eq) tm = `mar_bits`))
                       or (mem (line_name tm)
	                   [`button`; `flag0`; `flag1`; `write_bit`; `rmem`]))))
	 THENC PRUNE_CONV
	 THENC (REDEPTH_CONV(CHANGED_CONV(AND_FORALL_CONV)))))
  THEN SPLIT_CONJUNCTS_TAC
  THEN BINDER_EQ_TAC
  THEN CONJUNCTS_TAC
  );;

timer false;;
close_theory ();;
print_theory `-`;;
