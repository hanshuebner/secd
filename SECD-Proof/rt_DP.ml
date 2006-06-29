% SECD verification                                                 %
%                                                                   %
% FILE:        rt_DP.ml                                             %
%                                                                   %
% DESCRIPTION: This is a first attempt to define an intermediate    %
%              level view of the host machine, aimed at a           %
%              register transfer level of the data path.            %
%                                                                   %
% USES FILES:  dp_types.th                                          %
%                                                                   %
% Brian Graham 88.02.03                                             %
%                                                                   %
% Modifications:                                                    %
% 88.03.02 - added busgates between pads and bus                    %
% 88.05.11 - added Clocked predicate to registers                   %
% 88.10.07 - made x1,x2,buf1 not hidden.                            %
% 89.09.05 - removed one_asserted_12 definition.                    %
% 89.09.07 - changed recognizer fun's from ":word2->bool" to        %
%            ":word32->bool".                                       %
%          - moved recognizer and field selector functions to       %
%            dp_types to allow access from mem_abs.ml.              %
%          - redefined eq_flag as implemented.                      %
%          - defined all ALU operations on 32 bit words, in terms   %
%            of actual function, or undefined integer operations.   %
% 89.11.20 - redefined registers, using times "t" and "PRE t".      %
%            This is nearly equivalent, and simplifies the later    %
%            simplification of the datapath definition.             %
%             This also leaves the definition of the startup state  %
%             of the registers quite loose.  Contents of the reg    %
%             at (PRE t) can be thought of as being what was        %
%             there before the clock started cycling, and should    %
%             be an arbitrary or nondeterministic value.            %
% 90.02.22 - Corrected the ALU to make the arg register the         %
%            operand of the DEC operation.                          %
% 90.05.03 - renamed S_reg, etc., made reg, register, busgate       %
%            all polymorphic.                                       %
% 16.04.91 - BtG - updated to HOL12                                 %
% ================================================================= %
new_theory `rt_DP`;;

loadt `wordn`;;

map new_parent 
[ `dp_types`
; `interface`
; `modulo_ops`
; `val_defs`
];;

load_definitions `dp_types`;;

map (load_theorem `dp_types`)
 [ `Bits14_Word14`
 ; `Bits2_Word2`
 ];;

load_definition `interface` `one_asserted_12`;;
% ================================================================= %
let mtime = ":num";;
let msig = ":^mtime->bool"
and w2_mvec = ":^mtime->word2"
and w14_mvec = ":^mtime->word14"
and w28_mvec = ":^mtime->word28"
and w32_mvec = ":^mtime->word32";;
% ================================================================= %
timer true;;
%------------------------------------------------------------%
%                   primitive gates                          %
%------------------------------------------------------------%
let busgate_type =
  ":(num -> *) -> ((num -> bool) -> ((num -> *) -> bool))";;

let busgate = new_definition
  (`busgate`,
   "! in_val rd out.
    (busgate:^busgate_type) in_val rd out =
      !t. (rd t) ==> (out t = in_val t)"
  );;
let busgate2 = inst_type [":word2",":*"]busgate_type;;
let busgate14 = inst_type [":word14",":*"]busgate_type;;
let busgate32 = inst_type [":word32",":*"]busgate_type;;

%------------------------------------------------------------------------
|   register is a reg with both input and output joined to same node.
------------------------------------------------------------------------%
let reg_type=":(num -> *) ->                      % input  %
                (num -> *) ->                     % output %
                 ((num -> bool) ->                % clock  %
                  ((num -> bool) ->               % write  %
                   ((num -> bool) ->              % read   %
                    ((num -> *) -> bool))))";;    % state  %
let register_type = (hd o tl o snd o dest_type) reg_type;;

let reg = new_definition
  (`reg`,
   "!in_sig out_sig clocked wr rd st.
    (reg:^reg_type) in_sig out_sig clocked wr rd st =
      (!t:^mtime.
         st t = clocked t => (wr t => in_sig t|(st (PRE t)))
                                 | (st (PRE t))
      ) /\
      (!t:^mtime. (rd t) ==> ((out_sig t) = (st t)))"
  );;

let register = new_definition
  (`register`,
   "!sgl:num->*. register sgl = reg sgl sgl"
  );;

let reg2 = inst_type [":word2",":*"] reg_type;;
let register2 = inst_type [":word2",":*"] register_type;;
let reg14 = inst_type [":word14",":*"] reg_type;;
let register14 = inst_type [":word14",":*"] register_type;;
let reg32 = inst_type [":word32",":*"] reg_type;;
let register32 = inst_type [":word32",":*"] register_type;;

%------------------------------------------------------------%
%                       busgates                             %
%------------------------------------------------------------%
let NUM = new_definition
  (`NUM`,
   "!rnum a_sig d_sig.
    NUM rnum a_sig d_sig =
        (busgate (\t:num. ZEROS14) rnum a_sig) /\
        (busgate (\t:num. NUM_addr)  rnum d_sig)"
  );;

let Nil = new_definition
  (`Nil`,
   "Nil = busgate (\t:^mtime. NIL_addr)"
  );;

let TRUE = new_definition
  (`TRUE`,
   "TRUE = busgate (\t:^mtime. T_addr)"
  );;

let FALSE = new_definition
  (`FALSE`,
   "FALSE = busgate (\t:^mtime. F_addr)"
  );;

%------------------------------------------------------------%
%                  state registers                           %
%------------------------------------------------------------%
let S_reg = new_definition
  (`S_reg`, "S_reg:^register14 = register" );;

let E_reg = new_definition
  (`E_reg`, "E_reg:^register14 = register" );;

let C_reg = new_definition
  (`C_reg`, "C_reg:^register14 = register" );;

let D_reg = new_definition
  (`D_reg`, "D_reg:^register14 = register" );;

%------------------------------------------------------------%
%                  misc. registers                           %
%------------------------------------------------------------%
let READ_MEM = new_definition
  (`READ_MEM`, "READ_MEM:^busgate32 = busgate" );;

let MAR = new_definition
  (`MAR`,
   "!c_sig d_sig clocked wmar rmar mar.
     MAR c_sig d_sig clocked wmar rmar mar =
        ((register:^register14) d_sig clocked wmar rmar mar)   /\
        ((busgate:^busgate14) (\t:^mtime. ZEROS14) rmar c_sig)  ");;

let FREE_reg = new_definition
  (`FREE_reg`, "FREE_reg:^register14 = register" );;

let PARENT_reg = new_definition
  (`PARENT_reg`, "PARENT_reg:^register14 = register" );;

let ROOT_reg = new_definition
  (`ROOT_reg`, "ROOT_reg:^register14 = register" );;

let Y1_reg = new_definition
  (`Y1_reg`, "Y1_reg:^register14 = register" );;

let X1_reg = new_definition
  (`X1_reg`, "X1_reg:^register14 = register");;

let X2_reg = new_definition
  (`X2_reg`, "X2_reg:^register14 = register" );;

let CAR_reg = new_definition
  (`CAR_reg`, "CAR_reg:^reg14 = reg" );;

let Y2_reg = new_definition
  (`Y2_reg`, "Y2_reg:^register14 = register" );;

let ARG_reg = new_definition
  (`ARG_reg`, "ARG_reg:^register32 = register" );;

let BUF1_reg = new_definition
  (`BUF1_reg`, "BUF1_reg:^reg32 = reg " );;

let BUF2_reg = new_definition
  (`BUF2_reg`, "BUF2_reg:^reg32 = reg " );;

%------------------------------------------------------------%
%                         cons unit                          %
%------------------------------------------------------------%
let Cons = new_definition
  (`Cons`,
   "!c_in_sig d_in_sig rcons bus.
     Cons c_in_sig d_in_sig rcons bus =
      let g_out_sig = (\t:^mtime. garbage_bits  (bus t))
      and r_out_sig = (\t:^mtime. rec_type_bits (bus t))
      and c_out_sig = (\t:^mtime. car_bits      (bus t))
      and d_out_sig = (\t:^mtime. cdr_bits      (bus t))
      in
      ((busgate (\t:^mtime. #00)     rcons g_out_sig) /\
       (busgate (\t:^mtime. RT_CONS) rcons r_out_sig) /\
       (busgate c_in_sig             rcons c_out_sig) /\
       (busgate d_in_sig             rcons d_out_sig))"
  );;

%------------------------------------------------------------%
%                       flagsunit                            %
%------------------------------------------------------------%
let LEQ_prim = new_definition
(`LEQ_prim`,
 "LEQ_prim (x:word32) (y:word32) =
    let ival_x = (iVal o Bits28 o atom_bits) x
    in
    let ival_y = (iVal o Bits28 o atom_bits) y
    in
    ((ival_x below ival_y) \/ (ival_x = ival_y))"
 );;

let FLAGSUNIT = new_definition
  (`FLAGSUNIT`,
   "! (bus:^w32_mvec)  (arg:^w32_mvec)
      (atomflag:^msig) (bit30flag:^msig) (bit31flag:^msig)
      (zeroflag:^msig) (nilflag:^msig)   (eqflag:^msig)
      (leqflag:^msig).
    FLAGSUNIT bus arg
      atomflag bit30flag bit31flag zeroflag nilflag eqflag leqflag =
    !t.
      (atomflag  t = is_atom (bus t))                   /\
      (bit30flag t = field_bit (bus t))                 /\
      (bit31flag t = mark_bit (bus t))                  /\
      (zeroflag  t = (atom_bits (bus t) = ZERO28) )     /\
      (nilflag   t = (cdr_bits (bus t) = NIL_addr))     /\
      (eqflag    t = (bus t = arg t))                   /\
      (leqflag t   = LEQ_prim (arg t) (bus t))"     % arg <= bus %
  );;

%------------------------------------------------------------%
%                           alu                              %
%------------------------------------------------------------%
let REPLCAR = new_definition
(`REPLCAR`,
 "REPLCAR (x:word32) (y:word14) =
    bus32_cons_append (garbage_bits x) (rec_type_bits x)
                      y                (cdr_bits x)"
 );;

let REPLCDR = new_definition
(`REPLCDR`,
 "REPLCDR (x:word32) (y:word14) =
    bus32_cons_append (garbage_bits x) (rec_type_bits x)
                      (car_bits x)     y"
 );;

let SUB28 = new_definition
(`SUB28`,
 "SUB28 (x:word28) (y:word28) =
    let ival_x = (iVal o Bits28) x
    in
    let ival_y = (iVal o Bits28) y
    in
    bus32_num_append
      (@bit28_val:word28.
         (iVal o Bits28) bit28_val =
         (ival_x modulo_28_Sub ival_y))"
 );;

let ADD28 = new_definition
(`ADD28`,
 "ADD28 (x:word28) (y:word28) =
    let ival_x = (iVal o Bits28) x
    in
    let ival_y = (iVal o Bits28) y
    in
    bus32_num_append
      (@bit28_val:word28.
         (iVal o Bits28) bit28_val =
         (ival_x modulo_28_Add ival_y))"
 );;

let DEC28 = new_definition
(`DEC28`,
 "DEC28 (x:word28) =
    let ival_x = (iVal o Bits28) x
    in
    bus32_num_append
      (@bit28_val:word28.
         (iVal o Bits28) bit28_val =
         (modulo_28_Dec ival_x))"
 );;

let SETBIT30 = new_definition
(`SETBIT30`,
 "SETBIT30 (x:word32) =
    gc_bus32_append (mark_bit x) T x"
 );;

let SETBIT31 = new_definition
(`SETBIT31`,
 "SETBIT31 (x:word32) =
    gc_bus32_append T (field_bit x) x"
 );;

let RESETBIT30 = new_definition
(`RESETBIT30`,
 "RESETBIT30 (x:word32) =
    gc_bus32_append (mark_bit x) F x"
 );;

let RESETBIT31 = new_definition
(`RESETBIT31`,
 "RESETBIT31 (x:word32) =
    gc_bus32_append F (field_bit x) x"
 );;


%<-----------------------------------------------------------------------
let DEC28 = new_definition
  (`DEC28`,
   "!x:word28. DEC28 x =
    let num_val = VAL28 x
    in
    bus32_num_append ((num_val = 0) => #1111111111111111111111111111
                                     | WORD28 (PRE num_val))"
  );;
----------------------------------------------------------------------->%

let ALU = new_definition
  (`ALU`,
   "! (replcar:^msig)    (replcdr:^msig)
      (sub:^msig)        (add:^msig)        (dec:^msig)
      (mul:^msig)        (div:^msig)        (rem:^msig)
      (setbit30:^msig)   (setbit31:^msig)
      (resetbit30:^msig) (resetbit31:^msig)
      (ralu:^msig)
      (arg:^w32_mvec)    (y2:^w14_mvec)
      (bus:^w32_mvec)    (alu:^w32_mvec).
    ALU replcar replcdr sub add dec mul div rem
        setbit30 setbit31 resetbit30 resetbit31
        ralu arg y2 bus alu =
    (one_asserted_12 replcar replcdr sub add dec mul div rem
        setbit30 setbit31 resetbit30 resetbit31 ==>
      (!t. 
        let bus28 = (atom_bits (bus t))
        in
        let arg28 = (atom_bits (arg t))
        in
        ((replcar t     ==> (alu t = REPLCAR (arg t) (y2 t)))    /\
         (replcdr t     ==> (alu t = REPLCDR (arg t) (y2 t)))    /\
         (sub t         ==> (alu t = SUB28    arg28   bus28))    /\
         (add t         ==> (alu t = ADD28    arg28   bus28))    /\
         (dec t         ==> (alu t = DEC28    arg28))            /\
         (mul t         ==> (alu t = DEC28    arg28))            /\
         (div t         ==> (alu t = DEC28    arg28))            /\
         (rem t         ==> (alu t = DEC28    arg28))            /\
         (setbit31 t    ==> (alu t = SETBIT31 (arg t)))          /\
         (setbit30 t    ==> (alu t = SETBIT30 (arg t)))          /\
         (resetbit31 t  ==> (alu t = RESETBIT31 (arg t)))        /\
         (resetbit30 t  ==> (alu t = RESETBIT30 (arg t))))
      )
      /\
      (!t. ralu t ==> (bus t = alu t))
    )"
  );;

%------------------------------------------------------------%
%                  TOP LEVEL DATA PATH                       %
%------------------------------------------------------------%
let DP = new_definition
  (`DP`,
   "DP bus_bits mem_bits (SYS_Clocked:^msig) 
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
    ? (alu:^w32_mvec) .
      let a_bus = (\t. car_bits (bus_bits t))
      and d_bus = (\t. cdr_bits (bus_bits t))
      in
      ( (READ_MEM mem_bits rmem bus_bits)                            /\
        (MAR a_bus d_bus SYS_Clocked wmar     rmar    mar)    /\
        (NUM   rnum   a_bus d_bus)                            /\
        (Nil   rnil   d_bus)                                  /\
        (TRUE  rtrue  d_bus)                                  /\
        (FALSE rfalse d_bus)                                  /\
        (S_reg      d_bus   SYS_Clocked  ws      rs      s)      /\
        (E_reg      d_bus   SYS_Clocked  we      re      e)      /\
        (C_reg      d_bus   SYS_Clocked  wc      rc      c)      /\
        (D_reg      d_bus   SYS_Clocked  wd      rd      d)      /\
        (FREE_reg   d_bus   SYS_Clocked  wfree   rfree   free)   /\
        (PARENT_reg d_bus   SYS_Clocked  wparent rparent parent) /\
        (ROOT_reg   d_bus   SYS_Clocked  wroot   rroot   root)   /\
        (Y1_reg     d_bus   SYS_Clocked  wy1     ry1     y1)     /\
        (X1_reg     d_bus   SYS_Clocked  wx1     rx1     x1)     /\
        (X2_reg     d_bus   SYS_Clocked  wx2     rx2     x2)     /\
        (Cons x1 x2 rcons bus_bits)                              /\
        (CAR_reg a_bus d_bus SYS_Clocked  wcar    rcar    car)   /\
        (FLAGSUNIT bus_bits arg atomflag bit30flag bit31flag
                   zeroflag nilflag eqflag    leqflag   )     /\
        (Y2_reg      d_bus   SYS_Clocked  wy2     ry2     y2)     /\
        (ARG_reg     bus_bits     SYS_Clocked  warg    rarg    arg)    /\
        (ALU replcar replcdr sub add dec mul div rem
             setbit30 setbit31 resetbit30 resetbit31
             ralu arg y2 bus_bits alu                          )   /\
        (BUF1_reg    alu bus_bits SYS_Clocked  wbuf1   rbuf1   buf1)   /\
        (BUF2_reg    alu bus_bits SYS_Clocked  wbuf2   rbuf2   buf2)
     )"
  );;

timer false;;
close_theory ();;
print_theory `-`;;
