let marker_list =

%
Alu_fields:
%
[ "dec:bool"
; "add:bool"
; "sub:bool"
; "mul:bool"
; "div:bool"
; "rem:bool"
; "setbit30:bool"
; "setbit31:bool"
; "resetbit31:bool"
; "replcar:bool"
; "replcdr:bool"
; "resetbit30:bool"
%
Test_fields:
%
; "jump:bool"
; "selOp:bool"
; "testbit30:bool"
; "testbit31:bool"
; "testeq:bool"
; "testleq:bool"
; "testnil:bool"
; "testatom:bool"
; "testzero:bool"
; "testbutton:bool"
; "push:bool"
; "pop:bool"
%
Read_fields:
%
; "ralu:bool"
; "rmem:bool"
; "rarg:bool"
; "rbuf1:bool"
; "rbuf2:bool"
; "rcar:bool"
; "rs:bool"
; "re:bool"
; "rc:bool"
; "rd:bool"
; "rmar:bool"
; "rx1:bool"
; "rx2:bool"
; "rfree:bool"
; "rparent:bool"
; "rroot:bool"
; "ry1:bool"
; "ry2:bool"
; "rnum:bool"
; "rnil:bool"
; "rtrue:bool"
; "rfalse:bool"
; "rcons:bool"
%
Write_fields:
%
; "wmem:bool"
; "warg:bool"
; "wbuf1:bool"
; "wbuf2:bool"
; "wcar:bool"
; "ws:bool"
; "we:bool"
; "wc:bool"
; "wd:bool"
; "wmar:bool"
; "wx1:bool"
; "wx2:bool"
; "wfree:bool"
; "wparent:bool"
; "wroot:bool"
; "wy1:bool"
; "wy2:bool"
%
Misc:
%
; "f0:bool"
; "f1:bool"
; "Inc9mpc:word9"
; "Afield:word9"
];;


let template = 
 " ?bus_bits_t mem_bits_t alu_t:word32.
        (mpc(SUC t) =
          ((jump \/
            testbit30 /\ field_bit(bus_bits_t) \/
            testbit31 /\ mark_bit(bus_bits_t) \/
            testeq /\ (bus_bits_t = arg t) \/
            testleq /\ LEQ_prim(arg t)(bus_bits_t) \/
            testnil /\ (cdr_bits(bus_bits_t) = NIL_addr) \/
            testatom /\ is_atom(bus_bits_t) \/
            testzero /\ (atom_bits(bus_bits_t) = ZERO28) \/
            testbutton /\ button_pin t \/
            push) => 
           Afield | 
           (pop => 
            s0 t | 
            (selOp => Opcode arg t | Inc9mpc)))) /\
             
        (s0(SUC t) =
           (push => 
            Inc9mpc | 
            (pop => s1 t | s0 t))) /\
        (s1(SUC t) =
           (push => 
            s0 t | 
            (pop => s2 t | s1 t))) /\
        (s2(SUC t) =
           (push => 
            s1 t | 
            (pop => s3 t | s2 t))) /\
        (s3(SUC t) =
           (push => 
            s2 t | 
            (pop => #000000000 | s3 t))) /\
	  
        (memory(SUC t) =
         (wmem => Store14 ( mar_pins t)(bus_pins t)(memory t)
                | (memory t))) /\

        (rmem   ==> (bus_bits_t = mem_bits_t)) /\
        (rmar   ==> (cdr_bits(bus_bits_t) = mar_pins t)) /\
        (rmar   ==> (car_bits(bus_bits_t) = ZEROS14)) /\
        (rnum   ==> (cdr_bits(bus_bits_t) = NUM_addr)) /\
        (rnum   ==> (car_bits(bus_bits_t) = ZEROS14)) /\
        (rnil   ==> (cdr_bits(bus_bits_t) = NIL_addr)) /\
        (rtrue  ==> (cdr_bits(bus_bits_t) = T_addr)) /\
        (rfalse ==> (cdr_bits(bus_bits_t) = F_addr)) /\
        (rs     ==> (cdr_bits(bus_bits_t) = s  t)) /\
        (re     ==> (cdr_bits(bus_bits_t) = e  t)) /\
        (rc     ==> (cdr_bits(bus_bits_t) = c  t)) /\
        (rd     ==> (cdr_bits(bus_bits_t) = d  t)) /\
        (rfree  ==> (cdr_bits(bus_bits_t) = free t)) /\
        (rx1    ==> (cdr_bits(bus_bits_t) = x1 t)) /\
        (rx2    ==> (cdr_bits(bus_bits_t) = x2 t)) /\
        (rparent==> (cdr_bits(bus_bits_t) = parent t)) /\
        (rroot  ==> (cdr_bits(bus_bits_t) = root t)) /\
        (ry1    ==> (cdr_bits(bus_bits_t) = y1 t)) /\
        (ry2    ==> (cdr_bits(bus_bits_t) = y2 t)) /\
        (rcons  ==> (garbage_bits(bus_bits_t) = #00)) /\
        (rcons  ==> (rec_type_bits(bus_bits_t) = RT_CONS)) /\
        (rcons  ==> (car_bits(bus_bits_t) = x1 t)) /\
        (rcons  ==> (cdr_bits(bus_bits_t) = x2 t)) /\
        (rcar   ==> (cdr_bits(bus_bits_t) = car t)) /\
        (rarg   ==> (bus_bits_t = arg t)) /\
        (rbuf1  ==> (bus_bits_t = buf1 t)) /\
        (rbuf2  ==> (bus_bits_t = buf2 t)) /\
        (ralu   ==> (bus_bits_t = alu_t)) /\
        (rmem_pin t = rmem) /\

        (sub ==>
         (alu_t = SUB28(atom_bits(arg t))(atom_bits(bus_bits_t)))) /\
        (add ==>
         (alu_t = ADD28(atom_bits(arg t))(atom_bits(bus_bits_t)))) /\
        (dec ==> (alu_t = DEC28(atom_bits(arg t)))) /\
        (mul ==> (alu_t = DEC28(atom_bits(arg t)))) /\
        (div ==> (alu_t = DEC28(atom_bits(arg t)))) /\
        (rem ==> (alu_t = DEC28(atom_bits(arg t)))) /\
        (replcar ==> (alu_t = REPLCAR(arg t)(y2 t))) /\
        (replcdr ==> (alu_t = REPLCDR(arg t)(y2 t))) /\
        (setbit31 ==> (alu_t = SETBIT31(arg t))) /\
        (setbit30 ==> (alu_t = SETBIT30(arg t))) /\
        (resetbit31 ==> (alu_t = RESETBIT31(arg t))) /\
        (resetbit30 ==> (alu_t = RESETBIT30(arg t))) /\

        ((~wmem) => 
         (mem_bits_t = bus_pins t) | 
         (bus_pins t = bus_bits_t)) /\
        ((~wmem) /\ (rmem) ==>
         (bus_pins t = memory t(mar_pins t))) /\

        (buf1 t = (wbuf1 => alu_t | buf1(PRE t))) /\
        (buf2 t = (wbuf2 => alu_t | buf2(PRE t))) /\
        (mar_pins t =
         (wmar => cdr_bits(bus_bits_t) | mar_pins(PRE t))) /\
        (s  t = (ws => cdr_bits(bus_bits_t) | s (PRE t))) /\
        (e  t = (we => cdr_bits(bus_bits_t) | e (PRE t))) /\
        (c  t = (wc => cdr_bits(bus_bits_t) | c (PRE t))) /\
        (d  t = (wd => cdr_bits(bus_bits_t) | d (PRE t))) /\
        (free t = (wfree => cdr_bits(bus_bits_t) | free(PRE t))) /\
        (x1 t = (wx1 => cdr_bits(bus_bits_t) | x1(PRE t))) /\
        (x2 t = (wx2 => cdr_bits(bus_bits_t) | x2(PRE t))) /\
        (car t = (wcar => car_bits(bus_bits_t) | car(PRE t))) /\
        (arg t = (warg => bus_bits_t | arg(PRE t))) /\
        (parent t = (wparent => cdr_bits(bus_bits_t) | parent(PRE t))) /\
        (root t = (wroot => cdr_bits(bus_bits_t) | root(PRE t))) /\
        (y1 t = (wy1 => cdr_bits(bus_bits_t) | y1(PRE t))) /\
        (y2 t = (wy2 => cdr_bits(bus_bits_t) | y2(PRE t))) /\
        (write_bit_pin t = ~wmem) /\

        (flag0_pin t = (f0:bool)) /\
        (flag1_pin t = (f1:bool))"
;;
