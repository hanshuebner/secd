%                                                                   %
% FILE: rt_CU.ml                                                    %
%                                                                   %
% DESCRIPTION: This is the register-transfer definition of the      %
%              control unit.                                        %
%                                                                   %
% USES FILES:  microcode.th                                         %
%                                                                   %
% Brian Graham 88.04.21                                             %
%                                                                   %
% 88.04.22 - CU_DECODE loading correctly                            %
% Modifications:                                                    %
% 88.06.23 - Changed the idle and error signals to 2 flag signals   %
% 88.08.08 - Added wmem_bar signal to CU.                           %
% 88.11.07 - Moved !t outside the let expressions in DECODE.        %
%            Changed Clocked parameter from "(SUC t)" to "t".       %
% 89.07.17 - redefined using new "wordn" type                       %
%          - eliminated shift registers from this view              %
%          - brought stack contents out as parameters,              %
%            state now consists of a 5-tuple                        %
%          - redefined latches to include reset, load signals       %
% 89.09.01 - Altered clock phase labelling in the documentation.    %
%          -  Changed definition of ROM_t for unwinding.            %
% 89.10.11 - eliminated the reset signal from the rtl definition.   %
% 89.11.28 - corrected the read/write fields which were swapped.    %
% 16.04.91 - BtG - updated to HOL12                                 %
% ================================================================= %
new_theory `rt_CU`;;

loadt `wordn`;;

map new_parent [`microcode`];;

% ================================================================= %
let mtime = ":num";;
let msig = ":^mtime->bool"
and w9_mvec = ":^mtime->word9"
and w27_mvec = ":^mtime->word27";;
% ================================================================= %
timer true;;
%------------------------------------------------------------%
%               CONTROL UNIT - MPC latch                     %
%------------------------------------------------------------%
let MPC9 = new_definition
  (`MPC9`,
   "! (Clocked:^msig) (in_sig:^w9_mvec) (out_sig:^w9_mvec).
    MPC9 Clocked in_sig out_sig =
    (out_sig 0 = #000000000) /\
    (!t:^mtime. out_sig (SUC t) =
                (Clocked t) =>  in_sig t  | out_sig t)"
  );;

let S_latch9 = new_definition
  (`S_latch9`,
   "! (Clocked:^msig) (load:^msig) (in_sig:^w9_mvec) (out_sig:^w9_mvec).
    S_latch9 Clocked load in_sig out_sig =
     !t:^mtime. out_sig (SUC t) = Clocked t =>
                                     load t => in_sig t | out_sig t
                                             | out_sig t"
  );;


let STATE_REG = new_definition
  (`STATE_REG`,
   "!next_mpc next_s0 next_s1 next_s2 next_s3 mpc s0 s1 s2 s3:^w9_mvec
    (Clocked:^msig) (load:^msig) .
    STATE_REG Clocked load
         (next_mpc,next_s0,next_s1,next_s2,next_s3)
         (     mpc,     s0,     s1,     s2,     s3) =
     (MPC9     Clocked       next_mpc mpc) /\
     (S_latch9 Clocked load  next_s0  s0)  /\ 
     (S_latch9 Clocked load  next_s1  s1)  /\ 
     (S_latch9 Clocked load  next_s2  s2)  /\ 
     (S_latch9 Clocked load  next_s3  s3)     "
  );;

%------------------------------------------------------------%
%                  CONTROL UNIT - ROM                        %
%------------------------------------------------------------%
% ========== this is defined in microcode ... ============== %
%%
%------------------------------------------------------------%
%               CONTROL UNIT - DECODE UNIT                   %
%------------------------------------------------------------%

let CU_DECODE = new_definition
  (`CU_DECODE`,
   "CU_DECODE
                                         % inputs %
         (button:^msig)

         (mpc:^w9_mvec)
         (s0:^w9_mvec)(s1:^w9_mvec)(s2:^w9_mvec)(s3:^w9_mvec)

         (rom_out:^w27_mvec) (opcode:^w9_mvec)

         (atomflag:^msig)    (bit30flag:^msig)   (bit31flag:^msig)  
         (zeroflag:^msig)    (nilflag:^msig)     (eqflag:^msig)
         (leqflag:^msig)
                                         % outputs %
         (flag0:^msig) (flag1:^msig) 
         (nextmpc:^w9_mvec)
         (next_s0:^w9_mvec)  (next_s1:^w9_mvec)  
         (next_s2:^w9_mvec)  (next_s3:^w9_mvec)

         (push_or_pop:^msig)
         
         (ralu:^msig)   (rmem:^msig)   (rarg:^msig)
         (rbuf1:^msig)  (rbuf2:^msig)  (rcar:^msig)
         (rs:^msig)     (re:^msig)     (rc:^msig)
         (rd:^msig)     (rmar:^msig)   (rx1:^msig)
         (rx2:^msig)    (rfree:^msig)  (rparent:^msig)
         (rroot:^msig)  (ry1:^msig)    (ry2:^msig)
         (rnum:^msig)   (rnil:^msig)   (rtrue:^msig) 
         (rfalse:^msig) (rcons:^msig)

         (write_bit:^msig)              (wmem_bar:^msig)
         (warg:^msig)   (wbuf1:^msig)
         (wbuf2:^msig)  (wcar:^msig)    (ws:^msig)
         (we:^msig)     (wc:^msig)      (wd:^msig)
         (wmar:^msig)   (wx1:^msig)     (wx2:^msig)
         (wfree:^msig)  (wparent:^msig) (wroot:^msig)
         (wy1:^msig)    (wy2:^msig)

         (dec:^msig)      (add:^msig)      (sub:^msig)
         (mul:^msig)      (div:^msig)      (rem:^msig)
         (setbit30:^msig) (setbit31:^msig) (resetbit31:^msig)
         (replcar:^msig)  (replcdr:^msig)  (resetbit30:^msig)
         =
 !t:^mtime.
  let mpc_plus_1   = Inc9 (mpc t) in
  let write_bits   = Write_field (rom_out t) in
  let read_bits    = Read_field  (rom_out t) in
  let alu_bits     = Alu_field   (rom_out t) in
  let test         = Test_field  (rom_out t) in
  let A_address    = A_field     (rom_out t) in
  let idle_state   = mpc t = #000010110   in           % 22 %
  let error_state  = mpc t = #000011000   in           % 24 %
  let toc_state    = mpc t = #000101011   in           % 43 %
  let selA         = ( (test = #0001)                 \/
                      ((test = #0011) /\ bit30flag t) \/
                      ((test = #0100) /\ bit31flag t) \/
                      ((test = #0101) /\ eqflag    t) \/
                      ((test = #0110) /\ leqflag   t) \/
                      ((test = #0111) /\ nilflag   t) \/
                      ((test = #1000) /\ atomflag  t) \/
                      ((test = #1001) /\ zeroflag  t) \/
                      ((test = #1010) /\ button    t) \/
                       (test = #1011))    in
  let pop           = (test = #1100)      in
  let push          = (test = #1011)      in
  let selOp         = (test = #0010)      in
% let selNxt        = ~(selA \/ pop \/ push \/ selOp) in %

  (   (flag0 t      = idle_state \/ error_state)                 /\
      (flag1 t      = toc_state  \/ error_state)                 /\
      (nextmpc t    = (selA)   =>   A_address |
                      ((pop)    =>   s0 t    |
                       ((selOp)  =>   opcode t    |
                     %(selNxt t) %    mpc_plus_1)))              /\
      ((next_s0 t, next_s1 t, next_s2 t, next_s3 t) =
                      push => (mpc_plus_1, s0 t, s1 t, s2 t) |
                      pop  => (s1 t, s2 t, s3 t, #000000000) |
                              (s0 t, s1 t, s2 t, s3 t))          /\
     (push_or_pop t = push \/ pop)                               /\
     (ralu       t = (read_bits = #00001))                       /\
     (rmem       t = (read_bits = #00010))                       /\
     (rarg       t = (read_bits = #00011))                       /\
     (rbuf1      t = (read_bits = #00100))                       /\
     (rbuf2      t = (read_bits = #00101))                       /\
     (rcar       t = (read_bits = #00110))                       /\
     (rs         t = (read_bits = #00111))                       /\
     (re         t = (read_bits = #01000))                       /\
     (rc         t = (read_bits = #01001))                       /\
     (rd         t = (read_bits = #01010))                       /\
     (rmar       t = (read_bits = #01011))                       /\
     (rx1        t = (read_bits = #01100))                       /\
     (rx2        t = (read_bits = #01101))                       /\
     (rfree      t = (read_bits = #01110))                       /\
     (rparent    t = (read_bits = #01111))                       /\
     (rroot      t = (read_bits = #10000))                       /\
     (ry1        t = (read_bits = #10001))                       /\
     (ry2        t = (read_bits = #10010))                       /\
     (rnum       t = (read_bits = #10011))                       /\
     (rnil       t = (read_bits = #10100))                       /\
     (rtrue      t = (read_bits = #10101))                       /\
     (rfalse     t = (read_bits = #10110))                       /\
     (rcons      t = (read_bits = #10111))                       /\

     (write_bit  t = ~(write_bits = #00001))                     /\ % nand wmem with PhiA %
     (wmem_bar   t = ~(write_bits = #00001))                     /\ % nand wmem with ~PhiB %
     (warg       t = (write_bits = #00010))                      /\
     (wbuf1      t = (write_bits = #00011))                      /\
     (wbuf2      t = (write_bits = #00100))                      /\
     (wcar       t = (write_bits = #00101))                      /\
     (ws         t = (write_bits = #00110))                      /\
     (we         t = (write_bits = #00111))                      /\
     (wc         t = (write_bits = #01000))                      /\
     (wd         t = (write_bits = #01001))                      /\
     (wmar       t = (write_bits = #01010))                      /\
     (wx1        t = (write_bits = #01011))                      /\
     (wx2        t = (write_bits = #01100))                      /\
     (wfree      t = (write_bits = #01101))                      /\
     (wparent    t = (write_bits = #01110))                      /\
     (wroot      t = (write_bits = #01111))                      /\
     (wy1        t = (write_bits = #10000))                      /\
     (wy2        t = (write_bits = #10001))                      /\

     (dec        t = (alu_bits = #0001))                         /\
     (add        t = (alu_bits = #0010))                         /\
     (sub        t = (alu_bits = #0011))                         /\
     (mul        t = (alu_bits = #0100))                         /\
     (div        t = (alu_bits = #0101))                         /\
     (rem        t = (alu_bits = #0110))                         /\
     (setbit30   t = (alu_bits = #0111))                         /\
     (setbit31   t = (alu_bits = #1000))                         /\
     (resetbit31 t = (alu_bits = #1001))                         /\
     (replcar    t = (alu_bits = #1010))                         /\
     (replcdr    t = (alu_bits = #1011))                         /\
     (resetbit30 t = (alu_bits = #1100)))
");;

%------------------------------------------------------------%
% The ROM requires time varying input and output.            %
%------------------------------------------------------------%
let ROM_t = new_definition
  (`ROM_t`,
   "ROM_t in out = !t:^mtime.  (out t) = ROM_fun (in t)"
  );;

%------------------------------------------------------------%
%                TOP LEVEL CONTROL UNIT                      %
%------------------------------------------------------------%

let CU = new_definition
  (`CU`,
   "!    (SYS_Clocked:^mtime->bool)
         (button:^msig)

         (mpc:^w9_mvec)
         (s0:^w9_mvec)(s1:^w9_mvec)(s2:^w9_mvec)(s3:^w9_mvec)

         (opcode:^w9_mvec)

         (atomflag:^msig) (bit30flag:^msig) (bit31flag:^msig)
         (zeroflag:^msig) (nilflag:^msig)   (eqflag:^msig)
         (leqflag:^msig)
                                         % outputs %
         (flag0:^msig) (flag1:^msig)

         (ralu:^msig)   (rmem:^msig)   (rarg:^msig)
         (rbuf1:^msig)  (rbuf2:^msig)  (rcar:^msig)
         (rs:^msig)     (re:^msig)     (rc:^msig)
         (rd:^msig)     (rmar:^msig)   (rx1:^msig)
         (rx2:^msig)    (rfree:^msig)  (rparent:^msig)
         (rroot:^msig)  (ry1:^msig)    (ry2:^msig)
         (rnum:^msig)   (rnil:^msig)   (rtrue:^msig) 
         (rfalse:^msig) (rcons:^msig)

         (write_bit:^msig)              (bidir:^msig)
         (warg:^msig)   (wbuf1:^msig)
         (wbuf2:^msig)  (wcar:^msig)    (ws:^msig)
         (we:^msig)     (wc:^msig)      (wd:^msig)
         (wmar:^msig)   (wx1:^msig)     (wx2:^msig)
         (wfree:^msig)  (wparent:^msig) (wroot:^msig)
         (wy1:^msig)    (wy2:^msig)

         (dec:^msig)      (add:^msig)      (sub:^msig)
         (mul:^msig)      (div:^msig)      (rem:^msig)
         (setbit30:^msig) (setbit31:^msig) (resetbit31:^msig)
         (replcar:^msig)  (replcdr:^msig)  (resetbit30:^msig)
         .
    CU   SYS_Clocked
         button
         mpc s0 s1 s2 s3
         opcode
         atomflag bit30flag bit31flag zeroflag nilflag eqflag leqflag
         flag0 flag1
         ralu rmem rarg rbuf1 rbuf2 rcar rs re rc rd rmar rx1 rx2
         rfree rparent rroot ry1 ry2 rnum rnil rtrue rfalse rcons
         write_bit bidir
         warg wbuf1 wbuf2 wcar ws we wc wd wmar wx1 wx2
         wfree wparent wroot wy1 wy2
         dec add sub mul div rem
         setbit30 setbit31 resetbit31 replcar replcdr resetbit30
         =
     ? (rom_out:^w27_mvec)
       (nextmpc:^w9_mvec)
       (next_s0:^w9_mvec)
       (next_s1:^w9_mvec)
       (next_s2:^w9_mvec)
       (next_s3:^w9_mvec)
       (push_or_pop:^msig)
     .

      (STATE_REG SYS_Clocked push_or_pop
             (nextmpc, next_s0, next_s1, next_s2, next_s3)
             (    mpc,      s0,      s1,      s2,      s3)) /\

      (ROM_t mpc rom_out) /\

      (CU_DECODE
         button
         mpc s0 s1 s2 s3
         rom_out opcode
         atomflag bit30flag bit31flag zeroflag nilflag eqflag leqflag
                                         % outputs %
         flag0 flag1
         nextmpc next_s0 next_s1 next_s2 next_s3
         push_or_pop
         ralu rmem rarg rbuf1 rbuf2 rcar rs re rc rd rmar rx1 rx2
         rfree rparent rroot ry1 ry2 rnum rnil rtrue rfalse rcons
         write_bit bidir
         warg wbuf1 wbuf2 wcar ws we wc wd wmar wx1 wx2
         wfree wparent wroot wy1 wy2
         dec add sub mul div rem
         setbit30 setbit31 resetbit31 replcar replcdr resetbit30
    )"
  );;

timer false;;
close_theory ();;
print_theory `-`;;
