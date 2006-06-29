% SECD verification                                                 %
%                                                                   %
% FILE:        rt_SECD.ml                                           %
%                                                                   %
% DESCRIPTION: This is the register transfer view of the secd       %
%              chip.  It still lacks the external memory, which     %
%              will, together with the SECD, define the SYSTEM.     %
%                                                                   %
% USES FILES:  rt_CU.th                                             %
%               rt_DP.th                                            %
%               rt_PADS.th                                          %
%                                                                   %
% Brian Graham 88.05.11                                             %
%                                                                   %
% Modifications:                                                    %
% 88.06.23 - Changed the idle and error signals to 2 flag signals   %
% 88.08.08 - Added wmem_bar signal                                  %
% 88.10.07 - x1,x2,buf1 added to DP parameters.                     %
% 16.04.91 - BtG - updated to HOL12                                 %
% ================================================================= %
new_theory `rt_SECD`;;

loadt `wordn`;;

map new_parent [ `rt_CU`
               ; `rt_DP`
               ; `rt_PADS`
               ];;

let Word32 = theorem `dp_types` `Word32`;;
% ================================================================= %
let mtime = ":num";;
let msig = ":^mtime->bool"
and w9_mvec = ":^mtime->word9"
and w14_mvec = ":^mtime->word14"
and w27_mvec = ":^mtime->word27"
and w32_mvec = ":^mtime->word32";;
% ================================================================= %
timer true;;
%------------------------------------------------------------%
% A couple of useful selector functions.                     %
%------------------------------------------------------------%
let w32 = "Word32 (Bus b32 (Bus b31
                  (Bus b30 (Bus b29 (Bus b28 (Bus b27 (Bus b26
                  (Bus b25 (Bus b24 (Bus b23 (Bus b22 (Bus b21
                  (Bus b20 (Bus b19 (Bus b18 (Bus b17 (Bus b16
                  (Bus b15 (Bus b14 (Bus b13 (Bus b12 (Bus b11
                  (Bus b10 (Bus b9  (Bus b8  (Bus b7  (Bus b6
                  (Bus b5  (Bus b4  (Bus b3  (Bus b2  (Wire (b1:bool)
                  ))))))))))))))))))))))))))))))))";;

let opcode_bits = new_recursive_definition false Word32
   `opcode_bits`
   "opcode_bits ^w32 =
      Word9 (Bus b9 (Bus b8 (Bus b7 (Bus b6 (Bus b5 (Bus b4
            (Bus b3 (Bus b2 (Wire (b1:bool))))))))))"
 ;;

let Opcode = new_definition
  (`Opcode`,
   "Opcode (b:^w32_mvec) (t:^mtime) = opcode_bits (b t)"
  );;

%------------------------------------------------------------%
%                      SECD - the chip                       %
%                      ***************                       %
% This top level view of the chip has 4 functional           %
% components:  the control unit, the datapath, the shift     %
% registers (primitive testing structure) and the pad frame. %
%------------------------------------------------------------%
let SECD = new_definition
  (`SECD`,
   "SECD
    (SYS_Clocked:^mtime->bool) 
    (mpc:^w9_mvec)
    (s0:^w9_mvec)         (s1:^w9_mvec)
    (s2:^w9_mvec)         (s3:^w9_mvec)
    (button_pin:^msig)   
    (flag0_pin:^msig)     (flag1_pin:^msig) 
    (write_bit_pin:^msig) (rmem_pin:^msig)
    (bus_pins:^w32_mvec)  (mar_pins:^w14_mvec) 
    (s:^w14_mvec)         (e:^w14_mvec)
    (c:^w14_mvec)         (d:^w14_mvec)
    (free:^w14_mvec) 
    (x1:^w14_mvec)        (x2:^w14_mvec)
    (y1:^w14_mvec)        (y2:^w14_mvec)
    (car:^w14_mvec)
    (root:^w14_mvec)      (parent:^w14_mvec)
    (buf1:^w32_mvec)      (buf2:^w32_mvec)
    (arg:^w32_mvec)
    =
    ? (button:^msig)
      (atomflag:^msig)  (bit30flag:^msig) (bit31flag:^msig)
      (zeroflag:^msig)  (nilflag:^msig)   (eqflag:^msig)
      (leqflag:^msig)
      (flag0:^msig)     (flag1:^msig)
      (ralu:^msig)      (rmem:^msig)      (rarg:^msig)
      (rbuf1:^msig)     (rbuf2:^msig)     (rcar:^msig)
      (rs:^msig)        (re:^msig)        (rc:^msig)
      (rd:^msig)        (rmar:^msig)      (rx1:^msig)
      (rx2:^msig)       (rfree:^msig)     (rparent:^msig)
      (rroot:^msig)     (ry1:^msig)       (ry2:^msig)
      (rnum:^msig)      (rnil:^msig)      (rtrue:^msig) 
      (rfalse:^msig)    (rcons:^msig)
      (write_bit:^msig) (bidir:^msig)
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
      (bus_bits:^w32_mvec) (mem_bits:^w32_mvec) (mar_bits:^w14_mvec)
      .
   (CU   SYS_Clocked
	 button
	 mpc s0 s1 s2 s3
         (Opcode arg)
         atomflag bit30flag bit31flag zeroflag nilflag eqflag leqflag
         flag0    flag1
	 ralu   rmem   rarg
         rbuf1  rbuf2  rcar
         rs     re     rc
         rd     rmar   rx1
         rx2    rfree  rparent
         rroot  ry1    ry2
         rnum   rnil   rtrue 
         rfalse rcons
         write_bit         bidir
	 warg   wbuf1
         wbuf2  wcar    ws
         we     wc      wd
         wmar   wx1     wx2
	 wfree  wparent wroot
	 wy1    wy2
         dec      add      sub
         mul      div      rem
	 setbit30 setbit31 resetbit31
	 replcar  replcdr  resetbit30)
    /\
    (DP  bus_bits mem_bits SYS_Clocked 
         rmem
	 mar_bits wmar    rmar      rnum rnil rtrue rfalse
         s        ws      rs
         e        we      re
         c        wc      rc
         d        wd      rd
	 free     wfree   rfree
         parent   wparent rparent
         root     wroot   rroot
         y1       wy1     ry1
	 x1       wx1     rx1
         x2       wx2     rx2
         y2       wy2     ry2      rcons
         car      wcar    rcar
	 atomflag bit30flag bit31flag zeroflag nilflag eqflag leqflag
	 arg      warg    rarg
         buf1     wbuf1   rbuf1
         buf2     wbuf2   rbuf2
	 replcar  replcdr sub add dec mul div rem
	 setbit30 setbit31 resetbit30 resetbit31
	 ralu )
    /\
    (rt_PF button
           flag0         flag1
	   bidir         write_bit   rmem
	   bus_bits      mem_bits    mar_bits
	   button_pin
           flag0_pin     flag1_pin
	   write_bit_pin rmem_pin
	   bus_pins      mar_pins)"
  );;

timer false;;
close_theory ();;
print_theory `-`;;
