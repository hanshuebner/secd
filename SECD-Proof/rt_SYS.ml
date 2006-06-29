% SECD verification                                                %
%                                                                  %
% FILE:                rt_SYS.ml                                   %
%                                                                  %
% DESCRIPTION:  This describes the top level view of the SECD      %
%               system implementation, which is the SECD chip      %
%               wired to memory.                                   %
%                                                                  %
% USES FILES:   rt_SECD.th                                         %
%                                                                  %
% Brian Graham 88.08.11                                            %
%                                                                  %
% Modifications:                                                   %
% 88.??.?? - defined my own simple memory to overcome problems     %
%            with initialization.                                  %
% 88.10.07 - x1,x2,buf1 added to SECD parameters.                  %
% 16.04.91 - BtG - updated to HOL12                                 %
% ================================================================ %
new_theory `rt_SYS`;;

loadt `wordn`;;

new_parent `rt_SECD`;;

% ================================================================= %
let mtime = ":num";;
let mem14_32 = ":word14->word32";;
let msig        = ":^mtime->bool"
and w9_mvec     = ":^mtime->word9"
and w32_mvec    = ":^mtime->word32"
and w14_mvec    = ":^mtime->word14"
and m14_32_mvec = ":^mtime->^mem14_32";;
% ================================================================= %
timer true;;
% ================================================================= %
let Fetch14 = new_definition
  (`Fetch14`,
   "Fetch14 (mar:word14) (bus:word32) (mem:^mem14_32) = (bus = mem mar)"
  );;

let Store14 = new_definition
  (`Store14`,
   "Store14 (mar:word14) (bus:word32) (mem:^mem14_32) =
     (\a. (a = mar) => bus | mem a)"
  );;

%-----------------------------------------------------------------%
% This is a simple model of a Static RAM memory.  The control     %
% lines are as named on the AMD Am99C88/Am99CL88 family of        %
% 8K x 8 CMOS Static Random Access Memories.                      %
% Configuration is as follows:                                    %
%                W_bar         G_bar         function             %
%                 H             H            output disabled      %
%                 H             L            read                 %
%                 L             X            write                %
%                                                                 %
% Memory is a vector, like any other signal, that changes         %
% over time.  There is an output only if both controls are        %
% asserted correctly.                                             %
%                                                                 %
% Notice that the temporal abstraction differs from that of the   %
% datapath registers.  This seems unusual since in most ways, the %
% memory is no more than an addressable register.  The difference %
% lies in the fact that the value written to memory is not        %
% available as the state of the "register" during the cycle in    %
% which it is written.  Thus, the contents need only be the state %
% in the next cycle, rather than the present one as in the        %
% datapath.                                                       %
%                                                                 %
% We altered the above definition slighly.  The G_bar signal is   %
% inverted logic level to the signal that will be provided by the %
% SECD chip, so an inverter is necessary.  We incorporate this by %
% inverting the logic level of the signal within the definition.  %
%-----------------------------------------------------------------%
let SRAM = new_definition
  (`SRAM`,
   "SRAM mem W_bar G_bar address_in in_out =
    (!t.
        (mem(SUC t) =
           ((~W_bar t) => Store14(address_in t)(in_out t)(mem t)
                        | mem t)
        ) /\
        (W_bar t /\ G_bar t ==>
                          Fetch14 (address_in t)(in_out t)(mem t)))"
  );;

%-----------------------------------------------------------------%
% The system consists of the chip connected to a memory.          %
%-----------------------------------------------------------------%
let SYS = new_definition
  (`SYS`,
   "SYS memory
       SYS_Clocked 
       mpc s0  s1  s2  s3
       button_pin
       flag0_pin       flag1_pin
       write_bit_pin   rmem_pin
       bus_pins        mar_pins
       s   e   c   d   free
       x1  x2  y1  y2  car  root  parent
       buf1    buf2    arg  =
   (SECD     SYS_Clocked 
       mpc s0  s1  s2  s3
       button_pin
       flag0_pin       flag1_pin
       write_bit_pin   rmem_pin
       bus_pins        mar_pins
       s   e   c   d   free
       x1  x2  y1  y2  car  root  parent
       buf1    buf2    arg) /\
   (SRAM memory write_bit_pin rmem_pin mar_pins bus_pins)"
  );;

timer false;;
close_theory ();;
print_theory `-`;;
