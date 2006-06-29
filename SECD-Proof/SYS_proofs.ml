% SECD verification                                               %
%                                                                 %
% FILE:        SYS_proofs.ml                                      %
%                                                                 %
% DESCRIPTION: Unwinds the system implementation.                 %
%                                                                 %
% USES FILES:   rt_SYS.th                                         %
%               SECD_proofs.th                                    %
%               SPLIT_CONJUNCTS.ml                                %
%               BINDER_EQ_TAC.ml                                  %
%               EXISTS_PERM_LIST.ml                               %
%               MOVE_EXISTS_OUT_CONV.ml                           %
%               CONJUNCTS_TAC.ml                                  %
%                                                                 %
% Brian Graham 09.11.89                                           %
%                                                                 %
% Modifications:                                                  %
% 29.11.89 - installed the code for BASE_thm                      %
%          - upon testing the proof function in prove_SYS_lemmas  %
%            I tried the Swap_Quantifiers version of the theorem, %
%            to permit simpler unwinding and pruning of the       %
%            reduced theorem.                                     %
% 03.01.90 - The previously installed code to produce exhaustive  %
%            case theorems for subcomponents, and then CONJ them  %
%            all together, seemed much slower than substitution   %
%            and simplification by rewriting, so has been         %
%            commented out.                                       %
% 21.11.91 - BtG - updated to HOL2                                %
% =============================================================== %
new_theory `SYS_proofs`;;

loadf `wordn`;; 

map new_parent  [ `SECD_proofs`
                ; `rt_SYS`
                ];;

map loadt [ `SPLIT_CONJUNCTS`
          ; `BINDER_EQ_TAC`
          ; `EXISTS_PERM_LIST`
          ; `MOVE_EXISTS_OUT_CONV`
          ; `CONJUNCTS_TAC`
          ];;

load_library `unwind`;;
load_all `rt_SYS`;;


load_theorem `CU_proofs` `CU_unwound_lemma`;;
load_definition `constraints` `clock_constraint`;;
% ================================================================= %
let mtime = ":num";;

let msig = ":^mtime->bool"
and w9_mvec = ":^mtime->word9"
and w14_mvec = ":^mtime->word14"
and w27_mvec = ":^mtime->word27"
and w32_mvec = ":^mtime->word32";;

let mem14_32 = ":word14->word32";;
let m14_32_mvec = ":^mtime->^mem14_32";;
%%
timer true;;
% ================================================================= %
% A specialized tactic, used to change the "normal" form of         %
% conjunction to that of the implementation-derived form.  This is  %
% done by extracting the last item in the normal order              %
% conjunction series (here in fact it is the last conjunction),     %
% and putting it at the front of the conjunction.                   %
% ================================================================= %
letrec my_conjuncts w =
 (let a,b = dest_conj w
  in
  let bl = my_conjuncts b
  in
  ((length bl = 1) & not(is_conj (hd bl))) => [mk_conj (a, hd bl)]
                     | a . bl) ? [w];;

let my_FRONT_CONJ_CONV tm =
 let al = my_conjuncts tm
 in
 FRONT_CONJ_CONV al (el (length al) al);;

% ================================================================ %
% convert a num to a boolean list (1's and 0's).                   %
%                                                                  %
% functions:                                                       %
%   mk_bit_list (num,size) res                                     %
%       returns a list of strings of 1's and 0's,                  %
%       of length size.                                            %
%   example : #mk_bit_list (3,4)[];;                               %
%             [`0`; `0`; `1`; `1`] : string list                   %
% ================================================================ %
let rem (x,y) = x - y * (x / y);;

letrec mk_bit_list (num, size) res =
   (size = 0) => res |
                 (mk_bit_list ((num/2), (size-1)) 
                   (((string_of_int o rem) (num,2)) . res));;

% ================================================================ %
% This is a simplification of the defintion of SRAM.  Note that    %
% this may be taken too far.  It could be advantageous to leave    %
% the definition in terms of Fetch14 and Store14 commands,         %
% provided the abstraction of memory is indepentently proven for   %
% these terms.  This seems a most suitable candidate for proving   %
% a lower level definition correct, and using the proof in a       %
% higher level representation proof.                               %
%                                                                  %
% 90.02.23 - revised as suggested above.                           %
% |- !mem W_bar G_bar address_in in_out.                           %
%     SRAM mem W_bar G_bar address_in in_out =                     %
%     (!t.                                                         %
%       (mem(SUC t) =                                              %
%        ((~W_bar t) => Store14(address_in t)(in_out t)(mem t)     %
%                     | mem t)) /\                                 %
%       (W_bar t /\ G_bar t ==>                                    %
%           (in_out t = mem t(address_in t))))                     %
% ================================================================ %
let SRAM_lemma = save_thm (`SRAM_lemma`, porr[Fetch14]SRAM);;

%%
% ================================================================ %
% The main lemma.  Note that:                                      %
% - all quantified variables are at the outermost level            %
% - the CU is in the required form for prove_CU_lemmas             %
% - "t" is quantified over all except the CU                       %
% - all internal expressions are "reasonably" simplified.          %
% Optimizations that are possible include the extraction of        %
% common expressions like:                                         %
% 	bus_bits t                                                 %
% 	cdr_bits(bus_bits t)                                       %
% 	car_bits(bus_bits t)                                       %
% 	garbage_bits(bus_bits t)                                   %
% 	rec_type_bits(bus_bits t)                                  %
% 	atom_bits(arg t)                                           %
% 	atom_bits(bus_bits t)                                      %
% 	bus_bits(t+1)                                              %
% 	cdr_bits(bus_bits(t+1))                                    %
%         car_bits(bus_bits(t+1))                                  %
% by lambda abstraction, so that these can be substituded once     %
% only, rather than in every instance.                             %
%                                                                  %
% Total time : 359.5s 94.3s 3015                                   %
% ================================================================ %
let SYS_lemma = prove
("(clock_constraint SYS_Clocked) ==>
   (SYS memory
       SYS_Clocked 
       mpc s0  s1  s2  s3
       button_pin
       flag0_pin       flag1_pin
       write_bit_pin   rmem_pin
       bus_pins        mar_pins
       s   e   c   d   free
       x1  x2  y1  y2  car  root  parent
       buf1    buf2    arg  =
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
   !t.
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
    (s        t = (ws      t=> cdr_bits(bus_bits t)| s     (PRE t))) /\
    (e        t = (we      t=> cdr_bits(bus_bits t)| e     (PRE t))) /\
    (c        t = (wc      t=> cdr_bits(bus_bits t)| c     (PRE t))) /\
    (d        t = (wd      t=> cdr_bits(bus_bits t)| d     (PRE t))) /\
    (free     t = (wfree   t=> cdr_bits(bus_bits t)| free  (PRE t))) /\
    (x1       t = (wx1     t=> cdr_bits(bus_bits t)| x1    (PRE t))) /\
    (x2       t = (wx2     t=> cdr_bits(bus_bits t)| x2    (PRE t))) /\
    (car      t = (wcar    t=> car_bits(bus_bits t)| car   (PRE t))) /\
    (arg      t = (warg    t=>          bus_bits t | arg   (PRE t))) /\
    (parent   t = (wparent t=> cdr_bits(bus_bits t)| parent(PRE t))) /\
    (root     t = (wroot   t=> cdr_bits(bus_bits t)| root  (PRE t))) /\
    (y1       t = (wy1     t=> cdr_bits(bus_bits t)| y1    (PRE t))) /\
    (y2       t = (wy2     t=> cdr_bits(bus_bits t)| y2    (PRE t))) /\

    (atomflag  t    = is_atom        (bus_bits t))             /\
    (bit30flag t    = field_bit      (bus_bits t))             /\
    (bit31flag t    = mark_bit       (bus_bits t))             /\
    (zeroflag  t    = (atom_bits     (bus_bits t) = ZERO28))   /\
    (nilflag   t    = (cdr_bits      (bus_bits t) = NIL_addr)) /\
    (eqflag    t    =                (bus_bits t = arg t))     /\
    (leqflag   t    = LEQ_prim(arg t)(bus_bits t))             /\

    (bidir t => (mem_bits t = bus_pins t) |
                (bus_pins t = bus_bits t))                     /\
    (memory(SUC t) =
       ((~write_bit_pin t)
            => Store14(mar_pins t)(bus_pins t)(memory t)
             | memory t))                                      /\
    (write_bit_pin t /\ rmem_pin t ==>
       (bus_pins t = (memory t) (mar_pins t))))",
 DISCH_THEN
  (\th. SUBST1_TAC (SPEC_ALL SYS)
        THEN SUBST1_TAC
	(MP (theorem `SECD_proofs` `SECD_lemma`) th)) 
				% 29.7 19.4 37 %
 THEN REPEAT (CONV_TAC (LHS_CONV mmeoc) THEN BINDER_EQ_TAC)
				% 290.1 28.2 2013 %
 THEN CONV_TAC (LHS_CONV (REWR_CONV (SYM_RULE CONJ_ASSOC)))
				% 4.7 8.4 27 %
 THEN SPLIT_CONJUNCTS_TAC
				% 4.9 8.4 5 %
 THEN SUBST1_TAC
      (SPECL ["memory:^m14_32_mvec";"write_bit_pin:^msig"
             ;"rmem_pin:^msig";"mar_pins:^w14_mvec";"bus_pins:^w32_mvec"]
             SRAM_lemma)
				% 5.8 9.0 3 %
 THEN CONV_TAC (LHS_CONV (ONCE_DEPTH_CONV AND_FORALL_CONV))
				% 4.0 9.1 8 %
 THEN BINDER_EQ_TAC THEN SYM_TAC
				% 4.5 9.2 9 %
	
 THEN CONV_TAC (LHS_CONV my_FRONT_CONJ_CONV)
				% 26.4 27.9 909 %
 THEN CONV_TAC (LHS_CONV (REWR_CONV CONJ_SYM))
				% 3.8 9.5 10 %
 THEN REFL_TAC
				% 119.2 93.0 267 %
 );; 


% =============================================================== %
% The above lemma does not give a sufficiently powerful base for  %
% proofs for each step of the machine clock scale.  It appears    %
% to be a good idea to split up the proof just as was done in     %
% the control unit `CU_proofs` file, and build a proof function   %
% that derives the present and next states of the machine based   %
% on the current mpc value.                                       %
%                                                                 %
% The trouble I had was essentially with the existential          %
% quantifiers.  For backward proof, they are easily eliminated.   %
% However, forward proof is more problematic, and the presence    %
% of the universally quantified "t" over all but the CU, causes   %
% additional difficulty when trying to instantiate particular     %
% values for CU outputs only, and have them used in the rest.     %
%                                                                 %
% 1. Begin by unfolding the SYS definition entirely.              %
% 2. Use this as a basis for several subcomponent implicative     %
%    theorems.                                                    %
% 3. Prove exhaustive cases for the subcomponents.                %
% 4. Build a proof function to combine the subcomponents, and     %
%    unwind the remaining quantified variables (bus_bits,         %
%    mem_bits(?), and alu.                                        %
% =============================================================== %


% ================================================================= %
% A conversion to abstract out a term.                              %
% ================================================================= %
let BETA_INV_CONV (t1,t2) trm =
 (SYM o RIGHT_BETA)
 (REFL(mk_comb (mk_abs(t1,subst [t1,t2] trm), t2)));;

% ================================================================= %
% Two conversions, for getting at precisely the place where the     %
% above conversion needs to operate.                                %
% ================================================================= %
let FORALL_CONV conv tm =
 (let bv,body = dest_forall tm in
  let bodyth = conv body in
  (FORALL_EQ bv bodyth)) ? failwith `FORALL_CONV`;;

let EXISTS_CONV conv tm =
 (let bv,body = dest_exists tm in
  let bodyth = conv body in
  (EXISTS_EQ bv bodyth)) ? failwith `EXISTS_CONV`;;

let R_CONJ_CONV conv tm =
 (let lhs,rhs = dest_conj tm in
  let rhsth = conv rhs in
  (AP_TERM "$/\ ^lhs" rhsth)) ? failwith `R_CONJ_CONV`;;


% ================================================================= %
% An interesting theorem, permitting the swapping of the order of   %
% universal and existential quantifiers, IN PARTICULAR CASES.       %
% The implicative proof (lhs ==> rhs) is generally true, but the    %
% reverse will hold when the existentially quantified variable is   %
% a function of the universally quantified one.                     %
% This theorem can be specialized to the case we are interested in, %
% that of the "alu" and "t" values.                                 %
% ================================================================= %
% An improved form (yet again ... 89.11.29).  This time, we         %
% substitute of the a single quantifier for the quantified value    %
% being applied to "t".  The importance of this is that once the    %
% implementation expression is simplified, we are left with "!t."   %
% outside the existentially quantified variables, which cannot      %
% be unwound, since the "t" paremeter requires the use of UNWINDF,  %
% and it needs "!t" just outside the conjunctions.                  %
% With this change, we have a simple variable to unwind and prune,  %
% which can be accomplished with UNWIND THENC PRUNE alone.  This    %
% will let the expression simplify sufficiently, I hope.            %
% ================================================================= %
let Swap_Quantifiers = prove
("(!t:num.    ?at':*. P t at') =
   (?a:num->*. !t:num.    P t(a t))",
 EQ_TAC
 THENL
 [ DISCH_THEN
 \th. EXISTS_TAC "\t':num.@at':*. P t' at'"
      THEN GEN_TAC
      THEN in1_conv_tac BETA_CONV
      THEN in1_conv_tac SELECT_CONV
      THEN MATCH_ACCEPT_TAC th
 ;
 DISCH_THEN
 (CHOOSE_THEN
  \th. GEN_TAC
       THEN EXISTS_TAC "(a:num->*) t"
       THEN MATCH_ACCEPT_TAC th)
 ]
 );;

% ================================================================= %
% Trying to develop the desired base lemma for the automation of    %
% the implementation state proof.                                   %
% ================================================================= %

% ================================================================= %
% A very specialized conversion for moving the "!t." outside the    %
% existentially quantified variables.  Given a term;                %
% 	"!t. ?q. P[t,q]"                                            %
% it does the following:                                            %
% - use BETA INV to abstract out q from the body                    %
% 	"!t. ?q. (\q'.P[t,q'])q"                                    %
% - use BETA INV to abstract out "t" from the body                  %
% 	"!t. ?q. (\t' q'.P[t',q'])t q"                              %
% - rewrite with Swap_Quantifiers to reverse order of t and q.      %
% 	"?q''. !t. (\t' q'.P[t',q'])t (q'' t)"                      %
% - use LIST_BETA_CONV to eliminate abstractions                    %
% 	"?q''. !t. P[t,q'' t]"                                      %
% ================================================================= %
let conversn (t1,t2,t3) =
  (FORALL_CONV
   (EXISTS_CONV
    (BETA_INV_CONV (t1,t2)
     THENC
     RATOR_CONV (BETA_INV_CONV ("t':^mtime", "t:^mtime")))))
  THENC
  (REWR_CONV
   (CONV_RULE
    (RHS_CONV (GEN_ALPHA_CONV t3))
   Swap_Quantifiers))
  THENC
  (EXISTS_CONV
   (FORALL_CONV LIST_BETA_CONV));;

% ================================================================= %
% The next problem is splitting the expression up so components     %
% can be done individually ... ie. read, write, alu, and test       %
% signals, and then composing the lot together with the mpc         %
% instantiated to a specific value.                                 %
% ================================================================= %
let SYS_Unwound_lemma = prove_thm
(`SYS_Unwound_lemma`,
 "(clock_constraint SYS_Clocked) ==>
(SYS 
 memory 
 SYS_Clocked 
 mpc 
 s0 
 s1 
 s2 
 s3 
 button_pin 
 flag0_pin 
 flag1_pin 
 write_bit_pin 
 rmem_pin 
 bus_pins 
 mar_pins 
 s  
 e  
 c  
 d  
 free 
 x1 
 x2 
 y1 
 y2 
 car 
 root 
 parent 
 buf1 
 buf2 
 arg =
 (mpc 0 = #000000000) /\
 !t.
 (?bus_bits_t mem_bits_t alu_t.
   (mpc(SUC t) =
      (((Test_field(ROM_fun(mpc t)) = #0001) \/
        (Test_field(ROM_fun(mpc t)) = #0011)
                        /\ field_bit(bus_bits_t) \/
        (Test_field(ROM_fun(mpc t)) = #0100)
                         /\ mark_bit(bus_bits_t) \/
        (Test_field(ROM_fun(mpc t)) = #0101)
                        /\ (bus_bits_t = arg t) \/
        (Test_field(ROM_fun(mpc t)) = #0110) 
                /\ LEQ_prim (arg t)(bus_bits_t) \/
        (Test_field(ROM_fun(mpc t)) = #0111) 
           /\ (cdr_bits(bus_bits_t) = NIL_addr) \/
        (Test_field(ROM_fun(mpc t)) = #1000)
                         /\ is_atom(bus_bits_t) \/
        (Test_field(ROM_fun(mpc t)) = #1001)
             /\ (atom_bits(bus_bits_t) = ZERO28) \/
        (Test_field(ROM_fun(mpc t)) = #1010)
                                 /\ button_pin t \/
        (Test_field(ROM_fun(mpc t)) = #1011)) => 
       A_field(ROM_fun(mpc t)) | 
       ((Test_field(ROM_fun(mpc t)) = #1100) => 
        s0 t | 
        ((Test_field(ROM_fun(mpc t)) = #0010) => 
         Opcode arg t | 
         Inc9(mpc t))))) /\
   (s0(SUC t) =
      ((Test_field(ROM_fun(mpc t)) = #1011) => 
       Inc9(mpc t) | 
       ((Test_field(ROM_fun(mpc t)) = #1100) => s1 t | s0 t))) /\
   (s1(SUC t) =
      ((Test_field(ROM_fun(mpc t)) = #1011) => 
       s0 t | 
       ((Test_field(ROM_fun(mpc t)) = #1100) => s2 t | s1 t))) /\
   (s2(SUC t) =
      ((Test_field(ROM_fun(mpc t)) = #1011) => 
       s1 t | 
       ((Test_field(ROM_fun(mpc t)) = #1100) => s3 t | s2 t))) /\
   (s3(SUC t) =
      ((Test_field(ROM_fun(mpc t)) = #1011) => 
       s2 t | 
       ((Test_field(ROM_fun(mpc t)) = #1100) => #000000000 | s3 t))) /\

   (memory(SUC t) =
     ((Write_field(ROM_fun(mpc t)) = #00001)
       => Store14(mar_pins t)(bus_pins t)(memory t)
        | memory t)) /\

   ((Read_field(ROM_fun(mpc t)) = #00010) ==>
     (bus_bits_t = mem_bits_t)) /\
   ((Read_field(ROM_fun(mpc t)) = #01011) ==>
     (cdr_bits(bus_bits_t) = mar_pins t)) /\
   ((Read_field(ROM_fun(mpc t)) = #01011) ==>
     (car_bits(bus_bits_t) = ZEROS14)) /\
   ((Read_field(ROM_fun(mpc t)) = #10011) ==>
     (cdr_bits(bus_bits_t) = NUM_addr)) /\
   ((Read_field(ROM_fun(mpc t)) = #10011) ==>
     (car_bits(bus_bits_t) = ZEROS14)) /\
   ((Read_field(ROM_fun(mpc t)) = #10100) ==>
     (cdr_bits(bus_bits_t) = NIL_addr)) /\
   ((Read_field(ROM_fun(mpc t)) = #10101) ==>
     (cdr_bits(bus_bits_t) = T_addr)) /\
   ((Read_field(ROM_fun(mpc t)) = #10110) ==>
     (cdr_bits(bus_bits_t) = F_addr)) /\
   ((Read_field(ROM_fun(mpc t)) = #00111) ==>
     (cdr_bits(bus_bits_t) = s  t)) /\
   ((Read_field(ROM_fun(mpc t)) = #01000) ==>
     (cdr_bits(bus_bits_t) = e  t)) /\
   ((Read_field(ROM_fun(mpc t)) = #01001) ==>
     (cdr_bits(bus_bits_t) = c  t)) /\
   ((Read_field(ROM_fun(mpc t)) = #01010) ==>
     (cdr_bits(bus_bits_t) = d  t)) /\
   ((Read_field(ROM_fun(mpc t)) = #01110) ==>
     (cdr_bits(bus_bits_t) = free t)) /\
   ((Read_field(ROM_fun(mpc t)) = #01100) ==>
     (cdr_bits(bus_bits_t) = x1 t)) /\
   ((Read_field(ROM_fun(mpc t)) = #01101) ==>
     (cdr_bits(bus_bits_t) = x2 t)) /\
   ((Read_field(ROM_fun(mpc t)) = #01111) ==>
     (cdr_bits(bus_bits_t) = parent t)) /\
   ((Read_field(ROM_fun(mpc t)) = #10000) ==>
     (cdr_bits(bus_bits_t) = root t)) /\
   ((Read_field(ROM_fun(mpc t)) = #10001) ==>
     (cdr_bits(bus_bits_t) = y1 t)) /\
   ((Read_field(ROM_fun(mpc t)) = #10010) ==>
     (cdr_bits(bus_bits_t) = y2 t)) /\
   ((Read_field(ROM_fun(mpc t)) = #10111) ==>
     (garbage_bits(bus_bits_t) = #00)) /\
   ((Read_field(ROM_fun(mpc t)) = #10111) ==>
     (rec_type_bits(bus_bits_t) = RT_CONS)) /\
   ((Read_field(ROM_fun(mpc t)) = #10111) ==>
     (car_bits(bus_bits_t) = x1 t)) /\
   ((Read_field(ROM_fun(mpc t)) = #10111) ==>
     (cdr_bits(bus_bits_t) = x2 t)) /\
   ((Read_field(ROM_fun(mpc t)) = #00110) ==>
     (cdr_bits(bus_bits_t) = car t)) /\
   ((Read_field(ROM_fun(mpc t)) = #00011) ==>
     (bus_bits_t = arg t)) /\
   ((Read_field(ROM_fun(mpc t)) = #00100) ==>
     (bus_bits_t = buf1 t)) /\
   ((Read_field(ROM_fun(mpc t)) = #00101) ==>
     (bus_bits_t = buf2 t)) /\
   ((Read_field(ROM_fun(mpc t)) = #00001) ==>
     (bus_bits_t = alu_t)) /\
   (rmem_pin t = (Read_field(ROM_fun(mpc t)) = #00010)) /\

   ((Alu_field(ROM_fun(mpc t)) = #0011) ==>
     (alu_t = SUB28 (atom_bits (arg t)) (atom_bits(bus_bits_t)))) /\
   ((Alu_field(ROM_fun(mpc t)) = #0010) ==>
     (alu_t = ADD28 (atom_bits (arg t)) (atom_bits(bus_bits_t)))) /\
   ((Alu_field(ROM_fun(mpc t)) = #0001) ==>
     (alu_t = DEC28(atom_bits(arg t)))) /\
   ((Alu_field(ROM_fun(mpc t)) = #0100) ==>
     (alu_t = DEC28(atom_bits(arg t)))) /\
   ((Alu_field(ROM_fun(mpc t)) = #0101) ==>
     (alu_t = DEC28(atom_bits(arg t)))) /\
   ((Alu_field(ROM_fun(mpc t)) = #0110) ==>
     (alu_t = DEC28(atom_bits(arg t)))) /\
   ((Alu_field(ROM_fun(mpc t)) = #1010) ==>
     (alu_t = REPLCAR (arg t) (y2 t))) /\
   ((Alu_field(ROM_fun(mpc t)) = #1011) ==>
     (alu_t = REPLCDR (arg t) (y2 t))) /\
   ((Alu_field(ROM_fun(mpc t)) = #1000) ==>
     (alu_t = SETBIT31 (arg t))) /\
   ((Alu_field(ROM_fun(mpc t)) = #0111) ==>
     (alu_t = SETBIT30 (arg t))) /\
   ((Alu_field(ROM_fun(mpc t)) = #1001) ==>
     (alu_t = RESETBIT31 (arg t))) /\
   ((Alu_field(ROM_fun(mpc t)) = #1100) ==>
     (alu_t = RESETBIT30 (arg t))) /\

   (((~(Write_field(ROM_fun(mpc t)) = #00001)) => 
      (mem_bits_t = bus_pins t) | 
      (bus_pins t = bus_bits_t))) /\
   (~(Write_field(ROM_fun(mpc t)) = #00001) /\
     (Read_field(ROM_fun(mpc t)) = #00010) ==>
     (bus_pins t = memory t (mar_pins t))) /\

   (buf1 t =
     ((Write_field(ROM_fun(mpc t)) = #00011) =>
      alu_t | buf1(PRE t))) /\
   (buf2 t =
     ((Write_field(ROM_fun(mpc t)) = #00100) =>
      alu_t | buf2(PRE t))) /\
   (mar_pins t =
     ((Write_field(ROM_fun(mpc t)) = #01010) => 
      cdr_bits(bus_bits_t) | 
      mar_pins(PRE t))) /\
   (s  t =
     ((Write_field(ROM_fun(mpc t)) = #00110) => 
      cdr_bits(bus_bits_t) | 
      s (PRE t))) /\
   (e  t =
     ((Write_field(ROM_fun(mpc t)) = #00111) => 
      cdr_bits(bus_bits_t) | 
      e (PRE t))) /\
   (c  t =
     ((Write_field(ROM_fun(mpc t)) = #01000) => 
      cdr_bits(bus_bits_t) | 
      c (PRE t))) /\
   (d  t =
     ((Write_field(ROM_fun(mpc t)) = #01001) => 
      cdr_bits(bus_bits_t) | 
      d (PRE t))) /\
   (free t =
     ((Write_field(ROM_fun(mpc t)) = #01101) => 
      cdr_bits(bus_bits_t) | 
      free(PRE t))) /\
   (x1 t =
     ((Write_field(ROM_fun(mpc t)) = #01011) => 
      cdr_bits(bus_bits_t) | 
      x1(PRE t))) /\
   (x2 t =
     ((Write_field(ROM_fun(mpc t)) = #01100) => 
      cdr_bits(bus_bits_t) | 
      x2(PRE t))) /\
   (car t =
     ((Write_field(ROM_fun(mpc t)) = #00101) => 
      car_bits(bus_bits_t) | 
      car(PRE t))) /\
   (arg t =
     ((Write_field(ROM_fun(mpc t)) = #00010) =>
      bus_bits_t | arg(PRE t))) /\
   (parent t =
     ((Write_field(ROM_fun(mpc t)) = #01110) => 
      cdr_bits(bus_bits_t) | 
      parent(PRE t))) /\
   (root t =
     ((Write_field(ROM_fun(mpc t)) = #01111) => 
      cdr_bits(bus_bits_t) | 
      root(PRE t))) /\
   (y1 t =
     ((Write_field(ROM_fun(mpc t)) = #10000) => 
      cdr_bits(bus_bits_t) | 
      y1(PRE t))) /\
   (y2 t =
     ((Write_field(ROM_fun(mpc t)) = #10001) => 
      cdr_bits(bus_bits_t) | 
      y2(PRE t))) /\
   (write_bit_pin t = ~(Write_field(ROM_fun(mpc t)) = #00001)) /\

   (flag0_pin t = (mpc t = #000010110) \/ (mpc t = #000011000)) /\
   (flag1_pin t = (mpc t = #000101011) \/ (mpc t = #000011000))))",

 DISCH_THEN
 (\th.
  CONV_TAC
  (RHS_CONV
   (R_CONJ_CONV
    (conversn ("busval:word32", "bus_bits_t:word32","bus_bits:num->*")
     THENC
     (EXISTS_CONV
      (conversn ("memval:word32", "mem_bits_t:word32","mem_bits:num->*")
       THENC
       (EXISTS_CONV
        (conversn ("aluval:word32", "alu_t:word32","alu:num->*")
        )))))))
 THEN ((CONV_TAC o RHS_CONV)
       (RIGHT_AND_EXISTS_CONV
        THENC
        (EXISTS_CONV
         (RIGHT_AND_EXISTS_CONV
          THENC (EXISTS_CONV RIGHT_AND_EXISTS_CONV)))))
 THEN (SUBST1_TAC
       ((CONV_RULE o RHS_CONV)
        (GEN_ALPHA_CONV "t:num")
        (SYM (SPEC "mpc 0 = #000000000" (INST_TYPE [":num",":*"]
                                                   FORALL_SIMP)))))
 THEN (in1_conv_tac AND_FORALL_CONV)
 THEN SUBST1_TAC (MP SYS_lemma th)
 THEN port [rr[porr [clock_constraint] th]CU_unwound_lemma])
 THEN CONV_TAC (LHS_CONV (EXISTS_PERM_LIST_CONV
  ["bus_bits:^w32_mvec";
   "mem_bits:^w32_mvec";
   "alu:^w32_mvec";
   "atomflag:^msig";    "bit30flag:^msig";    "bit31flag:^msig";
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
   "replcar:^msig";  "replcdr:^msig";  "resetbit30:^msig"]))
 THEN REPEAT BINDER_EQ_TAC
 THEN CONV_TAC
      (LHS_CONV
       (DEPTH_EXISTS_CONV
	 (REDEPTH_CONV(CHANGED_CONV FORALL_AND_CONV)
	  THENC (UNWIND_CONV
                 (\tm. mem (line_name tm)
                       [ `atomflag`; `bit30flag`; `bit31flag`; `zeroflag` 
                       ; `nilflag`; `eqflag`; `leqflag`; `ralu`
                       ; `rarg`; `rbuf1`; `rbuf2`; `rcar`; `rs`; `re`; `rc`; `rd` 
                       ; `rmar`; `rx1`; `rx2`; `rfree`; `rparent`; `rroot`
                       ; `ry1`; `ry2`; `rnum`; `rnil`; `rtrue`; `rfalse` 
                       ; `rcons`; `bidir`; `warg`; `wbuf1`; `wbuf2`; `wcar`; `ws`
                       ; `we`; `wc`; `wd`; `wmar`; `wx1`; `wx2`; `wfree` 
                       ; `wparent`; `wroot`; `wy1`; `wy2`; `dec`; `add`; `sub`; `mul`
                       ; `div`; `rem`; `setbit30`; `setbit31` 
                       ; `resetbit31`; `replcar`; `replcdr`; `resetbit30`
                       ; `rmem_pin`; `write_bit_pin`
                       ])))
	 THENC PRUNE_CONV
	 THENC (REDEPTH_CONV(CHANGED_CONV(AND_FORALL_CONV)))))
 THEN BINDER_EQ_TAC
 THEN port[CONJUNCT1 NOT_CLAUSES]
 THEN CONJUNCTS_TAC);;

% ================================================================= %
let Base_thm = save_thm
(`Base_thm`,
 ((SPEC "t:^mtime") o CONJUNCT2 o UNDISCH o fst o EQ_IMP_RULE o UNDISCH)
 SYS_Unwound_lemma
 );;

timer false;;
close_theory ();;
print_theory `-`;;
