program LispKit;

(*-----------------------------------------------------------------*)
(*                                                                 *)
(*   Reference model lazy interactive SECD machine, 3              *)
(*      -- version 3a                                    April 83  *)
(*      -- IMPLODE and EXPLODE instructions, version 3b    May 83  *)
(*                                                                 *)
(*   Modifications specific to VAX VMS Pascal gaj        April 83  *)
(*   Break long lines in file output gaj                August 83  *)
(*   I/O compatible with both version 1 & 2 compilers    April 84  *)
(*                                                                 *)
(*   Ported to GNU Pascal version 4.0 ang             November 05  *)
(*                                                                 *)
(*-----------------------------------------------------------------*)
(*                                                                 *)
(*    (c)  Copyright  P Henderson, G A Jones, S B Jones            *)
(*                    Oxford University Computing Laboratory       *)
(*                    Programming Research Group                   *)
(*                    8-11 Keble Road                              *)
(*                    OXFORD  OX1 3QD                              *)
(*                                                                 *)
(*-----------------------------------------------------------------*)
(*                                                                 *)
(*   Documentation:                                                *)
(*                                                                 *)
(*     P Henderson, G A Jones, S B Jones                           *)
(*         The LispKit Manual                                      *)
(*         Oxford University Computing Laboratory                  *)
(*         Programming Research Group technical monograph PRG-32   *)
(*         Oxford, August 1983                                     *)
(*                                                                 *)
(*     P Henderson                                                 *)
(*         Functional Programming: Application and Implementation. *)
(*         Prentice-Hall International, London, 1980               *)
(*                                                                 *)
(*-----------------------------------------------------------------*)

(*------------------ Machine dependent constants ------------------*)

label 99;

const TopCell = 40000;     (*    size of heap storage    *)
      FileRecordLimit = 255;
      OutFileWidth = 200;
      OutTermWidth = 80;

(*--------------- Machine dependent file management ---------------*)

var InOpen : boolean;
    InFile : text;
    NewInput, InFromTerminal, OutToTerminal : boolean;
    OutFile : text;
    OutFileColumn : integer;
    OutTermColumn : integer;

procedure OpenInFile;
var s : string[255];
begin
      writeln(Output);
      write(Output, 'Take input from where? ');
      readln(Input, s);
      if (s = '') or (s = 'CONSOLE:') or (s = 'console:')
#if defined(__MINGW32__) || defined( __CYGWIN__)
         or (s = 'CON:') or (s = 'con:')
#endif
      then
        begin;
#if defined(__MINGW32__) || defined( __CYGWIN__)
          assign(InFile, 'con:');
#else
          assign(InFile,'/dev/tty');
#endif
          InFromTerminal := true;
        end
      else
        begin;
          assign(InFile, s);
          InFromTerminal := false;
        end;
      {$I-}
      reset(InFile);
      {$I+}

      if IOResult<>0 then
        begin
          InOpen:=false;
          write(Output, 'Cannot read from that file')
        end
      else
        InOpen := true;
end {OpenInFile};

procedure CloseInFile; begin close(InFile); InOpen := false end;

procedure ChangeOutFile;
var s : string[255];
    ok : boolean;
begin
      close(OutFile);
      repeat
        writeln(Output);
        write(Output, 'Send output to where? ');
        readln(Input,s);
        if (s = '') or (s = 'CONSOLE:') or (s = 'console:')
#if defined(__MINGW32__) || defined( __CYGWIN__)
           or (s = 'CON:') or (s = 'con:')
#endif
        then
          begin;
#if defined(__MINGW32__) || defined( __CYGWIN__)
            assign(OutFile,'con:');
#else
            assign(OutFile,'/dev/tty');
#endif
            OutToTerminal := true;
          end
        else
          begin;
            assign(OutFile,s);
            OutToTerminal := false;
          end;
        {$I-}
        rewrite(OutFile);
        {$I+}
        ok:= IOResult=0;
        if not ok Then
          write(Output, 'Cannot write to that file')
      until ok;
      OutTermColumn := 0;
      OutFileColumn := 0
end {ChangeOutFile};

(*------------------- Character input and output ------------------*)

procedure GetChar(VAR ch : char);
const EM = 25; // Ctrl-Y
begin
      while not InOpen do begin OpenInFile; NewInput := true end;
      if eof(InFile) then begin CloseInFile; ch := ' ' end
      else
        if eoln(InFile) then
              begin readln(InFile); NewInput := true; ch := ' ' end
      else
        begin
              if NewInput then
                begin if InFromTerminal then OutTermColumn := 0;
                      NewInput := false
                end;
              read(InFile, ch);
              if ch = chr(EM) then
                   begin readln(InFile); ChangeOutFile; ch := ' ' end
        end;
end {GetChar};

procedure PutChar(ch : char);
const CR = 13;
begin
      if ch = ' '
      then if OutToTerminal then
              begin if OutTermColumn >= OutTermWidth then ch := chr(CR) end
           else
              begin if OutFileColumn >= OutFileWidth then ch := chr(CR) end;
      if ch = chr(CR) then
         begin writeln(OutFile);
               if OutToTerminal then
                     OutTermColumn := 0
               else OutFileColumn := 0
         end
      else
         begin write(OutFile, ch);
               if OutToTerminal then
                    OutTermColumn := OutTermColumn + 1
               else OutFileColumn := OutFileColumn + 1
         end
end {PutChar};

(*------- Machine dependent initialisation and finalisation -------*)

procedure Initialise(Version, SubVersion : char);
begin
      writeln(Output, 'Pascal SECD machine ', Version, '.', SubVersion);
      assign(InFile,'loader.cls');
      {$I-}
      reset(InFile);
      {$I+}

      InOpen := IOResult = 0;
      If Not InOpen Then
        writeln(Output, 'No file loader.cls');
      NewInput := true;

#if defined(__MINGW32__) || defined( __CYGWIN__)
      assign(OutFile,'con:');
#else
      assign(OutFile,'/dev/tty');
#endif
      rewrite(OutFile);
      OutToTerminal := true;
      OutTermColumn := 0;
      OutFileColumn := 0
end {Initialise};

procedure Terminate;
begin
  writeln(OutFile);
  close(OutFile);
  goto 99;
end {Terminate};

(*--------- The code which follows is in Standard Pascal ----------*)
(*   As far as is possible, it is also machine independent.   The  *)
(*  most obvious machine dependency is that the character code of  *)
(*  the host machine has been assumed to be ISO-7 or similar.      *)
(*-----------------------------------------------------------------*)

procedure Machine;

const Version = '4';
      SubVersion = '0';

type TokenType = (Numeric, Alpha, Delimiter);

// this is not bitpacked in FPC
var Marked, IsAtom, IsNumb : packed array [1..TopCell] of 0..1;
        {-----------------------------------------------}
        {       Cell type coding:   IsAtom   IsNumb     }
        {       Cons                  0         0       }
        {       Recipe                0         1       }
        {       Number                1         1       }
        {       Symbol                1         0       }
        {-----------------------------------------------}
    Head, Tail : array[1..TopCell] of integer;
        {-----------------------------------------------}
        { Head is also used for value of integer, IVAL  }
        {                       pointer to symbol, SVAL }
        {                       BODY of recipe          }
        { Tail is also used for ENVironment of recipe   }
        {-----------------------------------------------}

    S, E, C, D, W, SymbolTable : integer;
    NILL, T, F, OpenParen, Point, CloseParen : integer;
    FreeCell : integer;
    Halted : boolean;

    InCh : char;
    InTokType : TokenType;

(*------------------ Garbage collection routines ------------------*)

procedure CollectGarbage;

    procedure Mark(n : integer);
    begin if Marked[n] = 0
          then begin Marked[n] := 1;
                     if (IsAtom[n] = 0) or (IsNumb[n] = 0) then
                            begin Mark(Head[n]); Mark(Tail[n]) end
          end
    end {Mark};

    procedure MarkAccessibleStore;
    begin Mark(NILL); Mark(T); Mark(F);
          Mark(OpenParen); Mark(Point); Mark(CloseParen);
          Mark(S); Mark(E); Mark(C); Mark(D); Mark(W)
    end;

    procedure ScanSymbols(var i : integer);
    begin if i <> NILL then
                if Marked[Head[Head[i]]] = 1 then
                      begin Marked[i] := 1;
                            Marked[Head[i]] := 1;
                            ScanSymbols(Tail[i])
                      end
                else begin i := Tail[i]; ScanSymbols(i) end
    end;

    procedure ConstructFreeList;
    var i : integer;
    begin for i := 1 to TopCell do
             if Marked[i] = 0 then
                  begin Tail[i] := FreeCell; FreeCell := i end
             else Marked[i] := 0
    end;

begin MarkAccessibleStore;
      ScanSymbols(SymbolTable);
      FreeCell := 0;
      ConstructFreeList;
      if FreeCell = 0 then
            begin writeln(Output, 'Cell store overflow'); Terminate end
end {CollectGarbage};

(*------------------ Storage allocation routines ------------------*)

function Cell : integer;
begin if FreeCell = 0 then CollectGarbage;
      Cell := FreeCell;
      FreeCell := Tail[FreeCell]
end {Cell};

function Cons : integer;
var i : integer;
begin i := Cell;
      IsAtom[i] := 0; IsNumb[i] := 0; Head[i] := NILL; Tail[i] := NILL;
      Cons := i
end {Cons};

function Recipe : integer;
var i : integer;
begin i := Cell;
      IsAtom[i] := 0; IsNumb[i] := 1; Head[i] := NILL; Tail[i] := NILL;
      Recipe := i
end {Recipe};

function Symb : integer;
var i : integer;
begin i := Cell;
      IsAtom[i] := 1; IsNumb[i] := 0; Head[i] := NILL; Tail[i] := NILL;
      Symb := i
end {Symb};

function Numb : integer;
var i : integer;
begin i := Cell;
      IsAtom[i] := 1; IsNumb[i] := 1;
      Numb := i
end {Numb};

function IsCons(i : integer) : boolean;
begin IsCons := (IsAtom[i] = 0) and (IsNumb[i] = 0) end;

function IsRecipe(i : integer) : boolean;
begin IsRecipe := (IsAtom[i] = 0) and (IsNumb[i] = 1) end;

function IsNumber(i : integer) : boolean;
begin IsNumber := (IsAtom[i] = 1) and (IsNumb[i] = 1) end;

function IsSymbol(i : integer) : boolean;
begin IsSymbol := (IsAtom[i] = 1) and (IsNumb[i] = 0) end;

function IsNill(i : integer) : boolean;
begin IsNill := IsSymbol(i) and (Head[i] = Head[NILL]) end;

procedure Store(var T : integer);
var Si, Sij, Tj : integer;
    found : boolean;
begin Tj := T;
      if IsAtom[Tj] = 1 then Tj := NILL
      else
        begin while IsAtom[Tail[Tj]] = 0 do Tj := Tail[Tj];
              Tail[Tj] := NILL
        end;
      Si := SymbolTable; found := false;
      while (not found) and (Si <> NILL) do
          begin Sij := Head[Head[Si]]; Tj := T; found := true;
                while found and (Tj <> NILL) and (Sij <> NILL) do
                   begin if Head[Tj] <> Head[Sij] then
                             if Head[Head[Tj]] = Head[Head[Sij]]
                             then Head[Tj] := Head[Sij]
                             else found := false;
                         Tj := Tail[Tj]; Sij := Tail[Sij]
                   end;
                if found then found := Tj = Sij;
                if found then T := Head[Si] else Si := Tail[Si]
          end;
      if not found then
          begin Tj := T;         (* NB: T may be an alias for W *)
                W := Cons;
                Tail[W] := Tj;
                Head[W] := Symb;
                Head[Head[W]] := Tail[W];
                Tail[W] := SymbolTable;
                SymbolTable := W;
                T := Head[W]
          end
end {Store};

procedure InitListStorage;

        var i : integer;

        function List(ch : char) : integer;
        begin W := Cons;
              Head[W] := Numb; Head[Head[W]] := ord(ch);
              List := W
        end {List};

    procedure OneChar(var reg : integer; ch : char);
    begin reg := List(ch); Store(reg) end {OneChar};

begin FreeCell := 1;
      for i := 1 to TopCell - 1 do begin Marked[i] := 0; Tail[i] := i + 1 end;
      Marked[TopCell] := 0;
      Tail[TopCell] := 0;
      NILL := Symb; Head[NILL] := NILL; Tail[NILL] := NILL;
      S := NILL; E := NILL; C := NILL; D := NILL; W := NILL;
      T := NILL; F := NILL;
      OpenParen := NILL; Point := NILL; CloseParen := NILL;
      Head[NILL] := List('N');
      Tail[Head[NILL]] := List('I');
      Tail[Tail[Head[NILL]]] := List('L');
      SymbolTable := Cons;
    { Head[SymbolTable] := NILL; the symbol ...     }
    { Tail[SymbolTable] := NILL; the empty list ... }
      OneChar(T, 'T');
      OneChar(F, 'F');
      OneChar(OpenParen, '(');
      OneChar(Point, '.');
      OneChar(CloseParen, ')')
end {InitListStorage};

procedure Update(x, y : integer);
begin IsAtom[x] := IsAtom[y];
      IsNumb[x] := IsNumb[y];
      Head[x] := Head[y];
      Tail[x] := Tail[y]
end {Update};

(*--------------------- Token input and output --------------------*)

procedure GetToken(var Token : integer);
var x : char;
    p : integer;
begin while InCh = ' ' do GetChar(InCh);
      x := InCh;
      GetChar(InCh);
      if (('0' <= x) and (x <= '9'))
        or (    ((x = '-') or (x = '+'))
            and ('0' <= InCh) and (InCh <= '9')) then
              begin InTokType := Numeric;
                    Token := Numb;
                    if (x = '+') or (x = '-')
                        then Head[Token] := 0
                        else Head[Token] := ord(x) - ord('0');
                    while ('0' <= InCh) and (InCh <= '9') do
                        begin Head[Token] := (10 * Head[Token])
                                           + (ord(InCh) - ord('0'));
                              GetChar(InCh)
                        end;
                    if x = '-' then Head[Token] := - Head[Token]
              end
   else
        if (x = '(') or (x = ')') or (x = '.') then
              begin InTokType := Delimiter;
                    if x = '(' then Token := OpenParen
               else if x = '.' then Token := Point
               else Token := CloseParen
              end
   else
        begin InTokType := Alpha;
              Token := Cons; p := Token;
              Head[p] := Numb; Head[Head[p]] := ord(x);
              while not ( (InCh = '(') or (InCh = ')')
                       or (InCh = '.') or (InCh = ' ') ) do
                  begin Tail[p] := Cons; p := Tail[p];
                        Head[p] := Numb; Head[Head[p]] := ord(InCh);
                        GetChar(InCh)
                  end;
              Store(Token)
        end
end {GetToken};

procedure PutSymbol(Symbol : integer);
var p : integer;
begin p := Head[Symbol];
      while p <> NILL do begin PutChar(chr(Head[Head[p]])); p := Tail[p] end;
      PutChar(' ')
end {PutSymbol};

procedure PutNumber(Number : integer);

  procedure PutN(n : integer);
  begin if n > 9 then PutN(n div 10); PutChar(chr(ord('0') + (n mod 10))) end;

begin if Head[Number] < 0 then begin PutChar('-'); PutN(-Head[Number]) end
                          else PutN(Head[Number]);
      PutChar(' ')
end {PutNumber};

procedure PutRecipe(E : integer);
begin PutChar('*');
      PutChar('*');
      PutChar('R');
      PutChar('E');
      PutChar('C');
      PutChar('I');
      PutChar('P');
      PutChar('E');
      PutChar('*');
      PutChar('*');
      PutChar(' ')
end {PutRecipe};

(*----------------- S-expression input and output -----------------*)

procedure GetExp(var E : integer);

    procedure GetList(var E : integer);
    begin if E = CloseParen then E := NILL
          else begin W := Cons; Head[W] := E; E := W;
                     if Head[E] = OpenParen then
                         begin GetToken(Head[E]); GetList(Head[E]) end;
                     GetToken(Tail[E]);
                     if Tail[E] = Point then
                          begin GetExp(Tail[E]); GetToken(W) end
                     else GetList(Tail[E])
               end
    end {GetList};

begin GetToken(E); if E = OpenParen then begin GetToken(E); GetList(E) end
end {GetExp};

procedure PutExp(E : integer);
var p : integer;
begin
 if IsRecipe(E) then PutRecipe(E)
 else if IsSymbol(E) then PutSymbol(E)
 else if IsNumber(E) then PutNumber(E)
 else begin PutSymbol(OpenParen);
            p := E;
            while IsCons(p) do begin PutExp(Head[p]); p := Tail[p] end;
            if not IsNill(p) then begin PutSymbol(Point); PutExp(p) end;
            PutSymbol(CloseParen)
      end
end {PutExp};

procedure LoadBootstrapProgram;
begin
      InCh := ' ';
      GetExp(S);                  (* NB GetExp corrupts W *)
      E := Tail[S]; C := Head[S];
      S := NILL; D := NILL; W := NILL;
end {LoadBootstrapProgram};

(*------------- Microcode for SECD machine operations -------------*)

//
//  LD - instruction #1
//
//        S E (LD (a.b).C) D  ->  (x.S) E C D
//
//  where x is the b'th element of the a'th element of E
//

procedure LDX;
var Wx, i : integer;
begin
      Wx := E;
      for i := 1 to Head[Head[Head[Tail[C]]]] do Wx := Tail[Wx];
      Wx := Head[Wx];
      for i := 1 to Head[Tail[Head[Tail[C]]]] do Wx := Tail[Wx];
      Wx := Head[Wx];
      W := Cons; Head[W] := Wx; Tail[W] := S; S := W;
      C := Tail[Tail[C]]
end {LDX};

//
//  LDC - instruction #2
//
//      S E (LD c.C) D  ->  (c.S) E C D
//

procedure LDCX;
begin
      W := Cons; Head[W] := Head[Tail[C]]; Tail[W] := S; S := W;
      C := Tail[Tail[C]]
end {LDCX};

//
// LDF - instruction #3
//
//      S E (LDF c.C) D  ->  ((c.E).S) E C D
//

procedure LDFX;
begin
      W := Cons; Head[W] := Cons;
      Head[Head[W]] := Head[Tail[C]]; Tail[Head[W]] := E;
      Tail[W] := S; S := W;
      C := Tail[Tail[C]]
end {LDFX};

//
//  AP - instruction #4
//
//      ((c.r) a.S) E (AP.C) D  ->  NIL (a.r) c (S E C.D)
//

procedure APX;
begin
      W := Cons; Head[W] := Tail[Tail[S]];
      Tail[W] := Cons; Head[Tail[W]] := E;
      Tail[Tail[W]] := Cons; Head[Tail[Tail[W]]] := Tail[C];
      Tail[Tail[Tail[W]]] := D; D := W;
      W := Cons; Head[W] := Head[Tail[S]]; Tail[W] := Tail[Head[S]]; E := W;
      C := Head[Head[S]];
      S := NILL
end {APX};

//
//  RTN - instruction #5
//
//      (a.s) e (RTN.c) (S E C.D)  ->  (a.S) E C D
//

procedure RTNX;
begin
      W := Cons; Head[W] := Head[S]; Tail[W] := Head[D]; S := W;
      E := Head[Tail[D]];
      C := Head[Tail[Tail[D]]];
      D := Tail[Tail[Tail[D]]]
end {RTNX};

//
//  DUM - instruction #6
//
//      S E (DUM.C) D  ->  S (NIL.E) C D
//

procedure DUMX;
begin W := Cons; Head[W] := NILL; Tail[W] := E; E := W; C := Tail[C] end {DUMX};

//
//  RAP - instruction #7
//
//      ((c.(x.e)) q.S) (r.E) (RAP.C) D  ->  NIL (q.e) c (S E C.D)
//

procedure RAPX;
begin
      W := Cons; Head[W] := Tail[Tail[S]];
      Tail[W] := Cons; Head[Tail[W]] := Tail[E];
      Tail[Tail[W]] := Cons; Head[Tail[Tail[W]]] := Tail[C];
      Tail[Tail[Tail[W]]] := D; D := W;
      E := Tail[Head[S]]; Head[E] := Head[Tail[S]];
      C := Head[Head[S]];
      S := NILL
end {RAPX};

//
//  SEL - instruction #8
//
//      (T.S) E (SEL t e.j) D  ->  S E t (j.D)
//      (x.S) E (SEL t e.j) D  ->  S E e (j.D)  unless x = T
//

procedure SELX;
begin
      W := Cons; Head[W] := Tail[Tail[Tail[C]]]; Tail[W] := D; D := W;
      if Head[Head[S]] = Head[T] then C := Head[Tail[C]]
                                 else C := Head[Tail[Tail[C]]];
      S := Tail[S]
end {SELX};

//
//  JOIN - instruction #9
//
//      S E (JOIN.C) (c.D)  ->  S E c D
//

procedure JOINX; begin C := Head[D]; D := Tail[D] end {JOINX};

//
//  CAR
//
//      ((a.b).S) E (CAR.C) D  ->  (a.S) E C D
//

procedure CARX;
begin
      W := Cons; Head[W] := Head[Head[S]]; Tail[W] := Tail[S]; S := W;
      C := Tail[C]
end {CARX};

//
//  CDR
//
//      ((a.b).S) E (CDR.C) D  ->  (b.S) E C D
//

procedure CDRX;
begin
      W := Cons; Head[W] := Tail[Head[S]]; Tail[W] := Tail[S]; S := W;
      C := Tail[C]
end {CDRX};

//
//  ATOM - instruction #12
//
//      (a.S) E (ATOM.C) D      ->  (T.S) E C D
//      ((a.b).S) E (ATOM.C) D  ->  (F.S) E C D
//

procedure ATOMX;
begin
      W := Cons;
      if IsAtom[Head[S]] = 1 then Head[W] := T else Head[W] := F;
      Tail[W] := Tail[S]; S := W;
      C := Tail[C]
end {ATOMX};

//
//  CONS - instruction #13
//
//      (a b.S) E (CONS.C) D  ->  ((a.b).S) E C D
//

procedure CONSX;
begin
      W := Cons; Head[W] := Cons;
      Head[Head[W]] := Head[S]; Tail[Head[W]] := Head[Tail[S]];
      Tail[W] := Tail[Tail[S]]; S := W;
      C := Tail[C]
end {CONSX};

//
//  EQ
//
//      (a a.S) E (EQ.C) D  ->  (T.S) E C D     if a == b
//      (a b.S) E (EQ.C) D  ->  (F.S) E C D     if a <> b
//

procedure EQX;
begin
      W := Cons;
      if ( ( IsSymbol(Head[S]) and IsSymbol(Head[Tail[S]]) )
        or ( IsNumber(Head[S]) and IsNumber(Head[Tail[S]]) ) )
       and (Head[Head[S]] = Head[Head[Tail[S]]])
      then Head[W] := T
      else Head[W] := F;
      Tail[W] := Tail[Tail[S]]; S := W;
      C := Tail[C]
end {EQX};

//
//  ADD - instruction #15
//
//      (a b.S) E (ADD.C) D  ->  ((a+b).S) E C D
//

procedure ADDX;
begin
      W := Cons;
      Head[W] := Numb; Head[Head[W]] := Head[Head[Tail[S]]] + Head[Head[S]];
      Tail[W] := Tail[Tail[S]]; S := W;
      C := Tail[C]
end {ADDX};

//
//  SUB - instruction #16
//
//      (a b.S) E (SUB.C) D  ->  ((b-a).S) E C D
//

procedure SUBX;
begin
      W := Cons;
      Head[W] := Numb; Head[Head[W]] := Head[Head[Tail[S]]] - Head[Head[S]];
      Tail[W] := Tail[Tail[S]]; S := W;
      C := Tail[C]
end {SUBX};

//
//  MUL - instruction #17
//
//      (a b.S) E (MUL.C) D  ->  ((a*b).S) E C D
//

procedure MULX;
begin
      W := Cons;
      Head[W] := Numb; Head[Head[W]] := Head[Head[Tail[S]]] * Head[Head[S]];
      Tail[W] := Tail[Tail[S]]; S := W;
      C := Tail[C]
end {MULX};

//
//  DIV - instruction #18
//
//      (a b.S) E (DIV.C) D  ->  ((b/a).S) E C D
//

procedure DIVX;
begin
      W := Cons;
      Head[W] := Numb; Head[Head[W]] := Head[Head[Tail[S]]] div Head[Head[S]];
      Tail[W] := Tail[Tail[S]]; S := W;
      C := Tail[C]
end {DIVX};

//
//  REM - instruction #19
//
//      (a b.S) E (REM.C) D  ->  ((b%a).S) E C
//

procedure REMX;
begin
      W := Cons;
      Head[W] := Numb; Head[Head[W]] := Head[Head[Tail[S]]] mod Head[Head[S]];
      Tail[W] := Tail[Tail[S]]; S := W;
      C := Tail[C]
end {REMX};

//
//  LEQX
//
//      (a b.S) E (ADD.C) D  ->  ((a>=b).S) E C D
//

procedure LEQX;
begin
      W := Cons;
      if Head[Head[Tail[S]]] <= Head[Head[S]] then Head[W] := T
                                              else Head[W] := F;
      Tail[W] := Tail[Tail[S]]; S := W;
      C := Tail[C]
end {LEQX};

//
//  STOP - instruction #21
//
//      (a.S) E (STOP.C) D  ->  (a.S) E (STOP.C) D if a is an atom
//      (((c.r).a).S) E (STOP.C) D  ->  NIL (a.r) c (S E (STOP.C).D)
//

procedure STOPX;
begin
      if IsAtom[Head[S]] = 1 then Halted := true
      else begin W := Cons; Head[W] := Tail[S];
                 Tail[W] := Cons; Head[Tail[W]] := E;
                 Tail[Tail[W]] := Cons; Head[Tail[Tail[W]]] := C;
                 Tail[Tail[Tail[W]]] := D; D := W;
                 C := Head[Head[Head[S]]];
                 W := Cons;
                 Head[W] := Tail[Head[S]]; Tail[W] := Tail[Head[Head[S]]];
                 E := W;
                 S := NILL
           end
end {STOPX};

//
//  LDE - instruction #22
//
//      S E (LDE x.C) D  -> ((recipe x.E).S) E C D
//

procedure LDEX;
begin
      W := Cons; Tail[W] := S; S := W;
      Head[W] := Recipe; Head[Head[W]] := Head[Tail[C]]; Tail[Head[W]] := E;
      C := Tail[Tail[C]]
end {LDEX};

//
//  UPD - instruction #23
//
//      (x.s) e c ((a.S) E C.D)  ->  (a.S) E C D
//                      but also, a := x
//

procedure UPDX;
begin
      Update(Head[Head[D]],Head[S]);
      S := Head[D];
      E := Head[Tail[D]];
      C := Head[Tail[Tail[D]]];
      D := Tail[Tail[Tail[D]]]
end {UPDX};

//
//  AP0 - instruction #24
//
//      ((rec c.e).S) E (AP0.C) D  ->  NIL e c (((rec c.e).S) E C.D)
//      (a.S) E (AP0.C) D  ->  (a.S) E C D if a is not a recipe
//

procedure AP0X;
begin
      if IsRecipe(Head[S]) then
          begin W := Cons; Head[W] := S;
                Tail[W] := Cons; Head[Tail[W]] := E;
                Tail[Tail[W]] := Cons; Head[Tail[Tail[W]]] := Tail[C];
                Tail[Tail[Tail[W]]] := D; D := W;
                C := Head[Head[S]];
                E := Tail[Head[S]];
                S := NILL
          end
      else
          C := Tail[C]
end {AP0X};

//
//  READ - instruction #25
//
//      S E (READ.C) D  ->  (x.S) E C D
//

procedure READX;
begin W := Cons; Tail[W] := S; S := W; GetExp(Head[S]); C := Tail[C] end {READX}
;

//
//  PRINT - instruction #26
//
//      (x.S) E (PRINT.C) D  ->  S E C D
//

procedure PRINTX; begin PutExp(Head[S]); S := Tail[S]; C := Tail[C] end {PRINTX}
;

//
//  IMPLODE - instruction #27
//
//       (x.S) E (IMPLODE.C) D  ->  (y.S) E C D
//
//    where, if x is a list of character codes, then y is the symbol
//                  with that representation
//           if x is the number 32 (space in ASCII), then y is the
//                  null symbol
//           if x is any other number, then y is the symbol whose
//                  representation consists of the single character
//                  with that character code
//

procedure IMPLODEX;
begin
      W := Cons; Head[W] := Head[S]; Tail[W] := Tail[S]; S := W;
      if IsNumber(Head[S]) then
            if Head[Head[S]] = ord(' ') then Head[S] := NILL
                  else begin W := Cons; Head[W] := Head[S]; Head[S] := W end;
      Store(Head[S]);
      C := Tail[C]
end {IMPLODEX};

//
//  EXPLODE - instruction #28
//
//       (x.S) E (EXPLODE.C) D  ->  (y.S) E C D
//
//     where y is the list of character codes for the characters which
//     form the representation of the symbol x
//

procedure EXPLODEX;
begin
      W := Cons; Head[W] := Head[Head[S]]; Tail[W] := Tail[S]; S := W;
      C := Tail[C]
end {EXPLODEX};

(*-------------------- Instruction decode loop --------------------*)

procedure FetchExecuteLoop;
label 1;
begin
   Halted := false;
   1: case Head[Head[C]] of
                 1:   LDX;              11:  CDRX;
                 2:  LDCX;              12: ATOMX;
                 3:  LDFX;              13: CONSX;
                 4:   APX;              14:   EQX;
                 5:  RTNX;              15:  ADDX;
                 6:  DUMX;              16:  SUBX;
                 7:  RAPX;              17:  MULX;
                 8:  SELX;              18:  DIVX;
                 9: JOINX;              19:  REMX;
                10:  CARX;              20:  LEQX;

                21: begin STOPX; if Halted then Terminate end;

                22: LDEX;               25: READX;
                23: UPDX;               26: PRINTX;
                24: AP0X;               27: IMPLODEX;
                                        28: EXPLODEX
      end;
      goto 1
end {FetchExecuteLoop};

(*------------------ body of procedure Machine --------------------*)

begin
  Initialise(Version, SubVersion);
  InitListStorage;
  LoadBootstrapProgram;
  writeln( Output, 'Program loaded');
  FetchExecuteLoop
end {Machine};

(*------------------- body of program LispKit ---------------------*)

begin
  Machine; 99:
end {LispKit}.
