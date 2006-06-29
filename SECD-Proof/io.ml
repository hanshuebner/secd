% SECD verification                                               %
%                                                                 %
% FILE:         io.ml                                             %
%                                                                 %
% DESCRIPTION: This file contains higher level wrappers for       %
%              the ml i/o functions.  Written by John VanTassel.  %
%                                                                 %
% USES FILES:                                                     %
%                                                                 %
% John VanTassel                                                  %
% Brian Graham 90.10.22                                           %
%                                                                 %
% Modifications:                                                  %
%                                                                 %
%=================================================================%
let write_string str file =
   if file = `nil` then tty_write str else write(file,str);;

let read_char file =
   if file = `nil` then tty_read() else (read file);;

let close_file file =
   if file = `nil` then ()
   else close file;;

let open_file direction filename =
   if filename = `nil` then `nil` 
   else if mem direction [`in` ; `input` ; `i`] then
      openi filename
   else if mem direction [`out`; `output`; `o`] then
      openw filename
   else 
      failwith (concat `can't open ` 
               (concat filename 
               (concat ` in direction ` direction)));;

% ============================================================ %
% Here are some new routines specifically for the SECD proof.  %
% ============================================================ %

%< To start, the following routines were used for FRANZ LISP,
   utilizing some higher level io commands available in it.
   These are nonstandard for Common lisp, and have been dropped
   in the present version.  They remain here as examples of how
   to build up franz lisp commands from ml.
% ============================================================ %
% I/O routines:                                                %
% *************                                                %
% The ml io functions are a bit too limited.  This io stuff    %
% permits reading int's from a file, rather than just          %
% individual characters.                                       %
% ============================================================ %
let lnil = obj_of_string `nil`
and lquote = obj_of_string `quote`;;

let ratom port =
  let a = paired_cons ((obj_of_string `EOF`),lnil) in
  let b = paired_cons (lquote,a) in
  let c = paired_cons (b,lnil) in
  let d = paired_cons (port,c) in
  let e = paired_cons((obj_of_string `ratom`),d) in
  let f = lisp_eval e in
  (is_int f) => (int_of_obj f) | failwith `end-of-file`;;
>%

% ============================================================ %
% Here are the generic common lisp routines.                   %
% ============================================================ %
let blanks =
[ ` `
; `	`
; `
`];;

let digits = 
[`0`;`1`;`2`;`3`;`4`;`5`;`6`;`7`;`8`;`9`];;

let letters =
[`a`;`b`;`c`;`d`;`e`;`f`;`g`;`h`;`i`;`j`;`k`;`l`;`m`;
 `n`;`o`;`p`;`q`;`r`;`s`;`t`;`u`;`v`;`w`;`x`;`y`;`z`;
 `A`;`B`;`C`;`D`;`E`;`F`;`G`;`H`;`I`;`J`;`K`;`L`;`M`;
 `N`;`O`;`P`;`Q`;`R`;`S`;`T`;`U`;`V`;`W`;`X`;`Y`;`Z`
];;

letrec read_atom file =
  let char = read_char file
  in
  ((mem char blanks) 
   => (read_atom file)
   | (mem char digits)
     => (implode (char . (read_number file)))
      | (mem char letters)
        => (implode (char . (read_symbol file)))
         | (char = `nil`)
           => failwith `attempt to read past end of file`
            | failwith (`unknown character read:`^char))
whererec
 read_number file =
  (let char = read_char file
   in
   (mem char blanks)
   => []:(string)list
    | char . (read_number file))
and
 read_symbol file = 
  (let char = read_char file
   in
   (mem char blanks)
   => []:(string)list
    | char . (read_symbol file))
;;
