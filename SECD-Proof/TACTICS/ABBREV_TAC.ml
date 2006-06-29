% ================================================================= %
% ABBREV_TAC: term->term->tactic                                    %
% ***********                                                       %
%                                                                   %
% Synopsis: abbreviates a term in the goal by adding an assumption  %
%    that the term equals a variable, and substituting the variable %
%    for all occurrences of the term.                               %
%                                                                   %
% Description: A theorem of the form:                               %
% 		|- ?v. v = tm                                       %
%    is generated, CHOOSE_THEN specializes to v, or if not free,    %
%    a quoted variant of v, and the resultant theorem is used to    %
%    substitute var for all instances of tm in the goal.  Lastly,   %
%    the theorem is added to the assumption list.                   %
%                                                                   %
%               {a1;...;an}, gl                                     %
%    ==========================================  ABBREV_TAC tm v    %
%     {a1[v/tm];...;an[v/tm];"tm=v"}, gl[v/tm]                      %
%                                                                   %
% Failure: fails if arguments do not type match, or 2nd argument is %
%    not a free variable.                                           %
%                                                                   %
% Uses: Substitutes a variable for a large or frequent subterm in   %
%       the goal, to simplify the detection of patterns, etc.       %
%       The original goal is retrieved by substituting with the     %
%       assumption which defines the introduced variable, and       %
%       discarding it.                                              %
%                                                                   %
% Written by: Brian Graham 26.11.90                                 %
%             from a suggestion by Jeff Joyce in Aug, 90.           %
% ================================================================= %
let ABBREV_TAC tm var =
 if (is_var var)
 then (if (type_of tm = type_of var)
       then (CHOOSE_THEN (\th. SUBST_ALL_TAC th THEN ASSUME_TAC th)
                         (EXISTS ("?^var.^tm=^var",tm) (REFL tm)))
       else failwith `ABBREV_TAC: type mismatch`)
 else failwith `ABBREV_TAC: 2nd argument must be a variable`
 ;;

