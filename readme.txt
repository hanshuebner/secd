This directory contains the VHDL implementation of the SECD microprocessor
as designed by Brian T. Graham.  This implementation has been done as an
exercise in VHDL by Hans Hübner (hans.huebner@gmail.com).  It is a work
in progress and published for reference and amusement.

Copyright 2006 for the VHDL implementation and the microcode tools in
the lisp-tools/ directory by Hans Hübner.  Other copyrights apply to
the SECD-Proof/ and the lispkit/ directory.

To use this, you need a Common Lisp implementation in order to
assemble microcode files and translate sexpr files containing SECD
code in list form to binary images that can be run in the simulator.
The common lisp code is in lisp-tools and should in be portable.
