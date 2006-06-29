#!/bin/perl -Ih:\fpga\secd\tools -- -*- Perl -*-

#use strict;
push @INC, 'h:\fpga\secd\tools';

use Aldec::ActiveHDL;
use SECD;

$prefix = "/UUT";

read_ram();

print "Result: ";
print_as_sexp(16383);
print "\n";
