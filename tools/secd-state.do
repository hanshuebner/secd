#!/bin/perl -Ih:\fpga\secd\tools -- -*- Perl -*-

#use strict;
push @INC, 'h:\fpga\secd\tools';

use Aldec::ActiveHDL;
use SECD;

$prefix = "/UUT";

read_ram();

my $register;
foreach $register (qw/s e c d/) {
    my $pointer = hex(Examine("$prefix/my_datapath/$register", 16));
    $count = 0;
    print "$register: ";
    print_as_sexp($pointer);
    print "\n";
}

my $c = hex(Examine("$prefix/my_datapath/c", 16));
my $opcode = lit(car($c));

print "opcode: ", $opcode, " ", $SECD_OPS[$opcode], "\n";
