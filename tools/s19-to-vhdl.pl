#!/bin/perl -w

use strict;
use Getopt::Std;

my %opt;

getopts('s:n:b', \%opt);

my $s19_filename = shift @ARGV;
my $rom_name = ($opt{n} or "ROM");

sub usage {
    die "usage: $0 [-s <size>] <input>.s19\n";
}

usage() unless ($s19_filename);

if ($s19_filename !~ /(.*)\.s19$/) {
    print STDERR "$0: Bad file suffix\n";
    usage();
}
my $vhdl_filename = "$1.vhd";
my $bin_filename;

if ($opt{b}) {
    $bin_filename = "$1.bin";
}

open(S19, $s19_filename) or die "$0: can't open input file $s19_filename: $!\n";
open(VHDL, ">$vhdl_filename") or die "$0: can't open vhdl output file $vhdl_filename for writing: $!\n";
if ($bin_filename) {
    open(BIN, ">$bin_filename") or die "$0: can't open binary output file $bin_filename for writing: $!\n";
}

my $origin = 0xFFFF;
my $end = 0;

my @ROM = '';

while (<S19>) {
    if (/^S1(..)(....)(.*)\r?\n/) {
        my $length = hex($1);
        my $address = hex($2);
        my $data = $3;
        if ($address < $origin) {
            $origin = $address;
        }
        my $i;
        for ($i = 0; $i < ($length - 2); $i++) {
            $ROM[$address + $i] = hex(substr($data, $i * 2, 2));
        }
        if (($i + $address) > $end) {
            $end = $i + $address - 1;
        }
    } elsif (/^S9/) {
        last;
    } else {
        die "bad input";
    }
}

my $rom_size = ($opt{s} or ($end - $origin));
@ROM = splice(@ROM, $origin);

for (my $i = ($end - $origin); $i < $rom_size; $i++) {
    $ROM[$i] = 0;
}

die "empty rom" unless ($rom_size);

print VHDL "
-- Automatically generated ROM initialization definitions for System09
-- Converted from S19 file $s19_filename
-- DO NOT EDIT!

library ieee;

use ieee.std_logic_1164.all;
use ieee.numeric_std.all;

package ${rom_name}_defs is

constant ${rom_name}_size : integer := $rom_size;
type ${rom_name}_type is array (0 to (${rom_name}_size - 1)) of std_logic_vector (7 downto 0);
constant ${rom_name}_init : ${rom_name}_type := (
    ";
for (my $i = 0; $i <= $#ROM; $i++) {
    if ($bin_filename) {
        print BIN pack('a', chr($ROM[$i]));
    }
    printf VHDL "X\"%02X\"", ($ROM[$i] or 0);
    if ($i != $#ROM) {
        print VHDL ",";
    }
    if (($i % 8) == 7) {
        print VHDL "\n    ";
    } else {
        print VHDL " ";
    }
}
print VHDL ");
end package;
";

printf "generated vhdl $vhdl_filename origin: 0x%04x size: 0x%04x\n", $origin, $rom_size;
if ($bin_filename) {
    print "generated binary file $bin_filename\n";
}
