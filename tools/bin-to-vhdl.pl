#!/bin/perl -w

use strict;
use Getopt::Std;

my %opt;

getopts('s:n', \%opt);

my $bin_filename = shift @ARGV;
my $rom_name = ($opt{n} or "ROM");

sub usage {
    die "usage: $0 [-s <size>] <input>.bin\n";
}

usage() unless ($bin_filename);

if ($bin_filename !~ /(.*)\.bin$/) {
    print STDERR "$0: Bad file suffix\n";
    usage();
}
my $vhdl_filename = "$1.vhd";

open(BIN, $bin_filename) or die "$0: can't open input file $bin_filename: $!\n";
open(VHDL, ">$vhdl_filename") or die "$0: can't open vhdl output file $vhdl_filename for writing: $!\n";

my $end = 0;

my $ROM;
my $length = read(BIN, $ROM, 10000000);

my $rom_size = ($opt{s} or $length);

die "empty rom" unless ($rom_size);

print VHDL "
-- Automatically generated ROM initialization definitions for System09
-- Converted from binary file $bin_filename
-- DO NOT EDIT!

library ieee;

use ieee.std_logic_1164.all;
use ieee.numeric_std.all;

package ${rom_name}_defs is

constant ${rom_name}_size : integer := $rom_size;
type ${rom_name}_type is array (0 to (${rom_name}_size - 1)) of std_logic_vector (7 downto 0);
constant ${rom_name}_init : ${rom_name}_type := (
    ";
for (my $i = 0; $i < length($ROM); $i++) {
    printf VHDL "X\"%02X\"", ord(substr($ROM, $i));
    if ($i != (length($ROM) - 1)) {
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

printf "generated vhdl $vhdl_filename size: 0x%04x\n", $rom_size;
