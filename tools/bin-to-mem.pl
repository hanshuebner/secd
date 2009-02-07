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
my $mem_filename = "$1.mem";

open(BIN, $bin_filename) or die "$0: can't open input file $bin_filename: $!\n";
open(MEM, ">$mem_filename") or die "$0: can't open mem output file $mem_filename for writing: $!\n";

my $end = 0;

my $ROM;
my $length = read(BIN, $ROM, 10000000);

my $rom_size = ($opt{s} or $length);

die "empty rom" unless ($rom_size);

print MEM "\@C000 ";
for (my $page = 0; $page < 8; $page++) {
    for (my $row = 0; $row < 0x40; $row++) {
        for (my $byte = 0; $byte < 32; $byte++) {
            printf MEM "%02x ", ord(substr($ROM, $page * 2048 + $row * 32 + $byte));
        }
        printf MEM "\n";
    }
}
printf "generated mem $mem_filename size: 0x%04x\n", $rom_size;
