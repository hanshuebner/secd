#!/bin/perl -- -*- Perl -*-

use Aldec::ActiveHDL;

my $prefix = "UUT";
my $ram = Examine("$prefix/my_secd_ram/RAM", 16);
my @RAM = map { hex $_ } split(/,/, $ram);
my $free = hex(Examine("$prefix/my_datapath/free", 16));

sub print_decode {
    my $value = shift;

    print " ";
    print (($value & 0x80000000) ? "F" : " ");
    print (($value & 0x40000000) ? "M" : " ");
    print " ";
    my $type = ($value & 0x30000000) >> 28;
    if ($type == 3) {
        printf "I %11d", $value & 0xFFFFFFF;
    } elsif ($type == 2) {
        printf "S %11d", $value & 0xFFFFFFF;
    } elsif ($type == 0) {
        printf "C %5d %5d", ($value & 0xFFFC000) >> 14, ($value & 0x3FFF);
    } else {
        printf "? 0x%08x", $value;
    }
    print "\n";
}


my $filename = "c:/cygwin/tmp/secd-mem.txt";
print "Dumping memory to file $filename\n";
open(OUT, ">$filename") || die $?;
select(OUT);

my $register;
foreach $register (qw/s e c d x1 x2/) {
    my $pointer = hex(Examine("$prefix/my_datapath/$register", 16));
    $count = 0;
    print "$register: $pointer\n";
}

my $i;
for ($i = 0; $i < 16384; $i++) {
    printf "%05d", $i;
    print_decode($RAM[$i]);
}
close(OUT);
select(STDOUT);
print "Done\n";
exit;

