#!/bin/perl

package SECD;

use Aldec::ActiveHDL;

@ISA = qw/Exporter/;

@EXPORT = qw/@SECD_OPS @RAM @printed read_ram car cdr lit type print_as_sexp $prefix/;
    
my @SECD_OPS = qw(NIL LD LDC LDF AP RTN DUM RAP SEL JOIN CAR CDR ATOM
                  CONS EQ ADD SUB MUL DIV REM LEQ STOP);

my $prefix = "/UUT"; # (or /UUT?)
my @RAM;

my $count = 0;
my $limit = 40000;

my @printed;

sub read_ram {
    @RAM = map { hex $_ } split(/,/, Examine("$prefix/my_secd_ram/RAM", 16));
}

sub car {
    my $address = shift;

    return ($RAM[$address] & 0xFFFC000) >> 14;
}

sub cdr {
    my $address = shift;

    return $RAM[$address] & 0x3FFF;
}

sub lit {
    my $address = shift;

    return $RAM[$address] & 0xFFFFFFF;
}

sub type {
    my $address = shift;
    
    return ($RAM[$address] & 0x30000000) >> 28;
}

sub print_as_sexp {
    undef @printed;
    $count = 0;
    _print_as_sexp(@_);
}

sub _print_as_sexp {
    my $address = shift;
    my $in_list = shift;

    if ($address == 0) {
        print "NIL";
        return;
    }

    my $type = type($address);

    if ($type == 0 && $printed[$address]) {
        print "[C]";
        return;
    }
    $printed[$address] = 1;

    my $value = $RAM[$address];

    if ($count++ == $limit) {
        print "...";
    }
    if ($count >= $limit) {
        return;
    }

    if ($type == 3) {
        printf "%d", lit($address);
    } elsif ($type == 2) {
        my $symbol_number = lit($address);
        if ($symbol_number == 0) {
            print "NIL";
        } elsif ($symbol_number == 1) {
            print "T";
        } elsif ($symbol_number == 2) {
            print "F";
        } else {
            printf "S%d", $symbol_number;
        }
    } elsif ($type == 0) {
        if (!$in_list) {
            print "(";
        }
        _print_as_sexp(car($address));
        my $cdr = cdr($address);
        if ($cdr != 0 && $RAM[$cdr] != 0x20000000) {
            if (type($cdr) != 0) {
                # cdr not cons => dotted
                print " .";
            }
            print " ";
            _print_as_sexp($cdr, 1);
        }
        if (!$in_list) {
            print ")";
        }
    } else {
        printf "?0x%08x", $value;
    }
}

1;
