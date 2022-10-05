#! /usr/bin/perl
#
#  parse yacc pre file and produce various header files.
#
#  Author: Atsushi Kasuya
#
#   Copyright (C) 2011 Atsushi Kasuya


$srcfile = "SystemVerilog.l.pp";

{

  open(TMP, $srcfile) or die "Can't open $srcfile \n" ;
  while(<TMP>) {
    chop ;
    $line = $_ ;
    if( $line =~ /^\s*#\s*INCLUDE\s*\"(\S+)\"\s*$/ ) {
      $incfile = $1 ;
      #printf stderr "#INCLUDE $incfile\n" ;
      open INC, $incfile or
        die "Can't open $incfile\n" ;
       while( <INC> ) {
        print $_ ;
      }
      close INC ;
    }
    else {
      print "$line\n";
    }
  }
}
