#! /usr/bin/perl
#
#  gen_action.pl  < SystemVerilog.y.prep > SystemVerilog.y
#
#  Copyright (C) 2011 Atsushi Kasuya
#
#

open KEY, "SV_keywords.data" or die "Can't open jeda_keyword.data\n" ;

while( <KEY> ) {
  if( /^\s*(\S+)\s+(\S+)/ ) {
    $keyword = $1 ;
    $token = $2 ;
    #printf stderr "Keyword: $keyword token: $token\n" ;
    $keyword_tbl{$keyword} = $token ;
  }
}

open ASF, "SV_parser_action.data" 
  or die "Can't open jeda_parser_action.data\n" ;
  

while( <ASF> ) {
  $line = $_ ;
  #print stderr "L:$line" ;
  if( $line =~ /^\s*#/ ) {
    # comment line
  }
  elsif( $line =~ /^\<\<(\w+)\>\>/ ) {
    $block = $1 ;
    $loop = 1 ;
    while($loop) {
      $line  = <ASF> ;
      if( $line =~ /^\s*\<\<(\w+)\>\>/ ) {
        $action{$block} .= $action{$1} ;
      }
      else {
        $action{$block} .= "  ".$line ;
      }
      if( $line =~ /^\}/ ) {
        $loop = 0 ;
      }
      # print stderr $line ;
    }
    #print stderr "$block defined\n" ;
  }
}

close ASF ;

# print stderr "action data parse completed\n" ;

while( <> ) {
  $line = $_ ;
  if( $line =~ /^\s*\/\// ) {
    # comment line
    print "\n" ;
  }
  elsif( $line =~ /^s*\#BEGIN/ || $line =~ /^*\#END/ ) {
    # BEGIN END comment
    print "\n" ;
  }
  elsif( $line =~ /^\s*#\s*INCLUDE\s*\"(\S+)\"\s*$/ ) {
    $incfile = $1 ;
    #printf stderr "#INCLUDE $incfile\n" ;
    open INC, $incfile or
      die "Can't open $incfile\n" ;
    while( <INC> ) {
      print $_ ;
    }
    close INC ;
  }
  elsif( $line =~ /^\s*\<\<(\w+)\>\>/ ) {
    $block = $1 ;
    $act = $action{$block} ;
    if( $act eq "" ) {
      print stderr "Undefined action $block detected\n" ;
    }
    else {
       print $act ;
    }
  }
  else {
    $R = $line ;
    while( $R =~ /\'(\S+)\'/ ) {
      $keyword = $1 ;
      # print stderr " got $keyword\n" ;
      $p = $` ;
      $R = $' ;
      print $p ;
      $token = $keyword_tbl{$keyword} ;
      if( $token ) {
        print "$token" ;
      }
      else {
        print "\'$keyword\'" ;
      }
    }
    print "$R" ;      
  }
}



 

