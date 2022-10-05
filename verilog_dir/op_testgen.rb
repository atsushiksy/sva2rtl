#!/usr/bin/ruby

require 'erb'

$template = ERB.new <<-EOF
module asv_module ( Clk<%= $verilog_arg %> ) ;
  input Clk ;
<%= $verilog_io %>
  
  check: assert property ( @(posedge Clk)  <%= $test_code %> ) ;
  
endmodule

module test_module ;

  reg clock, reset_, clear, enable ;
  reg <%= $test_exprs %> ;
  integer cycle_count ;
  integer final_count ;
  wire err, mtch, ovwp ;

  asv_module dut ( 
    .Clk(clock)<%= $exprs_connections %>,
    .ARV_resetN(reset_), 
    .ARV_clear(clear), 
    .ARV_enable(enable),
    .ARV_error(err),
    .ARV_match(mtch),
    .ARV_overwrap(ovwp)
  ) ;

  initial begin
    clock = 0 ;
    reset_ = 0 ;
    clear = 1 ;
    enable = 0 ;
    cycle_count = 0 ;
<%= $test_exprs_init %>
<%= $final_count_init %>
  end
  
  
  always begin
    #5 clock = !clock ;
  end
  
  always @(negedge clock) begin
    case ( cycle_count )
    0: begin
      reset_ = 0 ;
      clear = 1 ;
      enable = 0 ;
    end
    1: begin
      reset_ = 1 ;
      clear = 1 ;
      enable = 0 ;
    end
    2: begin
      reset_ = 1 ;
      clear = 0 ;
      enable = 0 ;
    end
    3: begin
      reset_ = 1 ;
      clear = 0 ;
      enable = 1 ;
    end
<%= $test_sequences %>
    default: begin
      if( cycle_count >= final_count ) $finish ;
    end
    endcase
  end
  
  always @(posedge clock) begin
    cycle_count = cycle_count + 1 ;
    case ( cycle_count )
<%= $test_expects %>
    default: begin
      if( err || mtch || ovwp ) begin
        $display( \"%0d Error! unexpected default responce\", cycle_count ) ;
      end
    end

    endcase
    
<%= $test_display %>
      
  end
  
endmodule

EOF

def set_verilog_exp( num )
  $verilog_arg = ""
  $verilog_io = "" 
  $test_exprs = ""
  $exprs_connections = "" 
  $test_exprs_init = ""
  $test_display = "  $display( \"%3d r:%b c:%b e:%b " 

  num.times { |i|
    $verilog_arg += ", exp#{i}"
    $verilog_io += "  input exp#{i} ;\n"
    if $test_exprs == "" 
      $test_exprs += "exp#{i}" 
    else 
      $test_exprs += ", exp#{i}"
    end
    $exprs_connections += ", .exp#{i}( exp#{i} )" 
    $test_exprs_init += "    exp#{i} = 0 ;\n"
    $test_display += " exp#{i}:%b"
  }
  $test_display += " err:%b match:%b overwrap:%b"

  $test_display += "\", cycle_count, reset_, clear, enable" ;
  num.times { |i|
    $test_display += ", exp#{i}"
  }
  $test_display += ", err, mtch, ovwp"
  $test_display += ") ;\n"

end

def set_seq ( t, txt ) 
  if( $time_array[$t_count+t] == nil )
    $time_array[$t_count+t] = txt
  else
    $time_array[$t_count+t] = $time_array[$t_count+t] + txt
  end
end

def set_exp ( t, txt )
  if( $exp_array[$t_count+t] == nil ) 
    $exp_array[$t_count+t] = txt
  else
    $exp_array[$t_count+t] = $exp_array[$t_count+t] + txt
  end
end

def gen_test_file (fname)
  $test_sequence = ""
  1.upto($t_count) do |tm|
    if( $time_array[tm] != nil )
      $test_sequences += "    #{tm}: begin\n"
      $test_sequences += $time_array[tm]
      $test_sequences += "    end\n"
    end
    if( $exp_array[tm] != nil )
      $test_expects += "    #{tm}: begin\n"
      $test_expects += $exp_array[tm]
      $test_expects += "    end\n"
    end
  end
  test_erb = ERB.new $test 
  $test_code = test_erb.result(binding)

  File.open( fname+".sv", 'w' ) { |f|
   f.puts $template.result(binding)
  }      
end

def test_init
  $time_array = Array.new
  $exp_array = Array.new
  $t_count = 4 ;
  $test_sequences = ""
  $test_expects = "" 
  $final_count_init = ""
end

def gen_exp_or_exp_then_exp
  # case of exp or exp |-> exp
  test_init

  set_seq( 0,                "      exp0 = 1 ;\n" )
  set_seq( 1,                "      exp0 = 0 ;\n" )
  set_seq( $nov,                "      exp2 = 1 ;\n" )
  set_seq( $nov+1,                "      exp2 = 0 ;\n" )
  set_exp( $nov+2,   "      if( err || !mtch || ovwp ) $display( \"%0d Error! unexpected responce\", cycle_count ) ;\n" )
  $t_count += 3+$nov

  set_seq( 0,                "      exp1 = 1 ;\n" )
  set_seq( 1,                "      exp1 = 0 ;\n" )
  set_seq( $nov,                "      exp2 = 1 ;\n" )
  set_seq( $nov+1,                "      exp2 = 0 ;\n" )
  set_exp( $nov+2,   "      if( err || !mtch || ovwp ) $display( \"%0d Error! unexpected responce\", cycle_count ) ;\n" )
  $t_count += 3+$nov
  
  set_seq( 0,                "      exp0 = 1 ;\n" )
  set_seq( 1,                "      exp0 = 0 ;\n" )
  set_seq( 0,                "      exp1 = 1 ;\n" )
  set_seq( 1,                "      exp1 = 0 ;\n" )
  set_seq( $nov,                "      exp2 = 1 ;\n" )
  set_seq( $nov+1,                "      exp2 = 0 ;\n" )
  set_exp( $nov+2,   "      if( err || !mtch || ovwp ) $display( \"%0d Error! unexpected responce\", cycle_count ) ;\n" )
  $t_count += 3+$nov

  set_seq( 0,                "      exp0 = 1 ;\n" )
  set_seq( 1,                "      exp0 = 0 ;\n" )
  set_exp( $nov+3,   "      if( !err || mtch || ovwp ) $display( \"%0d Error! unexpected responce\", cycle_count ) ;\n" )
  $t_count += $nov + 4

  set_seq( 0,                "      exp1 = 1 ;\n" )
  set_seq( 1,                "      exp1 = 0 ;\n" )
  set_exp( $nov+3,   "      if( !err || mtch || ovwp ) $display( \"%0d Error! unexpected responce\", cycle_count ) ;\n" )
  $t_count += $nov + 4

  $final_count_init = "  final_count = #{$t_count} ;\n"

end

# case of exp or exp |-> exp
set_verilog_exp(3)
$test = " exp0 or exp1 |-> exp2 "
$nov = 0 
gen_exp_or_exp_then_exp
gen_test_file( "expORexp2exp" )
$test = " exp0 or exp1 |=> exp2 "
$nov = 1
gen_exp_or_exp_then_exp
gen_test_file( "expORexp3exp" )


def gen_exp_and_exp_then_exp
  # case of first_match( exp and exp ) |-> exp
  test_init
  # 
  set_seq( 0,                "      exp0 = 1 ;\n" )
  set_seq( 1,                "      exp0 = 0 ;\n" )
  set_seq( 2,                "      exp0 = 1 ;\n" )
  set_seq( 3,                "      exp0 = 0 ;\n" )
  set_seq( 4,                "      exp1 = 1 ;\n" )
  set_seq( 5,                "      exp1 = 0 ;\n" )
  set_seq( 4+$nov,           "      exp2 = 1 ;\n" )
  set_seq( 5+$nov,           "      exp2 = 0 ;\n" )
  set_exp( 4+$nov+2,   "      if( err || !mtch || ovwp ) $display( \"%0d Error! unexpected responce\", cycle_count ) ;\n" )
  $t_count += 6+$nov
  set_seq( 1,                "      exp0 = 1 ;\n" )
  set_seq( 2,                "      exp0 = 0 ;\n" )
  set_seq( 1+$nov,           "      exp2 = 1 ;\n" )
  set_seq( 2+$nov,           "      exp2 = 0 ;\n" )
  set_exp( 1+$nov+2,   "      if( err || !mtch || ovwp ) $display( \"%0d Error! unexpected responce\", cycle_count ) ;\n" )
  $t_count += 5+$nov
  set_seq( 1,                "      exp1 = 1 ;\n" )
  set_seq( 2,                "      exp1 = 0 ;\n" )
  set_seq( 1+$nov,           "      exp2 = 1 ;\n" )
  set_seq( 2+$nov,           "      exp2 = 0 ;\n" )
  set_exp( 1+$nov+2,   "      if( err || !mtch || ovwp ) $display( \"%0d Error! unexpected responce\", cycle_count ) ;\n" )
  $t_count += 5+$nov
  # error case
  set_seq( 1,                "      exp0 = 1 ;\n" )
  set_seq( 2,                "      exp0 = 0 ;\n" )
  set_exp( $nov+1+3,   "      if( !err || mtch || ovwp ) $display( \"%0d Error! unexpected responce\", cycle_count ) ;\n" )
  $t_count += 5+$nov
  set_seq( 1,                "      exp1 = 1 ;\n" )
  set_seq( 2,                "      exp1 = 0 ;\n" )
  set_exp( $nov+1+3,   "      if( !err || mtch || ovwp ) $display( \"%0d Error! unexpected responce\", cycle_count ) ;\n" )
  $t_count += 5+$nov

  # clear
  set_seq( 0,                "      clear = 1 ;\n" )
  set_seq( 1,                "      clear = 0 ;\n" )
  $t_count += 2

  set_seq( 0,                "      exp1 = 1 ;\n" )
  set_seq( 1,                "      exp1 = 0 ;\n" )
  set_seq( 2,                "      exp1 = 1 ;\n" )
  set_seq( 3,                "      exp1 = 0 ;\n" )
  set_seq( 4,                "      exp0 = 1 ;\n" )
  set_seq( 5,                "      exp0 = 0 ;\n" )
  set_seq( 4+$nov,           "      exp2 = 1 ;\n" )
  set_seq( 5+$nov,           "      exp2 = 0 ;\n" )
  set_exp( 4+$nov+2,   "      if( err || !mtch || ovwp ) $display( \"%0d Error! unexpected responce\", cycle_count ) ;\n" )
  $t_count += 6+$nov
  set_seq( 1,                "      exp0 = 1 ;\n" )
  set_seq( 2,                "      exp0 = 0 ;\n" )
  set_seq( 1+$nov,           "      exp2 = 1 ;\n" )
  set_seq( 2+$nov,           "      exp2 = 0 ;\n" )
  set_exp( 1+$nov+2,   "      if( err || !mtch || ovwp ) $display( \"%0d Error! unexpected responce\", cycle_count ) ;\n" )
  $t_count += 5+$nov
  set_seq( 1,                "      exp1 = 1 ;\n" )
  set_seq( 2,                "      exp1 = 0 ;\n" )
  set_seq( 1+$nov,           "      exp2 = 1 ;\n" )
  set_seq( 2+$nov,           "      exp2 = 0 ;\n" )
  set_exp( 1+$nov+2,   "      if( err || !mtch || ovwp ) $display( \"%0d Error! unexpected responce\", cycle_count ) ;\n" )
  $t_count += 5+$nov
  # error case
  set_seq( 1,                "      exp0 = 1 ;\n" )
  set_seq( 2,                "      exp0 = 0 ;\n" )
  set_exp( $nov+1+3,   "      if( !err || mtch || ovwp ) $display( \"%0d Error! unexpected responce\", cycle_count ) ;\n" )
  $t_count += 5+$nov
  set_seq( 1,                "      exp1 = 1 ;\n" )
  set_seq( 2,                "      exp1 = 0 ;\n" )
  set_exp( $nov+1+3,   "      if( !err || mtch || ovwp ) $display( \"%0d Error! unexpected responce\", cycle_count ) ;\n" )
  $t_count += 5+$nov

  $final_count_init = "  final_count = #{$t_count} ;\n"

end


# case of exp and exp |-> exp
set_verilog_exp(3)
$test = "  exp0 and exp1  |-> exp2 "
$nov = 0
# gen_exp_and_exp_then_exp
# gen_test_file( "expANDexp2exp" )
$test = "  exp0 and exp1  |=> exp2 "
$nov = 1
# gen_exp_and_exp_then_exp
# gen_test_file( "expANDexp3exp" )

def gen_fm_exp_and_exp_mf_then_exp
  # case of first_match( exp and exp ) |-> exp
  test_init

  set_seq( 0,                "      exp0 = 1 ;\n" )
  set_seq( 1,                "      exp0 = 0 ;\n" )
  set_seq( 2,                "      exp0 = 1 ;\n" )
  set_seq( 3,                "      exp0 = 0 ;\n" )
  set_seq( 4,                "      exp1 = 1 ;\n" )
  set_seq( 5,                "      exp1 = 0 ;\n" )
  set_seq( 4+$nov,           "      exp2 = 1 ;\n" )
  set_seq( 5+$nov,           "      exp2 = 0 ;\n" )
  set_exp( 4+$nov+2,   "      if( err || !mtch || ovwp ) $display( \"%0d Error! unexpected responce\", cycle_count ) ;\n" )
  $t_count += 6+$nov

  # check first match clear
  set_seq( 1,                "      exp0 = 1 ;\n" )
  set_seq( 2,                "      exp0 = 0 ;\n" )
  set_seq( 1+$nov,           "      exp2 = 1 ;\n" )
  set_seq( 2+$nov,           "      exp2 = 0 ;\n" )

  set_seq( 4,                "      exp1 = 1 ;\n" )
  set_seq( 5,                "      exp1 = 0 ;\n" )
  set_seq( 4+$nov,           "      exp2 = 1 ;\n" )
  set_seq( 5+$nov,           "      exp2 = 0 ;\n" )
  set_exp( 4+$nov+2,   "      if( err || !mtch || ovwp ) $display( \"%0d Error! unexpected responce\", cycle_count ) ;\n" )
  $t_count += 6+$nov

  set_seq( 1,                "      exp1 = 1 ;\n" )
  set_seq( 2,                "      exp1 = 0 ;\n" )
  set_seq( 1+$nov,           "      exp2 = 1 ;\n" )
  set_seq( 2+$nov,           "      exp2 = 0 ;\n" )

  set_seq( 4,                "      exp0 = 1 ;\n" )
  set_seq( 5,                "      exp0 = 0 ;\n" )
  set_seq( 4+$nov,           "      exp2 = 1 ;\n" )
  set_seq( 5+$nov,           "      exp2 = 0 ;\n" )
  set_exp( 4+$nov+2,   "      if( err || !mtch || ovwp ) $display( \"%0d Error! unexpected responce\", cycle_count ) ;\n" )
  $t_count += 6+$nov

  # error case
  set_seq( 0,                "      exp0 = 1 ;\n" )
  set_seq( 1,                "      exp0 = 0 ;\n" )
  set_seq( 4,                "      exp1 = 1 ;\n" )
  set_seq( 5,                "      exp1 = 0 ;\n" )
  set_exp( $nov+4+3,   "      if( !err || mtch || ovwp ) $display( \"%0d Error! unexpected responce\", cycle_count ) ;\n" )
  $t_count += 5+$nov

  set_seq( 0,                "      exp1 = 1 ;\n" )
  set_seq( 1,                "      exp1 = 0 ;\n" )
  set_seq( 4,                "      exp0 = 1 ;\n" )
  set_seq( 5,                "      exp0 = 0 ;\n" )
  set_exp( $nov+4+3,   "      if( !err || mtch || ovwp ) $display( \"%0d Error! unexpected responce\", cycle_count ) ;\n" )
  $t_count += 5+$nov

  $final_count_init = "  final_count = #{$t_count} ;\n"

end

# case of first_match( exp and exp ) |-> exp
set_verilog_exp(3)
$test = " first_match( exp0 and exp1 ) |-> exp2 "
$nov = 0
# gen_fm_exp_and_exp_mf_then_exp
# gen_test_file( "fm_expANDexp_mf2exp" )
$test = " first_match( exp0 and exp1 ) |=> exp2 "
$nov = 1
# gen_fm_exp_and_exp_mf_then_exp
# gen_test_file( "fm_expANDexp_mf3exp" )

def gen_expINTexp2exp
  # case of exp intersect exp|-> exp
  test_init

  # no responce
  set_seq( 0,                "      exp0 = 1 ;\n" )
  set_seq( 1,                "      exp0 = 0 ;\n" )
  set_seq( 1,                "      exp1 = 1 ;\n" )
  set_seq( 2,                "      exp1 = 0 ;\n" )
  $t_count += 2
  
  set_seq( 0,                "      exp0 = 1 ;\n" )
  set_seq( 1,                "      exp0 = 0 ;\n" )
  set_seq( 0,                "      exp1 = 1 ;\n" )
  set_seq( 1,                "      exp1 = 0 ;\n" )
  set_seq( $nov,                "      exp2 = 1 ;\n" )
  set_seq( $nov+1,                "      exp2 = 0 ;\n" )
  set_exp( $nov+2,   "      if( err || !mtch || ovwp ) $display( \"%0d Error! unexpected responce\", cycle_count ) ;\n" )
  $t_count += $nov+3

  # no responce
  set_seq( 0,                "      exp1 = 1 ;\n" )
  set_seq( 1,                "      exp1 = 0 ;\n" )
  set_seq( 1,                "      exp0 = 1 ;\n" )
  set_seq( 2,                "      exp0 = 0 ;\n" )
  $t_count += 2
  
  set_seq( 0,                "      exp0 = 1 ;\n" )
  set_seq( 1,                "      exp0 = 0 ;\n" )
  set_seq( 0,                "      exp1 = 1 ;\n" )
  set_seq( 1,                "      exp1 = 0 ;\n" )
  set_seq( $nov,                "      exp2 = 1 ;\n" )
  set_seq( $nov+1,                "      exp2 = 0 ;\n" )
  set_exp( $nov+2,   "      if( err || !mtch || ovwp ) $display( \"%0d Error! unexpected responce\", cycle_count ) ;\n" )
  $t_count += $nov+3

  #error case
  set_seq( 0,                "      exp0 = 1 ;\n" )
  set_seq( 1,                "      exp0 = 0 ;\n" )
  set_seq( 0,                "      exp1 = 1 ;\n" )
  set_seq( 1,                "      exp1 = 0 ;\n" )
  set_exp( $nov+3,   "      if( !err || mtch || ovwp ) $display( \"%0d Error! unexpected responce\", cycle_count ) ;\n" )
  $t_count += $nov+5

  $final_count_init = "  final_count = #{$t_count} ;\n"

end

# case of exp intersect exp |-> exp
set_verilog_exp(3)
$test = " exp0 intersect exp1 |-> exp2 "
$nov = 0
gen_expINTexp2exp
gen_test_file( "expINTexp2exp" )
$test = " exp0 intersect exp1 |=> exp2 "
$nov = 1
gen_expINTexp2exp
gen_test_file( "expINTexp3exp" )

def exp2expTHRexpDexp( dly )
  # case of exp |-> exp throughout ( exp # exp )
  test_init

  set_seq( 0,                "      exp0 = 1 ;\n" )
  set_seq( 1,                "      exp0 = 0 ;\n" )
  set_seq( 0,                "      exp1 = 1 ;\n" )
  set_seq( 0,                "      exp2 = 1 ;\n" )
  set_seq( 1,                "      exp2 = 0 ;\n" )
  set_seq( dly,              "      exp3 = 1 ;\n" )  
  set_seq( dly+1,            "      exp3 = 0 ;\n" )  
  set_seq( dly+1,            "      exp1 = 0 ;\n" )
  set_exp( dly+2,   "      if( err || !mtch || ovwp ) $display( \"%0d Error! unexpected responce\", cycle_count ) ;\n" )
  $t_count += dly+3

  # exp1 error
  set_seq( 0,                "      exp0 = 1 ;\n" )
  set_seq( 1,                "      exp0 = 0 ;\n" )
  set_seq( 0,                "      exp2 = 1 ;\n" )
  set_seq( 1,                "      exp2 = 0 ;\n" )
  set_exp( 4,   "      if( !err || mtch || ovwp ) $display( \"%0d Error! unexpected responce\", cycle_count ) ;\n" )
  $t_count += 5

  if( dly > 3 )
    2.upto(dly-1) { |t0|
      set_seq( 0,                "      exp0 = 1 ;\n" )
      set_seq( 1,                "      exp0 = 0 ;\n" )
      set_seq( 0,                "      exp1 = 1 ;\n" )
      set_seq( t0,               "      exp1 = 0 ;\n" )
      set_seq( 0,                "      exp2 = 1 ;\n" )
      set_seq( 1,                "      exp2 = 0 ;\n" )
      set_seq( dly,              "      exp3 = 1 ;\n" )  
      set_seq( dly+1,            "      exp3 = 0 ;\n" )  
      set_exp( t0+3,   "      if( !err || mtch || ovwp ) $display( \"%0d Error! unexpected responce\", cycle_count ) ;\n" )
      $t_count += dly+5
    } 
  end

  # exp2 error
  set_seq( 0,                "      exp0 = 1 ;\n" )
  set_seq( 1,                "      exp0 = 0 ;\n" )
  set_seq( 0,                "      exp1 = 1 ;\n" )
  set_seq( dly,              "      exp1 = 0 ;\n" )
  set_exp( 4,   "      if( !err || mtch || ovwp ) $display( \"%0d Error! unexpected responce\", cycle_count ) ;\n" )
  $t_count += dly + 5

  # exp3 error
  set_seq( 0,                "      exp0 = 1 ;\n" )
  set_seq( 1,                "      exp0 = 0 ;\n" )
  set_seq( 0,                "      exp1 = 1 ;\n" )
  set_seq( 0,                "      exp2 = 1 ;\n" )
  set_seq( 1,                "      exp2 = 0 ;\n" )
  set_seq( dly+1,            "      exp1 = 0 ;\n" )
  set_exp( dly+4,   "      if( !err || mtch || ovwp ) $display( \"%0d Error! unexpected responce\", cycle_count ) ;\n" )
  $t_count += dly +7

  $final_count_init = "  final_count = #{$t_count} ;\n"

end

# case of exp |-> exp throughout ( exp # exp )
set_verilog_exp(4)
1.upto(5) { |d0|
  $test = sprintf( " exp0 |-> exp1 throughout ( exp2 ##%d exp3 ) ", d0 )
  $nov = 0
  exp2expTHRexpDexp( d0 )
  gen_test_file( "exp2expTHRexpDexp"+sprintf( "%d", d0 ) )
}



