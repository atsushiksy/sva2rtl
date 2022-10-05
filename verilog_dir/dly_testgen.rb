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

def set_trigger( t, exp, d = 1 )
  txt = sprintf( "      %s = 1 ;\n", exp ) 
  if( $time_array[$t_count+t] == nil ) 
    $time_array[$t_count+t] = txt
  else
    $time_array[$t_count+t] = $time_array[$t_count+t] + txt
  end
  t += d
  txt = sprintf( "      %s = 0 ;\n", exp ) 
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

def set_check( t, txt )
  check = "      if( " + txt +  " ) $display( \"%0d Error! unexpected responce\", cycle_count ) ;\n"
    if( $exp_array[$t_count+t] == nil ) 
    $exp_array[$t_count+t] = check
  else
    $exp_array[$t_count+t] = $exp_array[$t_count+t] + check
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

def gen_exp_D01_exp_then_exp_d2_exp_d3_exp( d0, d1, d2, d3 )
  # case of exp0 ##[d0:d1] exp1 |-> exp2 ##d2 exp3 ##d3 exp4
  test_init

  #pass case
  d0.upto(d1) do | t0 |
    set_trigger( 0, "exp0" ) 
    set_trigger( t0, "exp1" )
    set_trigger( t0+$nov, "exp2" )
    set_trigger( t0+$nov+d2, "exp3" )
    set_trigger( t0+$nov+d2+d3, "exp4" )
    set_check( t0+$nov+d2+d3+2, "err || !mtch || ovwp" )
    $t_count += t0+d2+d3+$nov+3
  end
  
  #error on exp2
  d0.upto(d1) do | t0 |
    set_trigger( 0, "exp0" ) 
    set_trigger( t0, "exp1" )
    set_trigger( t0+$nov+d2, "exp3" )
    set_trigger( t0+$nov+d2+d3, "exp4" )
    set_check( t0+$nov+2, "!err || mtch || ovwp" )
    $t_count += t0+d2+d3+$nov+3
  end

  #error on exp3
  d0.upto(d1) do | t0 |
    set_trigger( 0, "exp0" ) 
    set_trigger( t0, "exp1" )
    set_trigger( t0+$nov, "exp2" )
    set_trigger( t0+$nov+d2+d3, "exp4" )
    set_check( t0+$nov+d2+2, "!err || mtch || ovwp" )
    $t_count += t0+d2+d3+$nov+3
  end

  #error on exp4
  d0.upto(d1) do | t0 |
    set_trigger( 0, "exp0" ) 
    set_trigger( t0, "exp1" )
    set_trigger( t0+$nov, "exp2" )
    set_trigger( t0+$nov+d2, "exp3" )
    set_check( t0+$nov+d2+d3+2, "!err || mtch || ovwp" )
    $t_count += t0+d2+d3+$nov+3
  end

  #first stage overwrap
  if d1 > 1 
    set_trigger( 0, "exp0", 2 ) 
    set_trigger( d1, "exp1", 2 )
    set_trigger( d1+$nov, "exp2", 2 )
    set_trigger( d1+$nov+d2, "exp3", 2 )
    set_trigger( d1+$nov+d2+d3, "exp4", 3 )
    set_check( d1+$nov+d2+d3+2, "err || !mtch || ovwp" )
    set_check( d1+$nov+d2+d3+3, "err || !mtch || ovwp" )
    $t_count += d1+d2+d3+$nov+3    
  end

  $final_count_init = "  final_count = #{$t_count} ;\n"

end

# case of exp0 ##[d0:d1] exp1 |-> exp2 ##d2 exp3 ##d3 exp4
set_verilog_exp(5)

1.upto(5) do  |d1|
1.upto(d1) do |d0|
1.upto(5) do  |d2|
1.upto(5) do  |d3|

$test = sprintf( "exp0 ##[%d:%d] exp1 |-> exp2 ##%d exp3 ##%d exp4 ", d0, d1, d2, d3 )
$nov = 0 
gen_exp_D01_exp_then_exp_d2_exp_d3_exp( d0, d1, d2, d3 )
fname = sprintf(  "expD01exp2expD2expD3exp_%d_%d_%d_%d", d0, d1, d2, d3 )
gen_test_file( fname )
$test = sprintf( "exp0 ##[%d:%d] exp1 |=> exp2 ##%d exp3 ##%d exp4 ", d0, d1, d2, d3 )
$nov = 1
gen_exp_D01_exp_then_exp_d2_exp_d3_exp( d0, d1, d2, d3 )
fname = sprintf(  "expD01exp3expD2expD3exp_%d_%d_%d_%d", d0, d1, d2, d3 )
gen_test_file( fname )

end
end
end
end 

