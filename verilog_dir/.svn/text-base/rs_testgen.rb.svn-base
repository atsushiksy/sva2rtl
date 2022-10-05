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
  integer match_count ;
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
    match_count = 0 ;
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

def set_expect( t0, t1, txt )
  check = "      match_count = 0 ;\n" ;
    if( $exp_array[$t_count+t0] == nil ) 
    $exp_array[$t_count+t0] = check
  else
    $exp_array[$t_count+t0] = $exp_array[$t_count+t0] + check
  end
  0.upto(t1) { |t|
    check = "      if( " + txt +  " ) begin\n" 
    check += "        match_count = match_count + 1 ;\n" 
    check += "        $display( \"%0d Expeced match\", cycle_count ) ;\n"
    check += "        if( match_count > 1 ) begin\n"
    check += "          $display( \"%0d Error! more than one match\", cycle_count ) ;\n"
    check += "        end\n"
    check += "     end\n"
    if t == t1
      check += "     else begin\n"
      check += "       if( match_count == 0 ) begin\n"
      check += "          $display( \"%0d Error! expect failed\", cycle_count ) ;\n"
      check += "        end\n"
      check += "     end\n"
    end

    if( $exp_array[$t_count+t0+t] == nil ) 
      $exp_array[$t_count+t0+t] = check
    else
      $exp_array[$t_count+t0+t] = $exp_array[$t_count+t0+t] + check
    end
  }
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

def gen_test1( d0, d1, d2, d3 )
  # case of exp0 ##1 (exp1 ##d0 exp2) [*d1] |-> ( exp3 ##d2 exp4 )[*d3]  
  test_init
  #pass case
  set_trigger( 0, "exp0" ) 
  1.upto(d1) {
    set_trigger( 1, "exp1" ) 
    set_trigger( 1+d0, "exp2" ) 
    $t_count += 1 + d0
  }
  $t_count += $nov 
  1.upto(d3) {
    set_trigger( 0, "exp3" )
    set_trigger( d2, "exp4" )
    $t_count += d2 + 1 ;
  }
  set_expect( 1, 2 , "!err && mtch && !ovwp" )

  $t_count += 3 

  #error on 2nd sequence
  1.upto(d3) { |t0|
    set_trigger( 0, "exp0" ) 
    1.upto(d1) {
      set_trigger( 1, "exp1" ) 
      set_trigger( 1+d0, "exp2" ) 
      $t_count += 1 + d0
    }
    $t_count += $nov 
    if t0 > 1
      1.upto(t0-1) {
        set_trigger( 0, "exp3" )
        set_trigger( d2, "exp4" )
        $t_count += d2 + 1 ;
      }
    end
    set_expect( 1, 4 , "err && !mtch && !ovwp" )  
    $t_count += 5 
  }

  $final_count_init = "  final_count = #{$t_count} ;\n"

end

# continuous repetition test
# case of exp0 ##1 (exp1 ##d0 exp2) [*d1] |-> ( exp3 ##d2 exp4 )[*d3]  
set_verilog_exp(5)
1.upto(5) do  |d0|
1.upto(5) do  |d1|
1.upto(5) do  |d2|
1.upto(5) do  |d3|

$test = sprintf( "exp0 ##1 (exp1 ##%d exp2) [*%d] |-> ( exp3 ##%d exp4 )[*%d]", d0, d1, d2, d3 )
$nov = 0 
gen_test1( d0, d1, d2, d3 )
fname = sprintf(  "exp_1_seqR_2_seqR_%d_%d_%d_%d", d0, d1, d2, d3 )
gen_test_file( fname )
$test = sprintf( "exp0 ##1 (exp1 ##%d exp2) [*%d] |=> ( exp3 ##%d exp4 )[*%d]", d0, d1, d2, d3 )
$nov = 1
gen_test1( d0, d1, d2, d3 )
fname = sprintf(  "exp_1_seqR_3_seqR_%d_%d_%d_%d", d0, d1, d2, d3 )
gen_test_file( fname )

end
end
end
end

