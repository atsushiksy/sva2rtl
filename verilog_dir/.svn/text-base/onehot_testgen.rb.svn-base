#!/usr/bin/ruby

require 'erb'

$template = ERB.new <<-EOF
module asv_module ( Clk<%= $verilog_arg %> ) ;
  input Clk ;
<%= $verilog_io %>
  
  property arged_prop( <%= $arg_code %> ) ;
    <%= $variable_code %> 
    @(posedge Clk)  <%= $test_code %> ;
  endproperty
  check: assert property ( 
    arged_prop( <%= $actarg_code %> ) 
  ) ;
  
endmodule

module test_module ;

  reg clock, reset_, clear, enable ;
  reg <%= $test_exprs %> ;
<%= $test_data_exprs %>
  integer cycle_count ;
  integer final_count ;
  integer error_count ;
  integer overwrap_count ;
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
    error_count = 0 ;
    overwrap_count = 0 ;
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

def set_verilog_exp( num, width )
  $verilog_arg = ""
  $verilog_io = "" 
  $test_exprs = ""
  $test_data_exprs = ""
  $exprs_connections = "" 
  $test_exprs_init = ""
  $test_display = "  $display( \"%3d r:%b c:%b e:%b " 
  $verilog_arg += ", data0, data1"
  $verilog_io += "  input [#{width-1}:0] data0 ;\n"
  $verilog_io += "  input [#{width-1}:0] data1 ;\n"
  $test_data_exprs += "  reg [#{width-1}:0] data0 ;\n"
  $test_data_exprs += "  reg [#{width-1}:0] data1 ;\n"
  $exprs_connections += ", .data0( data0 )" 
  $exprs_connections += ", .data1( data1 )" 
  $test_exprs_init += "    data0 = 0 ;\n"
  $test_exprs_init += "    data1 = 0 ;\n"
  $test_display += " data0:%b data1:%b"
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

  $test_display += "\", cycle_count, reset_, clear, enable, data0, data1" ;
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

def set_data( t, exp, width, bit, inv, d = 1 )
  if( inv > 0 ) 
    dt = sprintf( "%d'b",width )
   if( width-bit-2 ) 
      (width-bit-2).downto(0) do
        dt += "0" 
      end
    end
    dt += "1" ;
    if( bit > 0 )
      0.upto(bit-1) do
        dt += "0"
      end
    end
  else
    dt = sprintf( "%d'b",width )
   if( width-bit-2 ) 
      (width-bit-2).downto(0) do
        dt += "0" 
      end
    end
    dt += "0" ;
    if ( bit > 0 )
      0.upto(bit-1) do
        dt += "0"
      end
    end
  end

  txt = sprintf( "      %s = %s ;\n", exp, dt ) 
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

def set_edata( t, exp, width, bit, bit1, d = 1 )

  dt = sprintf( "%d'b",width )
  if( width-bit-2 ) 
    (width-bit-2).downto(0) do |x0|
      if( x0 == (width - bit1 - 1) )
        dt += "1"
      else
        dt += "0" 
      end
    end
  end
  dt += "1" ;
  if( bit > 0 )
    0.upto(bit-1) do
      dt += "0" 
    end
  end
  
  txt = sprintf( "      %s = %s ;\n", exp, dt ) 
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

def set_expect_error( t0, t1, txt )
  check = "      error_count = 0 ;\n" ;
    if( $exp_array[$t_count+t0] == nil ) 
    $exp_array[$t_count+t0] = check
  else
    $exp_array[$t_count+t0] = $exp_array[$t_count+t0] + check
  end
  0.upto(t1) { |t|
    check = "      if( " + txt +  " ) begin\n" 
    check += "        error_count = error_count + 1 ;\n" 
    check += "        $display( \"%0d Expeced err\", cycle_count ) ;\n"
    check += "        if( error_count > 1 ) begin\n"
    check += "          $display( \"%0d Error! more than one error\", cycle_count ) ;\n"
    check += "        end\n"
    check += "     end\n"
    if t == t1
      check += "     else begin\n"
      check += "       if( error_count == 0 ) begin\n"
      check += "          $display( \"%0d Error! expect error failed\", cycle_count ) ;\n"
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

def set_expect_overwrap( t0, t1, txt )
  check = "      overwrap_count = 0 ;\n" ;
    if( $exp_array[$t_count+t0] == nil ) 
    $exp_array[$t_count+t0] = check
  else
    $exp_array[$t_count+t0] = $exp_array[$t_count+t0] + check
  end
  0.upto(t1) { |t|
    check = "      if( " + txt +  " ) begin\n" 
    check += "        overwrap_count = overwrap_count + 1 ;\n" 
    check += "        $display( \"%0d Expeced overwrap\", cycle_count ) ;\n"
    check += "        if( overwrap_count > 1 ) begin\n"
    check += "          $display( \"%0d Error! more than one overwrap\", cycle_count ) ;\n"
    check += "        end\n"
    check += "     end\n"
    if t == t1
      check += "     else begin\n"
      check += "       if( overwrap_count == 0 ) begin\n"
      check += "          $display( \"%0d Error! expect overwrap failed\", cycle_count ) ;\n"
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

def gen_test1( t0 )
# case of  "exp0 |-> $onehot(data0) ##1 exp1 ##1 $onehot0(data1) "
 
  test_init
  
  #pass case  
  0.upto(t0-1) do |p0|
    set_trigger( 0, "exp0" ) 
    set_data( $nov, "data0", t0, p0, 1 )
    set_trigger( $nov+1, "exp1" ) 
    set_data( $nov+2, "data1", t0, p0, 0 )
    set_check( $nov+4, "err || !mtch || ovwp" ) 

    $t_count += $nov+8 ;
  end

  0.upto(t0-1) do |p0|
    set_trigger( 0, "exp0" ) 
    set_data( $nov, "data0", t0, p0, 1 )
    set_trigger( $nov+1, "exp1" ) 
    set_data( $nov+2, "data1", t0, p0, 1 )
    set_check( $nov+4, "err || !mtch || ovwp" ) 

    $t_count += $nov+8 ;
  end

  #error case 
  0.upto(t0-2) do |p0|
    (p0+1).upto(t0-1) do |p1|
      set_trigger( 0, "exp0" ) 
      set_data( $nov, "data0", t0, p0, 1 )
      set_trigger( $nov+1, "exp1" ) 
      set_edata( $nov+2, "data1", t0, p0, p1 )
      set_check( $nov+4, "!err || mtch || ovwp" ) 

      $t_count += $nov+8 ;
    end
  end

  0.upto(t0-1) do |p0|
    (p0+1).upto(t0-1) do |p1|
      set_trigger( 0, "exp0" ) 
      set_edata( $nov+2, "data0", t0, p0, p1 )
      set_trigger( $nov+1, "exp1" ) 
      set_data( $nov+2, "data1", t0, p0, 0 )
      set_check( $nov+2, "!err || mtch || ovwp" ) 

      $t_count += $nov+8 ;
    end
  end

  $final_count_init = "  final_count = #{$t_count} ;\n"

end

# ohehot test
# case of exp0 |-> $onehot(data0) ##1 exp1 ##1 $onehot0(data1)  

2.upto(31) do |t0|

  set_verilog_exp( 2, t0 )

  $actarg_code = ""
  $test =  "exp0 |-> $onehot(data0) ##1 exp1 ##1 $onehot0(data1) "
  $nov = 0 
  gen_test1( t0 )
  fname = sprintf(  "exp_2_onehot_D1_onehot0_%d", t0 )
  gen_test_file( fname )
  $test =  "exp0 |=> $onehot(data0) ##1 exp1 ##1 $onehot0(data1) "
  $nov = 1
  gen_test1( t0 )
  fname = sprintf(  "exp_3_onehot_D1_onehot0_%d", t0 )
  gen_test_file( fname )

end
