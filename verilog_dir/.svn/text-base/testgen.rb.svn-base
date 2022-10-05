#!/usr/bin/ruby

require 'erb'

template = ERB.new <<-EOF
module asv_module ( Clk<%= verilog_arg %> ) ;
  input Clk ;
<%= verilog_io %>
  
  check: assert property ( @(posedge Clk)  <%= $test_code %> ) ;
  
endmodule

module test_module ;

  reg clock, reset_, clear, enable ;
  reg <%= test_exprs %> ;
  integer cycle_count ;
  integer final_count ;
  wire err, mtch, ovwp ;

  asv_module dut ( 
    .Clk(clock)<%= exprs_connections %>,
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
<%= test_exprs_init %>
<%= final_count_init %>
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
<%= test_sequences %>
    default: begin
      if( cycle_count >= final_count ) $finish ;
    end
    endcase
  end
  
  always @(posedge clock) begin
    cycle_count = cycle_count + 1 ;
    case ( cycle_count )
<%= test_expects %>
    default: begin
      if( err || mtch || ovwp ) begin
        $display( \"%0d Error! unexpected default responce\", cycle_count ) ;
      end
    end

    endcase
    
<%= test_display %>
      
  end
  
endmodule

EOF

class Test_node
  def initialize( type, id ) 
    @type = type 
    @next_node = nil 
    @id = id
  end
  attr_accessor :type, :next_node, :id 

end

$top_node = nil 
$cur_node = nil 

testfile = ARGV[0] ;
outfilepref = testfile.split( /\./ )[0]

File.open(testfile) { |f|
  contents = f.read
  $testarray = contents.split( /\s+/ ) 
}
$exp = 0 
$delay = 0 
$range = 0 
$p_delay = 0 
$p_range = 0 
$nov = 0 
$and = 0 
$or = 0
$intersect = 0
$throughout = 0
$p_and = 0
$p_or = 0
$p_intersect = 0
$p_throughout = 0

def new_node( nd )
  if( $top_node == nil )
    $top_node = nd
    $cur_node = nd
  else
    $cur_node.next_node = nd
    $cur_node = nd  
  end
end 

$testarray.each { |x| 
  #print x + "\n"
  case x
  when "T:"
    $test = ""
  when "exp"
    $test += " exp#{$exp}" 
    new_node( Test_node.new( "exp", $exp ) )
    $exp += 1 
  when "|->"
    $test += " " + x
    new_node( Test_node.new( "c_imply", 0 ) )
    $p_delay = $delay
    $p_range = $range
    $p_and = $and
    $p_or = $or
    $p_intersect = $intersect
    $p_throughout = $throughout
    $nov = 0 
  when "|=>"
    $test += " " + x
    new_node( Test_node.new( "c_imply", 0 ) )
    $p_delay = $delay
    $p_range = $range
    $p_and = $and
    $p_intersect = $intersect
    $p_throughout = $throughout
    $p_or = $or
    $nov = 1 
  when "#"
    $test += " <%= $delay_#{$delay} %> " 
    new_node( Test_node.new( "delay", $delay ) )
    $delay += 1 ;
  when "#?"
    $test += " <%= $range_#{$range} %> " 
    new_node( Test_node.new( "range", $range ) )
    $range += 1 
  when "and"
    $test += " " + x + "  "
    $and += 1
  when "or"
    $test += " " + x + "  "
    $or += 1
  when "intersect"
    $test += " " + x + "  "
    $intersect += 1
  when "throughout"
    $test += " " + x + "  "
    $throughout += 1
  when "("
    $test += " " + x + " "
  when ")"
    $test += " " + x + " "
  else
    print "Unknown symbol #{x} \n"
  end
  
}

# print $test + "\n"
verilog_arg = ""
verilog_io = "" 
test_exprs = ""
exprs_connections = "" 
test_exprs_init = ""
test_display = "  $display( \"%3d r:%b c:%b e:%b " 

$exp.times { |i|
  verilog_arg += ", exp#{i}"
  verilog_io += "  input exp#{i} ;\n"
  if test_exprs == "" 
    test_exprs += "exp#{i}" 
  else 
    test_exprs += ", exp#{i}"
  end
  exprs_connections += ", .exp#{i}( exp#{i} )" 
  test_exprs_init += "    exp#{i} = 0 ;\n"
  test_display += " exp#{i}:%b"
}
test_display += " err:%b match:%b overwrap:%b"

test_display += "\", cycle_count, reset_, clear, enable" ;
$exp.times { |i|
  test_display += ", exp#{i}"
}
test_display += ", err, mtch, ovwp"
test_display += ") ;\n"

t_count = 4 ;
test_sequences = ""
test_expects = "" 
final_count_init = ""

$time_array = Array.new
$exp_array = Array.new

def set_seq ( t, txt ) 
  if( $time_array[t] == nil )
    $time_array[t] = txt
  else
    $time_array[t] = $time_array[t] + txt
  end
end

def set_exp ( t, txt )
  if( $exp_array[t] == nil ) 
    $exp_array[t] = txt
  else
    $exp_array[t] = $exp_array[t] + txt
  end
end

if ($delay == 0) && ($range == 0 )
  # case of exp |-> exp
  set_seq( t_count,                "      exp0 = 1 ;\n" )
  set_seq( t_count+$nov,           "      exp1 = 1 ;\n" )
  set_seq( t_count+1,              "      exp0 = 0 ;\n" )
  set_seq( t_count+$nov+1,         "      exp1 = 0 ;\n" )
  set_exp( t_count+$nov+2,   "      if( err || !mtch || ovwp ) $display( \"%0d Error! unexpected responce\", cycle_count ) ;\n" )
  t_count += $nov+2 
  # error case
  set_seq( t_count,                "      exp0 = 1 ;\n" )
  set_seq( t_count+1,              "      exp0 = 0 ;\n" )
  set_exp( t_count+$nov+3,   "      if( !err || mtch || ovwp ) $display( \"%0d Error! unexpected responce\", cycle_count ) ;\n" )
  t_count += $nov+4 
  final_count_init += "  final_count = #{t_count} ;\n"

  1.upto(t_count) do |tm|
    if( $time_array[tm] != nil )
      test_sequences += "    #{tm}: begin\n"
      test_sequences += $time_array[tm]
      test_sequences += "    end\n"
    end
    if( $exp_array[tm] != nil )
      test_expects += "    #{tm}: begin\n"
      test_expects += $exp_array[tm]
      test_expects += "    end\n"
    end
  end
  test_erb = ERB.new $test 
  $test_code = test_erb.result(binding)

  File.open( outfilepref+".sv", 'w' ) { |f|
   f.puts template.result(binding)
 }      
end

if ($delay == 2) && ($range == 0 )
  # case of exp # exp |-> exp # exp
  1.upto(5) do | d0 |
    $delay_0 = sprintf( "##%d", d0 )
    1.upto(5) do | d1 |
      $delay_1 = sprintf( "##%d", d1 )
      test_sequences = ""
      test_expects = "" 
      $time_array = Array.new
      $exp_array = Array.new
      t_count = 4 
      final_count_init = ""
      #match case 
      set_seq( t_count,           "      exp0 = 1 ;\n" )
      set_seq( t_count+1,         "      exp0 = 0 ;\n" )
      set_seq( t_count+d0,        "      exp1 = 1 ;\n" )
      set_seq( t_count+d0+$nov,        "      exp2 = 1 ;\n" )
      set_seq( t_count+d0+1,      "      exp1 = 0 ;\n" )
      set_seq( t_count+d0+$nov+1,      "      exp2 = 0 ;\n" )
      set_seq( t_count+d0+$nov+d1,     "      exp3 = 1 ;\n" )
      set_seq( t_count+d0+$nov+d1+1,   "      exp3 = 0 ;\n" )
      set_exp( t_count+d0+d1+$nov+2,   "      if( err || !mtch || ovwp ) $display( \"%0d Error! unexpected responce\", cycle_count ) ;\n" )
      t_count += d0+d1+$nov+2
      # unmatch at end case
      set_seq( t_count,           "      exp0 = 1 ;\n" )
      set_seq( t_count+1,         "      exp0 = 0 ;\n" )
      set_seq( t_count+d0,        "      exp1 = 1 ;\n" )
      set_seq( t_count+d0+$nov,        "      exp2 = 1 ;\n" )
      set_seq( t_count+d0+1,      "      exp1 = 0 ;\n" )
      set_seq( t_count+d0+$nov+1,      "      exp2 = 0 ;\n" )
      set_seq( t_count+d0+$nov+d1+1,   "      exp3 = 1 ;\n" )
      set_seq( t_count+d0+$nov+d1+2,   "      exp3 = 0 ;\n" )
      set_exp( t_count+d0+$nov+d1+2,   "      if( !err || mtch || ovwp ) $display( \"%0d Error! unexpected responce\", cycle_count ) ;\n" )
      t_count += d0+$nov+d1+3
      #piped match case
      set_seq( t_count,           "      exp0 = 1 ;\n" )
      set_seq( t_count+2,         "      exp0 = 0 ;\n" )
      set_seq( t_count+d0,        "      exp1 = 1 ;\n" )
      set_seq( t_count+d0+$nov,        "      exp2 = 1 ;\n" )
      set_seq( t_count+d0+2,      "      exp1 = 0 ;\n" )
      set_seq( t_count+d0+$nov+2,      "      exp2 = 0 ;\n" )
      set_seq( t_count+d0+$nov+d1,     "      exp3 = 1 ;\n" )
      set_seq( t_count+d0+$nov+d1+1,   "      exp3 = 1 ;\n" )
      set_seq( t_count+d0+$nov+d1+2,   "      exp3 = 0 ;\n" )
      set_exp( t_count+d0+$nov+d1+2,   "      if( err ||!mtch || ovwp ) $display( \"%0d Error! unexpected responce\", cycle_count ) ;\n" )
      set_exp( t_count+d0+$nov+d1+3,   "      if( err ||!mtch || ovwp ) $display( \"%0d Error! unexpected responce\", cycle_count ) ;\n" )
      t_count += d0+$nov+d1+4

      #piped error case
      set_seq( t_count,           "      exp0 = 1 ;\n" )
      set_seq( t_count+2,         "      exp0 = 0 ;\n" )
      set_seq( t_count+d0,        "      exp1 = 1 ;\n" )
      set_seq( t_count+d0+$nov,        "      exp2 = 1 ;\n" )
      set_seq( t_count+d0+2,      "      exp1 = 0 ;\n" )
      set_seq( t_count+d0+$nov+2,      "      exp2 = 0 ;\n" )
      set_seq( t_count+d0+$nov+d1,     "      exp3 = 1 ;\n" )
      set_seq( t_count+d0+$nov+d1+1,   "      exp3 = 0 ;\n" )
      set_seq( t_count+d0+$nov+d1+2,   "      exp3 = 0 ;\n" )
      set_exp( t_count+d0+$nov+d1+2,   "      if( err ||!mtch || ovwp ) $display( \"%0d Error! unexpected responce\", cycle_count ) ;\n" )
      set_exp( t_count+d0+$nov+d1+3,   "      if( !err || mtch || ovwp ) $display( \"%0d Error! unexpected responce\", cycle_count ) ;\n" )
      t_count += d0+$nov+d1+3

      final_count_init += "  final_count = #{t_count+10} ;\n"

      1.upto(t_count) do |tm|
         if( $time_array[tm] != nil )
           test_sequences += "    #{tm}: begin\n"
           test_sequences += $time_array[tm]
           test_sequences += "    end\n"
         end
         if( $exp_array[tm] != nil )
           test_expects += "    #{tm}: begin\n"
           test_expects += $exp_array[tm]
           test_expects += "    end\n"
         end
      end
      test_erb = ERB.new $test 
      $test_code = test_erb.result(binding)

      File.open( outfilepref+"_"+sprintf("%d",d0)+"_"+sprintf("%d",d1)+".sv", 'w' ) { |f|
        f.puts template.result(binding)
      }      
    end
  end
end

  
if ($delay == 1) && ($range == 1 ) && ( $p_delay == 1 ) && ( $p_range = 0 )
  # case of exp # exp |-> exp #? exp
  1.upto(5) do | d0 |
  $delay_0 = sprintf( "##%d", d0 )
  1.upto(5) do | d2 |
  1.upto(d2) do | d1 |
    # Note: case of d1 == d2 is the seme as simple delay
    #printf( "%d %d %d\n", d0, d1, d2 )
    $range_0 = sprintf( "##[%d:%d]", d1, d2 )
    test_sequences = ""
    test_expects = "" 
    $time_array = Array.new
    $exp_array = Array.new
    t_count = 4 
    final_count_init = ""
    # match case on various exp3 timing
    d1.upto(d2) do | t0 |
      set_seq( t_count,           "      exp0 = 1 ;\n" )
      set_seq( t_count+1,         "      exp0 = 0 ;\n" )
      set_seq( t_count+d0,        "      exp1 = 1 ;\n" )
      set_seq( t_count+d0+$nov,        "      exp2 = 1 ;\n" )
      set_seq( t_count+d0+1,      "      exp1 = 0 ;\n" )
      set_seq( t_count+d0+$nov+1,      "      exp2 = 0 ;\n" )       
      set_seq( t_count+d0+$nov+t0,     "      exp3 = 1 ;\n" )
      set_seq( t_count+d0+$nov+t0+1,   "      exp3 = 0 ;\n" )      
      set_exp( t_count+d0+$nov+t0+2,   "      if( err || !mtch || ovwp ) $display( \"%0d Error! unexpected responce\", cycle_count ) ;\n" )
      t_count += d0+$nov + t0 + 3
    end
    # unmatch case on various pre exp3 timing
    if( d1 > 1 )
      1.upto(d1-1) do | t0 |
        set_seq( t_count,           "      exp0 = 1 ;\n" )
        set_seq( t_count+1,         "      exp0 = 0 ;\n" )
        set_seq( t_count+d0,        "      exp1 = 1 ;\n" )
        set_seq( t_count+d0+$nov,        "      exp2 = 1 ;\n" )
        set_seq( t_count+d0+1,      "      exp1 = 0 ;\n" )
        set_seq( t_count+d0+$nov+1,      "      exp2 = 0 ;\n" )       
        set_seq( t_count+d0+$nov+t0,     "      exp3 = 1 ;\n" )
        set_seq( t_count+d0+$nov+t0+1,   "      exp3 = 0 ;\n" )      
        set_exp( t_count+d0+$nov+d2+( (d1==d2)?2:3 ),   "      if( !err || mtch || ovwp ) $display( \"%0d Error! unexpected responce\", cycle_count ) ;\n" )
        t_count += d0+$nov + d2 + 3
      end
    end
    # unmatch case on after exp3
    set_seq( t_count,           "      exp0 = 1 ;\n" )
    set_seq( t_count+1,         "      exp0 = 0 ;\n" )
    set_seq( t_count+d0,        "      exp1 = 1 ;\n" )
    set_seq( t_count+d0+$nov,        "      exp2 = 1 ;\n" )
    set_seq( t_count+d0+1,      "      exp1 = 0 ;\n" )
    set_seq( t_count+d0+$nov+1,      "      exp2 = 0 ;\n" )       
    set_seq( t_count+d0+$nov+d2+1,   "      exp3 = 1 ;\n" )
    set_seq( t_count+d0+$nov+d2+2,   "      exp3 = 0 ;\n" )
    set_exp( t_count+d0+$nov+d2+( (d1==d2)?2:3 ),   "      if( !err || mtch || ovwp ) $display( \"%0d Error! unexpected responce\", cycle_count ) ;\n" )
    t_count += d0 + d2 + 3

    # overwrap case
    d1.upto(d2) do | t0 |
      set_seq( t_count,           "      exp0 = 1 ;\n" )
      set_seq( t_count+2,         "      exp0 = 0 ;\n" )
      set_seq( t_count+d0,        "      exp1 = 1 ;\n" )
      set_seq( t_count+d0+$nov,        "      exp2 = 1 ;\n" )
      set_seq( t_count+d0+2,      "      exp1 = 0 ;\n" )
      set_seq( t_count+d0+$nov+2,      "      exp2 = 0 ;\n" )       
      set_seq( t_count+d0+$nov+t0,     "      exp3 = 1 ;\n" )
      set_seq( t_count+d0+$nov+t0+1,   "      exp3 = 0 ;\n" )  
      if d1 == d2
        set_exp( t_count+d0+$nov+t0+2,   "      if( err || !mtch ||ovwp ) $display( \"%0d Error! unexpected responce\", cycle_count ) ;\n" )
        set_exp( t_count+d0+$nov+t0+3,   "      if( !err || mtch || ovwp ) $display( \"%0d Error! unexpected responce\", cycle_count ) ;\n" )
      else    
        set_exp( t_count+d0+$nov+3,   "      if( err || !ovwp ) $display( \"%0d Error! unexpected responce\", cycle_count ) ;\n" )
        set_exp( t_count+d0+$nov+t0+2,   "      if( err || !mtch ) $display( \"%0d Error! unexpected responce\", cycle_count ) ;\n" )
      end
      t_count += d0 + t0 + 3
    end

    final_count_init += "  final_count = #{t_count} ;\n"

    1.upto(t_count) do |tm|
         if( $time_array[tm] != nil )
           test_sequences += "    #{tm}: begin\n"
           test_sequences += $time_array[tm]
           test_sequences += "    end\n"
         end
         if( $exp_array[tm] != nil )
           test_expects += "    #{tm}: begin\n"
           test_expects += $exp_array[tm]
           test_expects += "    end\n"
         end
    end
    test_erb = ERB.new $test 
    $test_code = test_erb.result(binding)

    File.open( outfilepref+"_"+sprintf("%d",d0)+"_"+sprintf("%d",d1)+"_"+sprintf("%d",d2)+".sv", 'w' ) { |f|
      f.puts template.result(binding)
    }      

  end
  end
  end
end
  
if ($delay == 1) && ($range == 1 ) && ( $p_delay == 0 ) && ( $p_range = 1 )
  # case of exp #? exp |-> exp # exp

  1.upto(5) do | d1 |
  1.upto(d1) do | d0 |
  $range_0 = sprintf( "##[%d:%d]", d0, d1 )
  1.upto(5) do | d2 |
  $delay_0 = sprintf( "##%d", d2 )
    test_sequences = ""
    test_expects = "" 
    $time_array = Array.new
    $exp_array = Array.new
    t_count = 4 
    final_count_init = ""
    # match on various timing
    d0.upto(d1) do |t0|
      set_seq( t_count,           "      exp0 = 1 ;\n" )
      set_seq( t_count+1,         "      exp0 = 0 ;\n" )
      set_seq( t_count+t0,        "      exp1 = 1 ;\n" )
      set_seq( t_count+t0+$nov,        "      exp2 = 1 ;\n" )
      set_seq( t_count+t0+1,      "      exp1 = 0 ;\n" )
      set_seq( t_count+t0+1+$nov,      "      exp2 = 0 ;\n" )       
      set_seq( t_count+t0+$nov+d2,     "      exp3 = 1 ;\n" )
      set_seq( t_count+t0+$nov+d2+1,   "      exp3 = 0 ;\n" )      
      set_exp( t_count+t0+$nov+d2+2,   "      if( err || !mtch || ovwp ) $display( \"%0d Error! unexpected responce\", cycle_count ) ;\n" )
      t_count += t0+$nov + d2 + 3      
    end
    # unmatch cases
    d0.upto(d1) do |t0|
      set_seq( t_count,           "      exp0 = 1 ;\n" )
      set_seq( t_count+1,         "      exp0 = 0 ;\n" )
      set_seq( t_count+t0,        "      exp1 = 1 ;\n" )
      set_seq( t_count+t0+$nov,        "      exp2 = 1 ;\n" )
      set_seq( t_count+t0+1,      "      exp1 = 0 ;\n" )
      set_seq( t_count+t0+$nov+1,      "      exp2 = 0 ;\n" )       
      set_seq( t_count+t0+$nov+d2+1,     "      exp3 = 1 ;\n" )
      set_seq( t_count+t0+$nov+d2+2,   "      exp3 = 0 ;\n" )      
      set_exp( t_count+t0+$nov+d2+2,   "      if( !err || mtch || ovwp ) $display( \"%0d Error! unexpected responce\", cycle_count ) ;\n" )
      t_count += t0+$nov + d2 + 4      
    end
    if d2 > ( d0 + 1 ) 
      # pipelined match case
      set_seq( t_count,           "      exp0 = 1 ;\n" )
      set_seq( t_count+1,         "      exp0 = 0 ;\n" )
      set_seq( t_count+d0,        "      exp1 = 1 ;\n" )
      set_seq( t_count+d0+1,      "      exp1 = 0 ;\n" )
      set_seq( t_count+d0+$nov,        "      exp2 = 1 ;\n" )
      set_seq( t_count+d0+$nov+1,      "      exp2 = 0 ;\n" )       
      set_seq( t_count+d0+$nov+d2,     "      exp3 = 1 ;\n" )
      set_seq( t_count+d0+$nov+d2+1,   "      exp3 = 0 ;\n" )   
      set_exp( t_count+d0+$nov+d2+2,   "      if( err || !mtch || ovwp ) $display( \"%0d Error! unexpected responce\", cycle_count ) ;\n" )
      set_seq( t_count+d0+1,      "      exp0 = 1 ;\n" )
      set_seq( t_count+d0+2,      "      exp0 = 0 ;\n" ) 
      set_seq( t_count+d0+1+d0,      "      exp1 = 1 ;\n" )  
      set_seq( t_count+d0+2+d0,      "      exp1 = 0 ;\n" )  
      set_seq( t_count+d0+1+d0+$nov,      "      exp2 = 1 ;\n" )  
      set_seq( t_count+d0+2+d0+$nov,      "      exp2 = 0 ;\n" )  
      set_seq( t_count+d0+1+d0+$nov+d2,     "      exp3 = 1 ;\n" )
      set_seq( t_count+d0+2+d0+$nov+d2,   "      exp3 = 0 ;\n" )      
      set_exp( t_count+d0+1+d0+$nov+d2+2,   "      if( err || !mtch || ovwp ) $display( \"%0d Error! unexpected responce\", cycle_count ) ;\n" )
      t_count += d0 + d2 + 4            

    # pipelined error case
      set_seq( t_count,           "      exp0 = 1 ;\n" )
      set_seq( t_count+1,         "      exp0 = 0 ;\n" )
      set_seq( t_count+d0,        "      exp1 = 1 ;\n" )
      set_seq( t_count+d0+1,      "      exp1 = 0 ;\n" )
      set_seq( t_count+d0+$nov,        "      exp2 = 1 ;\n" )
      set_seq( t_count+d0+$nov+1,      "      exp2 = 0 ;\n" )       
      set_seq( t_count+d0+$nov+d2,     "      exp3 = 1 ;\n" )
      set_seq( t_count+d0+$nov+d2+1,   "      exp3 = 0 ;\n" )   
      set_exp( t_count+d0+$nov+d2+2,   "      if( err || !mtch || ovwp ) $display( \"%0d Error! unexpected responce\", cycle_count ) ;\n" )
      set_seq( t_count+d0+1,      "      exp0 = 1 ;\n" )
      set_seq( t_count+d0+2,      "      exp0 = 0 ;\n" ) 
      set_seq( t_count+d0+1+d0,      "      exp1 = 1 ;\n" )  
      set_seq( t_count+d0+2+d0,      "      exp1 = 0 ;\n" )  
      set_seq( t_count+d0+1+d0+$nov,      "      exp2 = 1 ;\n" )  
      set_seq( t_count+d0+2+d0+$nov,      "      exp2 = 0 ;\n" )  
      set_exp( t_count+d0+1+d0+$nov+d2+2,   "      if( !err || mtch || ovwp ) $display( \"%0d Error! unexpected responce\", cycle_count ) ;\n" )
      t_count += d0 + d2 + 4            

    end

    final_count_init += "  final_count = #{t_count} ;\n"

    1.upto(t_count) do |tm|
         if( $time_array[tm] != nil )
           test_sequences += "    #{tm}: begin\n"
           test_sequences += $time_array[tm]
           test_sequences += "    end\n"
         end
         if( $exp_array[tm] != nil )
           test_expects += "    #{tm}: begin\n"
           test_expects += $exp_array[tm]
           test_expects += "    end\n"
         end
    end

    test_erb = ERB.new $test 
    $test_code = test_erb.result(binding)

    File.open( outfilepref+"_"+sprintf("%d",d0)+"_"+sprintf("%d",d1)+"_"+sprintf("%d",d2)+".sv", 'w' ) { |f|
      f.puts template.result(binding)
    }      

  end
  end
  end
end
