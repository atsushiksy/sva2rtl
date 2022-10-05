module delay_pipe_4_test ;

   reg clock, reset_, clear, enable, start ;
   wire busy, go ;

   initial begin


      clock = 0 ;
      reset_ = 0 ;
      clear = 0 ;
      enable = 0 ;
      start = 0 ;

      #5  reset_ = 1 ;
      #10 enable = 1 ;
      #10 start = 1 ;
      #10 start = 0 ;
      #20 clear = 1 ;
      #20 $finish ;

   end // initial begin

   always begin
      #5 clock = !clock ;
   end

   always @(posedge clock) begin
      $display ( 
        "%d r:%b c:%b e:%b s:%b b:%b g:%b", 
        $time, reset_, clear, enable, start, busy, go 
      ) ;
   end
   
   ARV_DELAY_PIPE #(3, 4) p0 (
     .Clk(clock), .R_(reset_), .E(enable), .C(clear), 
     .D(start), .Q(go), .B(busy)
   ) ;
   
endmodule // delay_pipe_4_test

   
      