/*
 *  Verilog Primitive Modules for sva2rtl
 *  
 *  Author: Atsushi Kasuya
 *
 *
 ***************************************************************************/
 /* 
   Copyright (C) 2011 Atsushi Kasuya
 */

/* D-FF for buffering */
module ARV_DFF (Clk, RN, D, Q) ;
   input Clk ;
   input RN ;
   input D ;
   output Q ;
   reg 	  Q ;

   always @ ( negedge RN or posedge Clk )
     if( !RN ) Q <= 0 ;
     else Q <= D ;

endmodule // ARV_DFF

module ARV_DFF_ES (Clk, RN, E, D, Q) ;
   parameter DEPTH = 1 ;
   input Clk ;
   input RN ;
   input E ;
   input D ;
   output Q ;
   reg 	[DEPTH-1:0]  X;

   always @ ( negedge RN or posedge Clk ) begin
     if( !RN ) X <= 0 ;
     else begin
       if( E ) begin
	 X <= {X,D} ;
       end	
       else begin
	 X <= 0 ;
       end
	//$display( "DFF_ES %m  D:%b X:%b Q:%b", D, X, Q ) ;
     end
   end

   assign Q = (DEPTH == 0) ? D : X[DEPTH-1] ;
   
endmodule // ARV_DFF_ES

module ARV_DFF_ESW (Clk, RN, E, D, Q) ;
   parameter DEPTH = 1 ;
   parameter WIDTH = 1 ;
   input Clk ;
   input RN ;
   input E ;
   input 	[WIDTH-1:0] D ;
   output 	[WIDTH-1:0] Q ;
   reg 	[WIDTH-1:0]  X [0:DEPTH-1] ;
   integer 	     i ;
   

   always @ ( negedge RN or posedge Clk ) begin
     if( !RN ) begin
	for( i = 0 ; i < DEPTH ; i = i + 1 ) 
	   X[i] <= 0 ;
     end
     else begin
       if( E ) begin
	  for( i = 0 ; i < DEPTH ; i = i + 1 )
	     X[i] <= ( i == 0 ) ? D : X[i-1] ;
       end	
       else begin
	for( i = 0 ; i < DEPTH ; i = i + 1 ) 
	   X[i] <= 0 ;
       end
     end // else: !if( !RN )
     //$display( "DFF_ES %m  D:%h X0:%h X1:%h X2:%h Q:%h", D,  X[0], X[1], X[2],Q ) ;

   end

   assign Q = (DEPTH == 0) ? D : X[DEPTH-1] ;
   
endmodule // ARV_DFF_ESW

module ARV_DFF_E (Clk, RN, E, D, Q) ;
   input Clk ;
   input RN ;
   input E ;
   input D ;
   output Q ;
   reg 	  Q ;

   always @ ( negedge RN or posedge Clk ) begin
     if( !RN ) Q <= 0 ;
     else begin
       if( E ) 
	 Q <= D ;
       else
	 Q <= 0 ;
     end
   end

endmodule // ARV_DFF_E

/* SysFuncBlock module for $rose $fell $stable $past $sampled */
/* Here, we assume that entire logic will only be enabled more than 2 cycle
   after the reset is released, so that the undtablity at the begining
   will not be the issue.
 */
module ARV_SYSFUNC_BLK (Clk, RN, E, C, D, ROSE, FELL, STBL, PAST, SMPL) ;
   input Clk ;
   input RN ;
   input E ;
   input C ;
   input D ;
   output ROSE ;
   output FELL ;
   output STBL ;
   output PAST ;
   output SMPL ;
   reg 	  Q1, Q2  ;

   always @ ( negedge RN or posedge Clk ) begin
     if( !RN || C )  begin 
	Q1 <= 0 ;
	Q2 <= 0 ;
     end
     else begin
	Q1 <= D ;
	Q2 <= Q1 ;
     end
   end

   assign #1 ROSE = E && Q1 && !Q2 ;
   assign #1 FELL = E && !Q1 && Q2 ;
   assign #1 STBL = E && Q1 && Q2 ;
   assign #1 PAST = Q2 ;
   assign #1 SMPL = Q1 ;

endmodule // ARV_SYSFUNC_BLK

module ARV_SYSFUNC_PAST_BLK (Clk, RN, E, C, D, PAST) ;
   parameter PAST_NUM = 1 ;
   input Clk ;
   input RN ;
   input E ;
   input C ;
   input D ;
   output PAST ;
   reg 	[PAST_NUM-1:0]  Q;

   always @ ( negedge RN or posedge Clk ) begin
     if( !RN ) Q <= 0 ;
     else begin
       if( E ) 
	 Q <= (PAST_NUM>1)?{Q[PAST_NUM-1:1],D}:D ;
       else
	 Q <= 0 ;
     end
   end

   assign #1 PAST = Q[PAST_NUM-1] ;

endmodule // ARV_SYSFUNC_PAST_BLK

module ARV_DELAY_PIPE1 ( Clk, RN, E, C, D, Q, B ) ;
   input Clk ;
   input RN ;
   input E ;
   input C ;
   input D ;
   output Q ;
   output B ;

   reg Y ;

   always @ ( negedge RN or posedge Clk ) begin
     if( !RN || C || !E ) begin
       Y <= 0 ;
     end
     else begin
       Y <= D ;
     end
   end
   
   assign #1 Q = E && Y ;
   assign #1 B = E && Y ;
   
endmodule // ARV_DELAY_PIPE1

// For debug, with display
module ARV_DELAY_PIPE0 ( Clk, RN, E, C, D, Q, B ) ;
   input Clk ;
   input RN ;
   input E ;
   input C ;
   input D ;
   output Q ;
   output B ;

   reg Y ;

   always @ ( negedge RN or posedge Clk ) begin
     if( !RN || C || !E ) begin
       Y <= 0 ;
	$display( " RN %b C %b E %b D %b Y %b Q %b", RN, C, E, D, Y, Q ) ;
     end
     else begin
       Y <= D ;
	$display( "RN %b C %b E %b D %b Y %b Q %b B %b", RN, C, E, D, Y, Q, B ) ;
     end
   end
   
   assign #1 Q = E && Y ;
   assign #1 B = E && Y ;
   
endmodule // ARV_DELAY_PIPE0

// For debug, with display
module ARV_ERROR_GEN ( Clk, RN, E, C, B, M, ER ) ;
   input Clk ;
   input RN ;
   input E ;
   input C ;
   input B ;
   input M ;
   output ER ;

   reg B0 ;
   reg BL ;
   
   always @ ( negedge RN or posedge Clk ) begin
     if( !RN || C || !E ) begin
	BL <= 0 ;
	B0 <= 0 ;
     end
     else if( B && !M && !BL && !B0 ) begin
	BL <= 1 ;
	B0 <= 1 ;
     end
     else if( B & M ) begin
	BL <= 0 ;
     end
     else if( !B ) begin
	BL <= 0 ;
	B0 <= 0 ;
     end
     else begin
       BL <= BL ;
       B0 <= B0 ;
     end
     //$display( "ERR_GEN B:%b M:%b BL:%b B0:%b ER:%b", B, M, BL, B0, ER ) ;
   end
   
   assign #1 ER = E && !B && BL ;
   
endmodule // ARV_ERROR_GEN

module ARV_DELAY_PIPE ( Clk, RN, E, C, D, Q, B ) ;
   parameter DLY1 = 1 ;
   parameter DLY2 = 2 ;
   input Clk ;
   input RN ;
   input E ;
   input C ;
   input D ;
   output Q ;
   output B ;

   reg [DLY2-1:0] Y ;

   always @ ( negedge RN or posedge Clk ) begin
     if( !RN || C || !E ) begin
       Y <= 0 ;
     end
     else begin
       Y <= {Y[DLY2-2:0],D} ;
     end
     //$display( "RN %b C %b E %b D %b Y %b Q %b B %b", RN, C, E, D, Y, Q, B ) ;
   end
   
   // using reduction unary or operator
   assign #1 Q = E && ( (DLY1 > 0) ? (|Y[DLY2-1:DLY1-1]) : ( (|Y[DLY2-1:0]) | D ) ) ;
   assign #1 B = E && (|Y) ;

endmodule // ARV_DELAY_PIPE

module ARV_DELAY_COUNTER ( Clk, RN, E, C, D, Q, B ) ;
   parameter DLY1 = 1 ;
   parameter DLY2 = 6 ;
   parameter NBIT = 3 ;
   input Clk ;
   input RN ;
   input E ;
   input C ;
   input D ;
   output Q ;
   output B ;
   
   reg [NBIT-1:0] Y ;

   always @ ( negedge RN or posedge Clk ) begin
     if( !RN || C || !E ) begin
        Y <= 0 ;
     end
     else begin
        if( Y == DLY2 ) Y <= 0 ;
        else if ( Y > 0 || D ) Y <= Y + 1 ;
     end
   end

   //always @ (negedge RN or posedge Clk) begin
   //  if ( Y > 0 || D )
   //     $display( "DlyCnt %m C:%b D:%b Y:%b Q:%b B:%b", C, D, Y, Q, B ) ;
   //end

   assign #1 Q = E && (Y >= DLY1) ;
   assign #1 B = E && (Y > 0) ;

endmodule // ARV_DELAY_COUNTER

module ARV_DELAY_EVER ( Clk, RN, E, C, D, Q, B ) ;
   parameter DLY1 = 6 ;
   parameter NBIT = 3 ;
   input Clk ;
   input RN ;
   input E ;
   input C ;
   input D ;
   output Q ;
   output B ;
   
   reg [NBIT-1:0] Y ;

   always @ ( negedge RN or posedge Clk ) begin
     if( !RN || C || !E ) begin
        Y <= 0 ;
     end
     else begin
        if( Y == DLY1 ) Y <= DLY1 ;
        else if ( Y > 0 || D ) Y <= Y + 1 ;
     end
   end
   

   assign #1 Q = E && (Y == DLY1) ;
   assign #1 B = E && (Y > 0) ;

endmodule // ARV_DELAY_EVER

module ARV_SEQ_AND( Clk, RN, E, C, D1, D2, Q, B ) ;
   input Clk ;
   input RN ;
   input E ;
   input C ;
   input D1 ;
   input D2 ;
   output Q ;
   output B ;
   

   reg 	  Y1, Y2 ;

   always @ ( negedge RN or posedge Clk ) begin 
     if( !RN || C || !E ) begin
	Y1 <= 0 ;
	Y2 <= 0 ;
     end
     else begin
	Y1 <= D1 | Y1 ;
	Y2 <= D2 | Y2 ;
     end
     //$display( "%m D1:%b D2:%b Y1:%b Y2:%b Q:%b B:%b", D1, D2, Y1, Y2, Q, B ) ;
   end

   assign #1 Q = (D1 && D2) || (D1 && Y2) || ( D2 && Y1 ) ;
   assign #1 B = Y1 || Y2 ;

endmodule // ARV_SEQ_AND

module ARV_SEQ_AND_S( Clk, RN, E, C, B1, B2, D1, D2, Q, B ) ;
   input Clk ;
   input RN ;
   input E ;
   input C ;
   input B1 ;
   input B2 ;
   input D1 ;
   input D2 ;
   output Q ;
   output B ;
   

   reg 	  Y1, Y2 ;

   always @ ( negedge RN or posedge Clk ) begin 
     if( !RN || C || !E ) begin
	Y1 <= 0 ;
	Y2 <= 0 ;
     end
     else begin
	Y1 <= D1 | (Y1 && B2) ;
	Y2 <= D2 | (Y2 && B1) ;
     end
      //$display( "%m B1:%b B2:%b D1:%b D2:%b Y1:%b Y2:%b Q:%b B:%b", B1, B2, D1, D2, Y1, Y2, Q, B ) ;
   end

   assign #1 Q = (D1 && D2) || (D1 && Y2) || ( D2 && Y1 ) ;
   assign #1 B = B1 || B2 ;

endmodule // ARV_SEQ_AND

module ARV_PRP_OR( Clk, RN, E, C, S, B1, B2, D1, D2, E1, E2, CS, Q, B, ER ) ;
   input Clk ;
   input RN ;
   input E ;
   input C ;
   input S ;
   input B1 ;
   input B2 ;
   input D1 ;
   input D2 ;
   input E1 ;
   input E2 ;
   output CS ;
   output Q ;
   output B ;
   output ER ;
   
   reg 	  Y0 ;
   reg 	  Y1 ;

   always @ ( negedge RN or posedge Clk ) begin 
     if( !RN || C || !E ) begin
	Y0 <= 0 ;
	Y1 <= 0 ;
     end
     else begin
	Y0 <= ( E1 | E2 ) ;
	Y1 <= ( ( Y0 ) & !Q & ( B1 | B2 ) ) | ( Y1 & ( B1 | B2 ) & !Q )  ;
     end
     //$display( "%m S:%b CS:%b B1:%b B2:%b D1:%b D2:%b E1:%b E2:%b Y0:%b Y1:%b Q:%b B:%b ER:%b", S, CS, B1, B2, D1, D2, E1, E2, Y0, Y1, Q, B, ER ) ;
   end

   assign #1 CS = S && !B1 && !B2 ;
   assign #1 Q = D1 || D2  ;
   assign #1 B = B1 || B2 ;
   assign #1 ER = ( ( Y0 ) & !B1 & !B2 ) | ( !B1 & !B2 & Y1 & !Q ) ; 

endmodule // ARV_PRP_OR

module ARV_PRP_AND( Clk, RN, E, C, S, B1, B2, D1, D2, E1, E2, CS, Q, B, ER ) ;
   input Clk ;
   input RN ;
   input E ;
   input C ;
   input S ;
   input B1 ;
   input B2 ;
   input D1 ;
   input D2 ;
   input E1 ;
   input E2 ;
   output CS ;
   output Q ;
   output B ;
   output ER ;
   

   reg 	  EE0, EE1, Y1, Y2, BB ;

   always @ ( negedge RN or posedge Clk ) begin 
     if( !RN || C || !E ) begin
	EE0 <= 0 ;
	EE1 <= 0 ;
	Y1 <= 0 ;
	Y2 <= 0 ;
	BB <= 0 ;
     end
     else begin
	EE0 <= ( E1 | E2 ) ;
	EE1 <= ( ( EE0 ) & !Q & ( B1 | B2 ) ) | ( EE1 & ( B1 | B2 ) & !Q )  ;
	Y1 <= ( D1 | (Y1 && B2) ) & !Q ;
	Y2 <= ( D2 | (Y2 && B1) ) & !Q ;
	BB <= B & !Q ;
     end
      // $display( "%m S:%b B1:%b B2:%b D1:%b D2:%b E1:%b E2:%b EE0:%b EE1:%b Y1:%b Y2:%b Q:%b B:%b", S, B1, B2, D1, D2, E1, E2, EE0, EE1, Y1, Y2, Q, B ) ;
   end

   assign #1 CS = S && !B1 && !B2 ;
   assign #1 Q = (D1 && D2) || (D1 && Y2) || ( D2 && Y1 ) ;
   assign #1 B = B1 || B2 ;
   assign #1 ER = ( ( EE0 ) & !B1 & !B2 ) | ( !B1 & !B2 & ( BB | EE1 ) & !Q ) ; 

endmodule // ARV_PRP_AND

module ARV_C_REP_E1 ( Clk, RN, E, C, S, D, Q, B ) ;
   // parameter DLY1 = 1 ; Fix DLY1 == 1
   parameter DLY2 = 6 ;
   parameter NBIT = 3 ;
   input Clk ;
   input RN ;
   input E ;
   input C ;
   input S ; // start
   input D ; // expression
   output Q ;
   output B ;
   //output ER ;
   
   reg [NBIT-1:0] Y ;

   always @ ( negedge RN or posedge Clk ) begin
     if( !RN || C || !E ) begin
        Y <= 0 ;
     end
     else begin
        if( D && (Y == DLY2 - 1) ) Y <= 0 ;
        else if ( (D && Y > 0) || D & S ) Y <= Y + 1 ;
	else Y <= 0 ;
     end
     //$display("RN:%b E:%b C:%b S:%b D:%b Y:%b Q:%b B:%b ER:%b", RN,E,C,S,D,Y,Q,B,ER);
      
   end
   
   assign #1 Q = E && D && ( S || (Y >0) ) ;
   //assign #1 ER = E && !D &&  S ;
   assign #1 B = E &&  (Y > 0) ;

endmodule // ARV_C_REP_E1

// Note: DLY1 must be larger than 2
module ARV_C_REP_EN ( Clk, RN, E, C, S, D, Q, B ) ;
   parameter DLY1 = 2 ;
   parameter DLY2 = 6 ;
   parameter NBIT = 3 ;
   input Clk ;
   input RN ;
   input E ;
   input C ;
   input S ; // start
   input D ; // expression
   output Q ;
   output B ;
   //output ER ;
   
   reg [NBIT-1:0] Y ;

   always @ ( negedge RN or posedge Clk ) begin
     if( !RN || C || !E ) begin
        Y <= 0 ;
     end
     else begin
        if( D && (Y == DLY2 - 1) ) Y <= 0 ;
        else if ( (D && Y > 0) || D & S ) Y <= Y + 1 ;
	else Y <= 0 ;
     end
     //$display("RN:%b E:%b C:%b S:%b D:%b Y:%b Q:%b B:%b", RN,E,C,S,D,Y,Q,B);
      
   end
   
   assign #1 Q = E && D && ( Y >= DLY1 - 1 ) ;
   //assign #1 ER = E && !D && ( S || ( ( Y > 0 ) && (Y < (DLY1 - 1)) ) );
   assign #1 B = E &&  (Y > 0) ;

endmodule // ARV_C_REP_EN

// Consective repetition for sequence
module ARV_C_REP_S ( Clk, RN, E, C, S, D, G, N, Q, B ) ;
   parameter DLY1 = 1 ;
   parameter DLY2 = 6 ;
   parameter NBIT = 3 ;
   input Clk ;
   input RN ;
   input E ;
   input C ;
   input S ;  // to be connected to match_node input (start)
   input G ;  // to be connected to busy of the sequence
   input D ;  // to be connected to match output of the sequence
   output N ; // to be connected to start input of the sequence
   output Q ;
   output B ;
   
   reg [NBIT-1:0] Y ;
   reg 		  DD ;
   reg            BB ;
   
   wire YE = ( Y >= (DLY1-1) ) ;

   always @ ( negedge RN or posedge Clk ) begin
     if( !RN || C || !E ) begin
        Y <= 0 ;
	DD <= 0 ;
	BB <= 0 ;
     end
     else begin
	
	if( S && (Y == 0) ) begin
	   BB <= 1 ;
	end
        else if( (!G && !D && !DD) || (D && Y == DLY2 - 1) ) begin
	   Y <= 0 ;
	   DD <= 0 ;
	   BB <= 0 ;
	end
        else if ( D ) begin
	   Y <= Y + 1 ;
	   DD <= 1 ;
	   BB <= 1 ;
	end
	else if ( DD ) begin
	   Y <= Y ;
	   DD <= 0 ;
	   BB <= 1 ;
	end
	else if ( G && BB ) begin
	   Y <= Y ;
	   BB <= 1 ;
	end
	else begin
	   Y <= Y ;
	   DD <= 0 ;
	   BB <= 0 ;
	end
     end
   end
   //always @( S or BB or DD or D or YE ) begin
   //   $display("%d RN:%b E:%b C:%b S:%b G:%b D:%b DD:%b N:%b Y:%b YE:%B BB:%b Q:%b B:%b", $time, RN,E,C,S,G,D,DD,N,Y,YE,BB,Q,B);

   //end
   
   assign #1 Q = E && D && YE ;
   assign #1 N = !C && ( (S && !BB) || DD ) ;
   assign #1 B = E && ( BB || DD || (D && YE)) ;

endmodule // ARV_C_REP_S

module ARV_G_REP1 ( Clk, RN, E, C, S, D, Q, B ) ;
   input Clk ;
   input RN ;
   input E ;
   input C ;
   input S ;
   input D ;
   output Q ;
   output B ;
   
   reg 		  BB ;
   
   always @ ( negedge RN or posedge Clk ) begin
     if( !RN || C || !E ) begin
	BB <= 0 ;
     end
     else begin
	if( S && !D ) begin
           BB <= 1 ;	   
	end
	else if( D ) begin
	   BB <= 0 ;
	end
     end
     // $display( "GREP1  C:%b S:%b D:%b BB:%b Q:%b B:%b", C, S, D, BB, Q, B ) ;
   end
   
   assign #1 Q = E && D ;
   assign #1 B = E && BB ;

endmodule // ARV_G_REP1
	    
// Goto repetition module
module ARV_G_REP ( Clk, RN, E, C, S, D, Q, B ) ;
   parameter DLY1 = 1 ;
   parameter DLY2 = 6 ;
   parameter NBIT = 3 ;
   input Clk ;
   input RN ;
   input E ;
   input C ;
   input S ;
   input D ;
   output Q ;
   output B ;
   
   reg [NBIT-1:0] Y ;
   reg 		  BB ;
   
   always @ ( negedge RN or posedge Clk ) begin
     if( !RN || C || !E ) begin
        Y <= 0 ;
	BB <= 0 ;
     end
     else begin
	if( S && !BB ) begin
	   if( D ) Y = 1 ;
	   else Y = 0 ;
           BB <= 1 ;	   
	end
	else if( BB & D ) begin
	   if( Y == DLY2-1 ) begin
	      Y <= 0 ;
	      BB <= 0 ;
	   end
	   else begin
	      Y <= Y + 1 ;
	   end
	end
	else begin
	   Y <= Y ;
	   BB <= BB ;
        end
     end
     //$display( "D1:%d D2:%d  C:%b S:%b D:%b Y:%b Q:%b B:%b", DLY1, DLY2, C, S, D, Y, Q, B ) ;
   end
   
   assign #1 Q = E && D && (Y >= DLY1-1 ) ;
   assign #1 B = E && BB ;

endmodule // ARV_G_REP

module ARV_THROUGHOUT ( Clk, RN, E, C, S, G, D, P, N, F, Q, B ) ;
   input Clk ;
   input RN ;
   input E ;
   input C ;
   input S ;  // to be connected to match_node input (start)
   input G ;  // to be connected to busy of the sequence
   input D ;  // to be connected to match of the sequence
   input P ;  // to be connected to expression
   output N ; // to be connected to start input of the sequence
   output F ; // to be connected to clear of the sequence
   output Q ;
   output B ;

   reg 	  state ;

   always @ ( negedge RN or posedge Clk ) begin
     if( !RN || C || !E ) begin
        state <= 0 ;
     end
     else begin
        if(state == 0 ) begin
           if( S ) state <= 1 ;
	   else state <= 0 ;
	end
        else if ( !P || !G ) state <= 0 ;
	else state <= 1 ;
     end // else: !if( !RN || C || !E )
     // $display( "S:%b G:%b D:%b P:%b N:%b F:%b Q:%b B:%b state:%b", S,G,D,P,N,F,Q,B,state ) ;
   end   

   assign #1 N = E && S && (state == 0) ;
   assign #1 F = E && state && !P ;
   assign #1 Q = E && state && D && P ;
   assign #1 B = E && state ;
   
endmodule //  ARV_THROUGHOUT

module ARV_DISPATCH_2( Clk, RN, E, C, D, B1, B2, Q1, Q2, OW ) ;
   input Clk ;
   input RN ;
   input E ;
   input C ;
   input D ;
   input B1 ;
   input B2 ;
   output Q1 ;
   output Q2 ;
   output OW ;

   reg 	  Y ;

   assign #1 Q1 = !B1 && D ;
   assign #1 Q2 = B1 && !B2 && D ;
   assign #1 OW = Y ;

   always @ ( negedge RN or posedge Clk ) begin 
     if( !RN || C || !E ) begin
	Y <= 0 ;
     end
     else begin
	Y <= (B1 && B2 && D) ;
     end
     //if( D || B1 || B2 ) 
     //  $display( "%m D:%b B1:%b B2:%b Q1:%b Q2:%b OW:%b C:%b", D, B1, B2, Q1, Q2, OW, C ) ;
   end

endmodule // ARV_DISPATCH_2

module ARV_DISPATCH_3( Clk, RN, E, C, D, B1, B2, B3, Q1, Q2, Q3, OW ) ;
   input Clk ;
   input RN ;
   input E ;
   input C ;
   input D ;
   input B1 ;
   input B2 ;
   input B3 ;
   output Q1 ;
   output Q2 ;
   output Q3 ;
   output OW ;

   reg 	  Y ;

   assign #1 Q1 = !B1 && D ;
   assign #1 Q2 = B1 && !B2 && D ;
   assign #1 Q3 = B1 && B2 && !B3 && D ;
   assign #1 OW = Y ;
   
   always @ ( negedge RN or posedge Clk ) begin 
     if( !RN || C || !E ) begin
	Y <= 0 ;
     end
     else begin
	Y <= (B1 && B2 && B3 && D) ;
     end
     //$display( "%m D:%b B1:%b B2:%b B3:%b Q1:%b Q2:%b Q3:%b OW:%b C:%b", D, B1, B2, B3, Q1, Q2, Q3, OW, C ) ;
   end

endmodule // ARV_DISPATCH_3


module ARV_DISPATCH_4( 
  Clk, RN, E, C, D, B1, B2, B3, B4, Q1, Q2, Q3, Q4, OW
) ;
   input Clk ;
   input RN ;
   input E ;
   input C ;
   input D ;
   input B1 ;
   input B2 ;
   input B3 ;
   input B4 ;
   output Q1 ;
   output Q2 ;
   output Q3 ;
   output Q4 ;
   output OW ;

   reg 	  Y ;

   assign #1 Q1 = !B1 && D ;
   assign #1 Q2 = B1 && !B2 && D ;
   assign #1 Q3 = B1 && B2 && !B3 && D ;
   assign #1 Q4 = B1 && B2 && B3 && !B4 && D ;
   assign #1 OW = Y ;
   
   always @ ( negedge RN or posedge Clk ) begin 
     if( !RN || C || !E ) begin
	Y <= 0 ;
     end
     else begin
	Y <= (B1 && B2 && B3 && B4 && D) ;
     end
   end

endmodule // ARV_DISPATCH_4

module ARV_DISPATCH_5 ( 
  Clk, RN, E, C, D, B1, B2, B3, B4, B5, Q1, Q2, Q3, Q4, Q5, OW
) ;
   input Clk ;
   input RN ;
   input E ;
   input C ;
   input D ;
   input B1 ;
   input B2 ;
   input B3 ;
   input B4 ;
   input B5 ;
   output Q1 ;
   output Q2 ;
   output Q3 ;
   output Q4 ;
   output Q5 ;
   output OW ;

   reg 	  Y ;

   assign #1 Q1 = !B1 && D ;
   assign #1 Q2 = B1 && !B2 && D ;
   assign #1 Q3 = B1 && B2 && !B3 && D ;
   assign #1 Q4 = B1 && B2 && B3 && !B4 && D ;
   assign #1 Q5 = B1 && B2 && B3 && B4 && !B5 && D ;
   assign #1 OW = Y ;
   
   always @ ( negedge RN or posedge Clk ) begin 
     if( !RN || C || !E ) begin
	Y <= 0 ;
     end
     else begin
	Y <= (B1 && B2 && B3 && B4 && B5 && D) ;
     end
   end

endmodule // ARV_DISPATCH_5

module ARV_DISPATCH_6 ( 
  Clk, RN, E, C, D, B1, B2, B3, B4, B5, B6, Q1, Q2, Q3, Q4, Q5, Q6, OW
) ;
   input Clk ;
   input RN ;
   input E ;
   input C ;
   input D ;
   input B1 ;
   input B2 ;
   input B3 ;
   input B4 ;
   input B5 ;
   input B6 ;
   output Q1 ;
   output Q2 ;
   output Q3 ;
   output Q4 ;
   output Q5 ;
   output Q6 ;
   output OW ;

   reg 	  Y ;

   assign #1 Q1 = !B1 && D ;
   assign #1 Q2 = B1 && !B2 && D ;
   assign #1 Q3 = B1 && B2 && !B3 && D ;
   assign #1 Q4 = B1 && B2 && B3 && !B4 && D ;
   assign #1 Q5 = B1 && B2 && B3 && B4 && !B5 && D ;
   assign #1 Q6 = B1 && B2 && B3 && B4 && B5 && !B6 && D ;
   assign #1 OW = Y ;
   
   always @ ( negedge RN or posedge Clk ) begin 
     if( !RN || C || !E ) begin
	Y <= 0 ;
     end
     else begin
	Y <= (B1 && B2 && B3 && B4 && B5 && B6 && D) ;
     end
   end

endmodule // ARV_DISPATCH_6

module ARV_DISPATCH_7 ( 
  Clk, RN, E, C, D, B1, B2, B3, B4, B5, B6, B7, Q1, Q2, Q3, Q4, Q5, Q6, Q7, OW
) ;
   input Clk ;
   input RN ;
   input E ;
   input C ;
   input D ;
   input B1 ;
   input B2 ;
   input B3 ;
   input B4 ;
   input B5 ;
   input B6 ;
   input B7 ;
   output Q1 ;
   output Q2 ;
   output Q3 ;
   output Q4 ;
   output Q5 ;
   output Q6 ;
   output Q7 ;
   output OW ;

   reg 	  Y ;

   assign #1 Q1 = !B1 && D ;
   assign #1 Q2 = B1 && !B2 && D ;
   assign #1 Q3 = B1 && B2 && !B3 && D ;
   assign #1 Q4 = B1 && B2 && B3 && !B4 && D ;
   assign #1 Q5 = B1 && B2 && B3 && B4 && !B5 && D ;
   assign #1 Q6 = B1 && B2 && B3 && B4 && B5 && !B6 && D ;
   assign #1 Q7 = B1 && B2 && B3 && B4 && B5 && B6 && !B7 && D ;
   assign #1 OW = Y ;
   
   always @ ( negedge RN or posedge Clk ) begin 
     if( !RN || C || !E ) begin
	Y <= 0 ;
     end
     else begin
	Y <= (B1 && B2 && B3 && B4 && B5 && B6 && B7 && D) ;
     end
   end

endmodule // ARV_DISPATCH_7

module ARV_DISPATCH_8 ( 
  Clk, RN, E, C, D, B1, B2, B3, B4, B5, B6, B7, B8,
  Q1, Q2, Q3, Q4, Q5, Q6, Q7, Q8, OW
) ;
   input Clk ;
   input RN ;
   input E ;
   input C ;
   input D ;
   input B1 ;
   input B2 ;
   input B3 ;
   input B4 ;
   input B5 ;
   input B6 ;
   input B7 ;
   input B8 ;
   output Q1 ;
   output Q2 ;
   output Q3 ;
   output Q4 ;
   output Q5 ;
   output Q6 ;
   output Q7 ;
   output Q8 ;
   output OW ;

   reg 	  Y ;

   assign #1 Q1 = !B1 && D ;
   assign #1 Q2 = B1 && !B2 && D ;
   assign #1 Q3 = B1 && B2 && !B3 && D ;
   assign #1 Q4 = B1 && B2 && B3 && !B4 && D ;
   assign #1 Q5 = B1 && B2 && B3 && B4 && !B5 && D ;
   assign #1 Q6 = B1 && B2 && B3 && B4 && B5 && !B6 && D ;
   assign #1 Q7 = B1 && B2 && B3 && B4 && B5 && B6 && !B7 && D ;
   assign #1 Q8 = B1 && B2 && B3 && B4 && B5 && B6 && B7 && !B8 && D ;
   assign #1 OW = Y ;
   
   always @ ( negedge RN or posedge Clk ) begin 
     if( !RN || C || !E ) begin
	Y <= 0 ;
     end
     else begin
	Y <= (B1 && B2 && B3 && B4 && B5 && B6 && B7 && B8 && D) ;
     end
   end

endmodule // ARV_DISPATCH_8

module ARV_CONT_REP_EXP( Clk, RN, E, C, GO, EXP, M, F, B ) ;
   parameter NBIT = 2 ;   
   parameter CNT1 = 1 ;
   parameter CNT2 = 2 ;
   input Clk ;
   input RN ;
   input E ;
   input C ;
   input GO ;
   input EXP ;
   output M ;
   output F ;
   output B ;

   reg 	[NBIT-1:0]  CNT ;

   always @ ( negedge RN or posedge Clk ) begin 
     if( !RN || C || !E ) begin
	CNT <= 0 ;
     end
     else begin
       if( (EXP && GO && (CNT==0) ) || (EXP && (CNT > 0) && (CNT < CNT2) ) ) 
	 CNT <= CNT+1 ;
       else 
	 CNT <= 0 ;
     end
   end // always @ ( RN or C or E or posedge Clk )

   assign #1 B = ( CNT > 0 ) ;
   assign #1 M = ( CNT[NBIT-1:0] > CNT1 ) ;
   assign #1 F = (GO && !EXP) || ((CNT >0) && (CNT < CNT1) && !EXP) ;

endmodule // ARV_CONT_REP_EXP

module ARV_CONT_REP_SEQ( Clk, RN, E, C, GO, SGO, SB, SM, M, F, B ) ;
   parameter NBIT = 2 ;   
   parameter CNT1 = 1 ;
   parameter CNT2 = 2 ;
   input Clk ;
   input RN ;
   input E ;
   input C ;
   input GO ;
   output SGO ;
   input  SB ;
   input  SM ;
   output M ;
   output F ;
   output B ;

   reg 	 [NBIT-1:0] CNT ;
   reg    BSY ;

   always @ ( negedge RN or posedge Clk ) begin 
     if( !RN || C || !E ) begin
	CNT <= 0 ;
	BSY <= 0 ;
     end
     else begin
       if( !BSY ) begin
	  if( GO ) BSY <= 1 ;
       end
       else begin
	 if( !SB ) begin
	    BSY <= 0 ;
	    CNT <= 0 ;
	 end
	 else begin
	    if( SM ) begin
	       if( CNT < CNT2 ) begin
		  CNT <= CNT + 1 ;
	       end
	       else begin
		  BSY <= 0 ;
		  CNT <= 0 ;
	       end
	    end
	 end // else: !if( !SB )
       end // else: !if( !BSY )
     end // else: !if( !RN || C || !E )
   end // always @ ( RN or C or E or posedge Clk )
   
   assign #1 B = BSY ;
   assign #1 SGO = 
       (!BSY && GO && RN && !C && E ) || (BSY && SM && (CNT != (CNT2-1)) ) ;
   assign #1 M = ( CNT > CNT1 ) ;
   assign #1 F = (BSY && !SB) ;

endmodule // ARV_CONT_REP_SEQ
					  
					  
// Operand of GOTO REP must be expression 
module ARV_GOTO_REP( Clk, RN, E, C, GO, EXP, M, B ) ;
   parameter NBIT = 2 ;   
   parameter CNT1 = 1 ;
   parameter CNT2 = 2 ;
   input Clk ;
   input RN ;
   input E ;
   input C ;
   input GO ;
   input EXP ;
   output M ;
   output B ;

   reg 	 [NBIT-1:0]  CNT;
   reg 	  BSY ;

   always @ ( negedge RN or posedge Clk ) begin 
     if( !RN || C || !E ) begin
	CNT <= 0 ;
     end
     else begin
	if( !BSY ) begin
	   if( GO ) BSY <= 1 ;
	end
	else begin
	   if( EXP ) begin
	      if( CNT < CNT2 ) begin
		 CNT <= CNT + 1 ;
	      end
	      else begin
		 CNT <= 0 ;
		 BSY <= 0 ;
	      end
	   end
	end // else: !if( !BSY )
     end // else: !if( !RN || C || !E )
   end // always @ ( RN or C or E or posedge Clk )

   assign #1 B = BSY ;
   assign #1 M = ( CNT > CNT1 ) && EXP ;

endmodule // ARV_CONT_REP_EXP
