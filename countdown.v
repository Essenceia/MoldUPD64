/* Copyright (c) 2023, Julia Desmazes. All rights reserved.
 * 
 * This work is licensed under the Creative Commons Attribution-NonCommercial
 * 4.0 International License. 
 * 
 * This code is provided "as is" without any express or implied warranties. */ 


/* Countdown */
module countdown #(
	parameter CNT = 10000,
	parameter CNT_W = 14, // cnt log2
	parameter CNT_B = CNT_W'b10011100010000 // cnt in a binary format
)(
	input clk,
	input nreset,

	input        start_v_i, // restart countdown
	output logic finished_o
);
reg   [CNT_W-1:0] cnt_q;
logic [CNT_W-1:0] cnt_next;
logic             zero;

assign zero     = ~|cnt_q; 
assign cnt_next = start_v_i ? CNT_B :
					zero ? '0 : cnt_q - CNT_W'd1;
always @(posedge clk)
begin
	if (~nreset ) begin
		cnt_q <= CNT_B;
	end else begin
		cnt_q <= cnt_next;
	end
end

// output 
assign finished_o = zero;

`ifdef FORMAL


always @(posedge clk) 
begin
	// assert
	
	// parameter
	sva_cnt_start_nzero : assert ( CNT > 0);

	sva_cnt_stay_zero : assert ( start_v_i| ~zero | ( ~start_v_i & zero & ( cnt_next == {CNT_W{1'b0}} )));
	sva_cnt_dec : assert( (start_v_i | zero ) | (cnt_next == ( cnt_q - 1)));

	// cover
	c_zero : cover ( zero );
	c_finished : cover ( finished_o );
end	

`endif
endmodule
