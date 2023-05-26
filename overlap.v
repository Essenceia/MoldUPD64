/* Copyright (c) 2023, Julia Desmazes. All rights reserved.
 * 
 * This work is licensed under the Creative Commons Attribution-NonCommercial
 * 4.0 International License. 
 * 
 * This code is provided "as is" without any express or implied warranties.
 * 
 * For purchasing a commertial license contact : julia.desmazes@gmail.com  */ 


// Overlap detector
// Detects if the next axi payload will overlap over 2 moldupd64
// messages
module overlap_det #(
	parameter P_L  = 8, // Payload length in bytes
	parameter M_LW = 8  // Data width in bits for the number of bytes left on
						// current message
)(
	input [ML_W-1:0] msg_len_i,

	output           msg_overlap_o // next axi payload contains 2 msg
);
localparam P_L_LOG2 = $clog2( P_L );
logic [ML_W-1:P_L_LOG2] len_msb;
logic [P_L_LOG2-1:0]    len_lsb;
logic                   msg_last_payload; // last part of the msg is in the next payload
logic                   msg_ends_inside; // msg ends within the next payload 

// 
assign {len_msb , len_lsb } = msg_len_i;

assign msg_last_payload = ~|len_msb; 
assign msg_ends_inside  = ~|len_lsb;

assign msg_overlap_o = msg_last_payload & msg_ends_inside;

`ifdef FORMAL

logic msg_last_f;
logic msg_ends_inside_f;
logic overlap_f;
assign msg_last_f = msg_len_i <= P_L;
assign msg_ends_inside_f =  msg_len_i % P_L ;
assign overlap_f = msg_last_f & msg_ends_inside_f;

always_comb begin
	sva_overlap : assert ( overlap_f == msg_overlap_o );
end
`endif
endmodule
