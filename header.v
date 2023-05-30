/* Copyright (c) 2023, Julia Desmazes. All rights reserved.
 * 
 * This work is licensed under the Creative Commons Attribution-NonCommercial
 * 4.0 International License. 
 * 
 * This code is provided "as is" without any express or implied warranties. */ 


module header(
	input [63:0]    data_i,
	input           h0_v_i, // first 64 bits of the header
	input           h1_v_i, // second 64 bits
	input           h2_v_i, // last 32 bits of the header

	// session id, spread over 2 parts
	output logic        sid_p0_v_o, 
	output logic [63:0] sid_p0_o,
	output logic        sid_p1_v_o,	 
	output logic [15:0] sid_p1_o,
	// sequence number	   
	output logic        seq_num_p0_v_o,
	output logic [47:0] seq_num_p0_o,
	output logic        seq_num_p1_v_o,
	output logic [15:0] seq_num_p1_o,
	// message cnt
	output logic        msg_cnt_v_o,
	output logic [15:0] msg_cnt_o 

);

assign sid_p0_v_o   = h0_v_i;
assign sid_p0_o     = data_i[63:0];
assign sid_p1_v_o   = h1_v_i;
assign sid_p1_o     = data_i[15:0];

assign seq_num_p0_v_o = h1_v_i;
assign seq_num_p0_o   = data_i[63:16];
assign seq_num_p1_v_o = h2_v_i;
assign seq_num_p1_o   = data_i[15:0];

assign msg_cnt_v_o = h2_v_i;
assign msg_cnt_o   = data_i[31:16];

`ifdef FORMAL

logic [2:0] h_v_f; 
assign h_v_f = { h0_v_i, h1_v_i, h2_v_i };

always_comb begin
	// assert
	// no overlapping header decode step
	sva_h_v_i_onehot0 : assert ( $onehot0( h_v_f ));

	// xcheck
	// validity bit is never x
	sva_xcheck_sid_p0_v_o : assert ( ~$isunknown( sid_p0_v_o ) );
	sva_xcheck_sid_p1_v_o : assert ( ~$isunknown( sid_p1_v_o ) );
	sva_xcheck_seq_num_p0_v_o : assert ( ~$isunknown( seq_num_p0_v_o ) );
	sva_xcheck_seq_num_p1_v_o : assert ( ~$isunknown( seq_num_p1_v_o ) );
	sva_xcheck_msg_cnt_v_o : assert ( ~$isunknown( msg_cnt_o ));
	// if output is valid, data is known 
	sva_xcheck_sid_p0_o : assert ( ~sid_p0_v_o | ( sid_p0_v_o & ~$isunknown( sid_p0_o )));
	sva_xcheck_sid_p1_o : assert ( ~sid_p1_v_o | ( sid_p1_v_o & ~$isunknown( sid_p1_o )));
	sva_xcheck_seq_num_p0_o : assert ( ~seq_num_p0_v_o | ( seq_num_p0_v_o & ~$isunknown( seq_num_p0_o )));
	sva_xcheck_seq_num_p1_o : assert ( ~seq_num_p1_v_o | ( seq_num_p1_v_o & ~$isunknown( seq_num_p1_o )));
	sva_xcheck_msg_cnt_o : assert ( ~msg_cnt_v_o | ( msg_cnt_v_o & ~$isunknown( msg_cnt_o )));

	// cover
	c_invalid_i : cover ( ~|h_v_f );
	c_h0_v_i : cover ( h0_v_i );
	c_h1_v_i : cover ( h1_v_i );
	c_h2_v_i : cover ( h2_v_i );

end
`endif
endmodule
