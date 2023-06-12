/* Copyright (c) 2023, Julia Desmazes. All rights reserved.
 * 
 * This work is licensed under the Creative Commons Attribution-NonCommercial
 * 4.0 International License. 
 * 
 * This code is provided "as is" without any express or implied warranties. */ 

/* Extra's infomation out of the packet header and 
 * retuns it in little endian.
 */
module header(
	input [63:0]    data_i,
	input           h0_v_i, // first 64 bits of the header
	input           h1_v_i, // second 64 bits
	input           h2_v_i, // last 32 bits of the header

	// session id, spread over 2 parts
	output logic        sid_p0_v_o, 
	output logic [15:0] sid_p0_o,
	output logic        sid_p1_v_o,	 
	output logic [63:0] sid_p1_o,
	// sequence number	   
	output logic        seq_p0_v_o,
	output logic [15:0] seq_p0_o,
	output logic        seq_p1_v_o,
	output logic [47:0] seq_p1_o,
	// message cnt
	output logic        msg_cnt_v_o,
	output logic [15:0] msg_cnt_o 

);
/* sid [ 7:0 ]
 * seq [ 7:2 ] sid [ 1:0 ]
 *   x [ 7:4 ] cnt [ 3:2 ] seq [ 1:0 ]
 */
/* convert from big endian to littlen endian
 * be  : 9 8 7 6 5 4 3 2 1 0
 * le  : 0 1 2 3 4 5 6 7 8 9
 * pkt : 1 1 0 0 0 0 0 0 0 0
 */
assign sid_p0_v_o = h1_v_i;
endian_flip #(.B(2)) m_ef_sid_p0( 
	.d_i(data_i[15:0]),
	.d_o(sid_p0_o)
);
assign sid_p1_v_o = h0_v_i;
endian_flip #(.B(8)) m_ef_sid_p1( 
	.d_i(data_i),
	.d_o(sid_p1_o)
);
/* convert from big endian to littlen endian
 * be  : 7 6 5 4 3 2 1 0
 * le  : 0 1 2 3 4 5 6 7
 * pkt : 1 1 0 0 0 0 0 0
 */
assign seq_p0_v_o = h2_v_i;
endian_flip #(.B(2)) m_ef_seq_p0(
	.d_i(data_i[15:0]),
	.d_o(seq_p0_o)
);

assign seq_p1_v_o = h1_v_i;
endian_flip #(.B(6)) m_ef_seq_p1(
	.d_i(data_i[63:16]),
	.d_o(seq_p1_o)
);

assign msg_cnt_v_o = h2_v_i;
endian_flip #(.B(2)) m_ef_msg_cnt(
	.d_i(data_i[31:16]),
	.d_o(msg_cnt_o)
);
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
	sva_xcheck_seq_p0_v_o : assert ( ~$isunknown( seq_p0_v_o ) );
	sva_xcheck_seq_p1_v_o : assert ( ~$isunknown( seq_p1_v_o ) );
	sva_xcheck_msg_cnt_v_o : assert ( ~$isunknown( msg_cnt_o ));
	// if output is valid, data is known 
	sva_xcheck_sid_p0_o : assert ( ~sid_p0_v_o | ( sid_p0_v_o & ~$isunknown( sid_p0_o )));
	sva_xcheck_sid_p1_o : assert ( ~sid_p1_v_o | ( sid_p1_v_o & ~$isunknown( sid_p1_o )));
	sva_xcheck_seq_p0_o : assert ( ~seq_p0_v_o | ( seq_p0_v_o & ~$isunknown( seq_p0_o )));
	sva_xcheck_seq_p1_o : assert ( ~seq_p1_v_o | ( seq_p1_v_o & ~$isunknown( seq_p1_o )));
	sva_xcheck_msg_cnt_o : assert ( ~msg_cnt_v_o | ( msg_cnt_v_o & ~$isunknown( msg_cnt_o )));

	// cover
	c_invalid_i : cover ( ~|h_v_f );
	c_h0_v_i : cover ( h0_v_i );
	c_h1_v_i : cover ( h1_v_i );
	c_h2_v_i : cover ( h2_v_i );

end
`endif
endmodule
