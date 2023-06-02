/* Copyright (c) 2023, Julia Desmazes. All rights reserved.
 * 
 * This work is licensed under the Creative Commons Attribution-NonCommercial
 * 4.0 International License. 
 * 
 * This code is provided "as is" without any express or implied warranties. */ 

/* Missing packet detection logic using mold sequence number.
 * Compare gotten sequence number to next expected sequence number and detect
 * if there are missing packets.
 * Also keeps track of session id's in case our misses spread over different
 * sessions. These cases are driven through a different interface as
 * retransmission requests can only be performed on a specific session, so
 * when our miss overlaps multiple sessions we will need to make multiple
 * requests.
 * 
 * In case of a session id overflow session id will wrap back to 0, when this
 * happens, in order to not identify a late packet ( with a now much higher 
 * session id ) as the sign we have missed many packets we have a maximum
 * session id gap `SID_GAP_MAX` over which we not detect the miss.
 *
 * Limitations :
 * - We assume sequence numbers are seen in increasing order and only keep
 *   track of the highest session/seq num. */
module miss_msg_det #(
	parameter SEQ_NUM_W = 64,
	parameter SID_W     = 80,
	parameter ML_W      = 16,
	parameter SID_GAP_MAX = { 1'b1, {SEQ_NUM_W-1{1'b0}} }	
)(
	input clk,
	input nreset,

	input                 v_i,
	input [SID_W-1:0]     sid_i,
	input [SEQ_NUM_W-1:0] seq_num_i,
	input [ML_W-1:0]      msg_cnt_i,
	input                 eos_i, // end of session
 
	// missing sequence numbers of the same sid
	output logic                 miss_seq_num_v_o,
	output logic [SID_W-1:0]     miss_seq_num_sid_o,
	output logic [SEQ_NUM_W-1:0] miss_seq_num_start_o,	
	output logic [SEQ_NUM_W-1:0] miss_seq_num_cnt_o,
	// missing entire session's
	output logic                 miss_sid_v_o,
	output logic [SID_W-1:0]     miss_sid_start_o,
	output logic [SEQ_NUM_W-1:0] miss_sid_seq_num_start_o,
	output logic [SID_W-1:0]     miss_sid_cnt_o,
	output logic [SEQ_NUM_W-1:0] miss_sid_seq_num_end_o

);
reg   [SID_W-1:0] sid_q;
logic [SID_W-1:0] sid_next;
logic [SID_W-1:0] sid_add;
logic             sid_add_v;
logic             sid_add_overflow;
logic             sid_loop;
logic             sid_lt;
logic             sid_gap_v;
logic [SID_W-1:0] sid_gap;
logic             sid_match;

reg   [SEQ_NUM_W-1:0] seq_q;
logic [SEQ_NUM_W-1:0] seq_next;
logic [SEQ_NUM_W-1:0] seq_add;
logic                 seq_add_overflow;
logic                 seq_add_v;
logic                 seq_gap_v;
logic [SEQ_NUM_W-1:0] seq_gap;
logic [SEQ_NUM_W-1:0] seq_gap_add;
logic                 seq_gap_add_overflow;
logic                 seq_lt; // got seq num is less than our next expected number

logic [ML_W:0] msg_cnt_add_one;

// Session id
assign { sid_add_overflow, sid_add } = sid_q + { {SID_W-1{1'b0}}, 1'b1};
assign sid_add_v = eos_i;
assign sid_gap   = sid_i - sid_q;
assign sid_gap_v = sid_gap < SID_GAP_MAX;  
assign sid_lt    = sid_gap_v & ( sid_q < sid_i );
assign sid_next  = sid_add_v ? sid_add : 
				   sid_lt ? sid_i : sid_q;

always @(posedge clk) begin
	if ( ~nreset ) begin
		sid_q <= {SID_W{1'b0}};
	end else if ( v_i ) begin
		sid_q <= sid_next;
	end
end

assign miss_sid_v_o     = sid_lt & v_i;
assign miss_sid_start_o = sid_q;
assign miss_sid_cnt_o   = seq_gap;
assign miss_sid_seq_num_start_o = seq_q;
assign miss_sid_seq_num_end_o   = 'X;// seq_dec;

// Sequence number
// Increment by 1 so we see the next expected sequence number ( even on heartbeat ) 
assign msg_cnt_add_one = msg_cnt_i + {{ML_W-1{1'b0}}, 1'b1}; 
assign { seq_add_overflow,     seq_add     } = seq_q     + { {SEQ_NUM_W-ML_W-1{1'b0}}, msg_cnt_add_one };
assign { seq_gap_add_overflow, seq_gap_add } = seq_num_i + { {SEQ_NUM_W-ML_W-1{1'b0}}, msg_cnt_add_one }; 
// TODO : Support when message sequence overlap and the gap is only partial
assign sid_match = sid_q == sid_i;
assign seq_gap   = seq_num_i - seq_q;
assign seq_lt    = seq_q < seq_num_i;
assign seq_gap_v = seq_lt & v_i;  

assign seq_next = eos_i ? '0 : seq_gap_v ? seq_gap_add : seq_add;

always @(posedge clk) begin
	if ( ~nreset ) begin
		seq_q <= '0;
	end else if( v_i ) begin
		seq_q <= seq_next;
	end
end

assign miss_seq_num_v_o     = seq_gap_v & sid_match;
assign miss_seq_num_sid_o   = sid_q;
assign miss_seq_num_start_o = seq_q;
assign miss_seq_num_cnt_o   = seq_gap; 

`ifdef FORMAL 

initial begin
	a_reset : assume ( ~nreset );
end

always @(posedge clk) begin
	if ( nreset ) begin
	// assume
	// input message cnt 
	a_no_overflow_msg_cnt : assume( v_i & ~seq_gap_add_overflow);	// assert
	// x check 
	sva_xcheck_v_i : assert( ~$isunknown( v_i ));
	sva_xcheck_data_i : assert ( ~ v_i | ( v_i & ~$isunknown( |sid_i | |seq_num_i | |msg_cnt_i | oes_i) ));
	sva_xcheck_seq_num_v : assert ( ~$isunknown(miss_seq_num_v_o));  
	sva_xcheck_seq_num_data_o : assert ( ~miss_seq_num_v_o | 
		( miss_seq_num_v_o & $isunknown( |miss_seq_num_sid_o | |miss_seq_num_start_o | |miss_seq_num_cnt_o ) ));  
	sva_xcheck_sid_v : assert ( ~$isunknown(miss_sid_v_o)); 
	sva_xcheck_sid_data_o : assert ( ~miss_sid_v_o |
		( miss_sid_v_o & ($isunknown( |miss_sid_start_o | |miss_sid_seq_num_start_o | |miss_sid_cnt_o | |miss_sid_seq_num_end_o )) )); 
	// cover
	c_reset : cover ( ~nreset );
	c_sid_overflow : cover ( sid_add_overflow );
	end
end
`endif // FORMAL 
endmodule
