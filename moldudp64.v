/* Copyright (c) 2023, Julia Desmazes. All rights reserved.
 * 
 * This work is licensed under the Creative Commons Attribution-NonCommercial
 * 4.0 International License. 
 * 
 * This code is provided "as is" without any express or implied warranties. */ 


/* Module is a slave connected to an AXI steam interface */

// make sure shared logic is defined
`ifdef DEBUG_ID
`define _INC_MOLD_IDS
`elsif MOLD_MSG_IDS
`define _INC_MOLD_IDS
`endif

module moldudp64 #(

	parameter AXI_DATA_W  = 64,
	parameter AXI_KEEP_W  = 8,
	parameter SID_W       = 80,
	parameter SEQ_NUM_W   = 64,
	`ifdef DEBUG_ID
	parameter DEBUG_ID_W  = SID_W + SEQ_NUM_W,
	`endif	
	`ifdef NUKE
	parameter NUKE_ID_W   = 10,
	`endif	
	parameter ML_W        = 16, // Mold length field width in bits
	parameter EOS_MSG_CNT = {ML_W{1'b1}},// end-of-session msg cnt value

	// overlap fields
	parameter OV_DATA_W  = 64-ML_W,//48
	parameter OV_KEEP_W  = (OV_DATA_W/8),//6
	parameter OV_KEEP_LW = 3 //$clog2(OV_KEEP_W+1),
)(
	input clk,
	input nreset,
	
	// AXI stream interface from udp ethernet
	input                  udp_axis_tvalid_i,
	input [AXI_KEEP_W-1:0] udp_axis_tkeep_i,
	input [AXI_DATA_W-1:0] udp_axis_tdata_i,
	input                  udp_axis_tlast_i,
	input                  udp_axis_tuser_i,
	
	output                 udp_axis_tready_o,

	`ifdef MISS_DET
	// missing mold message detection

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
	output logic [SEQ_NUM_W-1:0] miss_sid_seq_num_end_o,	
	`endif // MISS_DET	
	
	`ifdef HEARTBEAT
	output logic            flatlined_v_o,
	`endif

	`ifdef MOLD_MSG_IDS	
	output [SID_W-1:0]      mold_msg_sid_o,
	output [SEQ_NUM_W-1:0]  mold_msg_seq_num_o,
	`endif
	`ifdef DEBUG_ID
	// no input debug id as it is constructed out of the seq
	// and sid numbers
	output [DEBUG_ID_W-1:0]  mold_msg_debug_id_o,
	`endif
	output                   mold_msg_v_o,
	output                   mold_msg_start_o, // start of a new msg
	output [AXI_KEEP_LW-1:0] mold_msg_len_o,
	output [AXI_DATA_W-1:0]  mold_msg_data_o, 

	// overlap
	output                   mold_msg_ov_v_o,
	output                   mold_msg_ov_start_o, // start of a new msg
	output [OV_KEEP_LW-1:0]  mold_msg_ov_len_o,
	output [OV_DATA_W-1:0]   mold_msg_ov_data_o
);
localparam AXI_MSG_L   = $clog2( AXI_DATA_W / 8 );
localparam AXI_KEEP_LW = $clog2( AXI_KEEP_W ) + 1;
localparam DFF_DATA_W  = AXI_DATA_W - 8; // 56
localparam DFF_DATA_LW = $clog2( DFF_DATA_W ); // 7 
localparam DATA_DIF_W  = AXI_DATA_W - DFF_DATA_W; // 8

// header data
reg   [SID_W-1:0]     sid_q;
logic [SID_W-1:0]     sid_next;

`ifdef _INC_MOLD_IDS
reg   [SEQ_NUM_W-1:0] seq;
reg   [SEQ_NUM_W-1:0] seq_q;
logic [SEQ_NUM_W-1:0] seq_next;
logic [SEQ_NUM_W-1:0] seq_add;
logic                 seq_add_overflow;
logic                 seq_msb_en;
logic                 seq_lsb_en;
logic                 seq_en;
`else
reg   [63:16]         seq_q;
`endif
logic        init_sid_p0_v; 
logic [15:0] init_sid_p0;
logic        init_sid_p1_v;
logic [63:0] init_sid_p1;
logic        init_seq_num_p0_v;
logic [15:0] init_seq_num_p0;
logic        init_seq_num_p1_v;
logic [47:0] init_seq_num_p1;
	
// metadata
logic            msg_end_v;
logic            pkt_end_v;
reg   [ML_W-1:0] msg_cnt_q;
logic [ML_W-1:0] msg_cnt_next;
logic            msg_cnt_dec_v;
logic [ML_W-1:0] msg_cnt_dec;
logic            init_msg_cnt_v;
logic [ML_W-1:0] init_msg_cnt;
logic            init_eos;// end of session
logic            cnt_en;
logic            cnt_end;
logic            cnt_end_next;

// FSM
reg   fsm_invalid_q;
logic fsm_invalid_next;
logic h0_v;
reg   fsm_h1_q;
reg   fsm_h2_q;
logic fsm_h1_next;
logic fsm_h2_next;
reg   fsm_msg_q;
logic fsm_msg_next;

// Header
header m_header(
	.data_i(udp_axis_tdata_i),
	.h0_v_i(h0_v),
	.h1_v_i(fsm_h1_q),
	.h2_v_i(fsm_h2_q),

	.sid_p0_v_o(init_sid_p0_v), 
	.sid_p0_o  (init_sid_p0),
	.sid_p1_v_o(init_sid_p1_v),
	.sid_p1_o  (init_sid_p1),
	.seq_p0_v_o(init_seq_num_p0_v),
	.seq_p0_o  (init_seq_num_p0),
	.seq_p1_v_o(init_seq_num_p1_v),
	.seq_p1_o  (init_seq_num_p1),
	.msg_cnt_v_o(init_msg_cnt_v),
	.msg_cnt_o  (init_msg_cnt)
);
// sid
always @(posedge clk) begin
	if( init_sid_p0_v )
		sid_q[15:0] <= init_sid_p0;
	if( init_sid_p1_v ) 
		sid_q[79:16] <= init_sid_p1;
end
// seq
`ifdef _INC_MOLD_IDS
assign { seq_add_overflow, seq_add } = seq_q + {{SEQ_NUM_W-1{1'b0}}, 1'b1};
assign seq_next[15:0]  = init_seq_num_p0_v ? init_seq_num_p0 : seq_add[15:0];
assign seq_next[63:16] = init_seq_num_p1_v ? init_seq_num_p1 : seq_add[63:16];
// recreate seq on init cycle
assign seq = { seq_q[63:16] , init_seq_num_p0_v? init_seq_num_p0 : seq_q[15:0] }; 

assign seq_en     = msg_end_v;
assign seq_msb_en = seq_en | init_seq_num_p1_v;
assign seq_lsb_en = seq_en | init_seq_num_p0_v;

always @(posedge clk) begin
	if( seq_lsb_en )
		seq_q[15:0] <= seq_next[15:0];
	if( seq_msb_en ) 
		seq_q[63:16] <= seq_next[63:16];
end
`else
always @(posedge clk) begin
	if( init_seq_num_p0_v )
		seq_q[63:16] <= init_seq_num_p1;
end
`endif

// decrement the number of messages we are still expected to see if we have
// reaced the end of the current message
assign msg_cnt_dec   = msg_cnt_q - { {ML_W-1{1'b0}}, 1'b1 };
// when half of the next length is in flop length's update will be delayed
// by 1 cycle, we should not consider this a message end 
assign msg_cnt_dec_v = msg_end_v & ~cnt_end;
 
assign msg_cnt_next = init_msg_cnt_v ? init_msg_cnt :
					  msg_cnt_dec_v  ? msg_cnt_dec : msg_cnt_q;
assign cnt_end_next = ~|msg_cnt_next;
assign cnt_end = ~|msg_cnt_q;
assign cnt_en = init_msg_cnt_v | msg_end_v;
always @(posedge clk) begin
	if ( ~nreset ) begin
		msg_cnt_q <= '0;
	end if ( cnt_en ) begin
		msg_cnt_q <= msg_cnt_next;	
	end
end
// End-Of-Session 
assign init_eos = init_msg_cnt == EOS_MSG_CNT;

`ifdef MISS_DET
// check for missed sequences
miss_msg_det #(
	.SEQ_NUM_W(SEQ_NUM_W),
	.SID_W(SID_W),
	.ML_W(ML_W)
) m_miss_det(
	.clk(clk),
	.nreset(nreset),

	.v_i      (fsm_h2_q                      ),
	.sid_i    (sid_q                         ),
	.seq_num_i({seq_q[63:16], init_seq_num_p0}),
	.msg_cnt_i(init_msg_cnt                  ),
	.eos_i    (init_eos                      ), // end of session
 
	// missing sequence numbers of the same sid
	.miss_seq_num_v_o    (miss_seq_num_v_o    ),
	.miss_seq_num_sid_o  (miss_seq_num_sid_o  ),
	.miss_seq_num_start_o(miss_seq_num_start_o),	
	.miss_seq_num_cnt_o  (miss_seq_num_cnt_o  ),
		
	// missing entire session's
	.miss_sid_v_o            (miss_sid_v_o            ),
	.miss_sid_start_o        (miss_sid_start_o        ),
	.miss_sid_seq_num_start_o(miss_sid_seq_num_start_o),
	.miss_sid_cnt_o          (miss_sid_cnt_o          ),
	.miss_sid_seq_num_end_o  (miss_sid_seq_num_end_o  )
);
`endif

`ifdef HEARTBEAT
	// check if server is still alive
	countdown #() m_cntdwn(
		.clk(clk),
		.nreset(nreset),

		.start_v_i (h0_v     ),
		.finished_o(flatlined_v_o)
	);
`endif
// message and sequence tracking
dispatch #(
	.AXI_DATA_W(AXI_DATA_W),
	.AXI_KEEP_W(AXI_KEEP_W),
	.KEEP_LW(AXI_KEEP_LW),
	.LEN_W(ML_W),
	.OV_DATA_W(OV_DATA_W), 
	.OV_KEEP_W(OV_KEEP_W),
	.OV_KEEP_LW(OV_KEEP_LW),
	.HEADER_DATA_OFF(6)
) m_mold_data_dispatch(
	.clk(clk),
	.nreset(nreset),

	.valid_i(udp_axis_tvalid_i),
	.data_i(udp_axis_tdata_i),
	.keep_i(udp_axis_tkeep_i),
	.init_v_i(fsm_h2_q),
	.last_i(udp_axis_tlast_i),

	.msg_end_v_o(msg_end_v),

	.valid_o(mold_msg_v_o),
	.start_o(mold_msg_start_o),
	.data_o(mold_msg_data_o),
	.len_o(mold_msg_len_o),

	.ov_valid_o(mold_msg_ov_v_o),
	.ov_start_o(mold_msg_ov_start_o),
	.ov_data_o (mold_msg_ov_data_o),
	.ov_len_o  (mold_msg_ov_len_o)
);
// fsm
logic tlast_q;
always @(posedge clk) begin
	if ( ~nreset ) begin
		tlast_q <= 1'b0;
	end else begin
		tlast_q <= udp_axis_tlast_i;
	end
end
assign fsm_invalid_next = udp_axis_tvalid_i
						& ( udp_axis_tlast_i | ( cnt_end & ~(h0_v | fsm_h1_q | fsm_h2_q) ))
						| ( fsm_invalid_q & ~udp_axis_tvalid_i);
assign h0_v            = udp_axis_tvalid_i & ( fsm_invalid_q | tlast_q ) ;
assign fsm_h1_next  = h0_v;
assign fsm_h2_next  = fsm_h1_q & udp_axis_tvalid_i;
assign fsm_msg_next = fsm_h2_q 
                    | fsm_msg_q & ~(cnt_end | udp_axis_tlast_i); 
always @(posedge clk) begin
	if ( ~nreset ) begin
		fsm_invalid_q <= 1'b1;
		fsm_h1_q      <= 1'b0;
		fsm_h2_q      <= 1'b0;
		fsm_msg_q     <= 1'b0;
	end else begin
		fsm_invalid_q <=fsm_invalid_next;
		fsm_h1_q      <=fsm_h1_next;
		fsm_h2_q      <=fsm_h2_next;
		fsm_msg_q     <=fsm_msg_next;
	end
end
// output
assign udp_axis_tready_o  = 1'b1; // no backpresure 

`ifdef MOLD_MSG_IDS
assign mold_msg_sid_o     = sid_q;
assign mold_msg_seq_num_o = seq;
`endif

`ifdef DEBUG_ID
assign mold_msg_debug_id_o = { sid_q , seq };
`endif

`ifdef FORMAL

logic [4:0] fsm_f;
assign fsm_f = {
	fsm_invalid_q, 
	fsm_h0_q, fsm_h1_q, fsm_h2_msg_q,
	fsm_msg_q };

initial begin
	// assume
	a_reset : assume ( ~nreset );
	
end

always @(posedge clk) begin
	if ( nreset ) begin
		// assume
		// AXI valid is never X
		a_axi_tvalid_know : assume ( ~$isunknown( udp_axis_tvalid_i ));
		// AXI doesn't drive X's when valid
		a_axi_valid_tdata_known : assume( ~udp_axis_tvalid_i | ( udp_axis_tvalid_i &  ~$isunknown( udp_axis_tdata_i )));
		a_axi_valid_tkeep_known : assume( ~udp_axis_tvalid_i | ( udp_axis_tvalid_i &  ~$isunknown( udp_axis_tkeep_i )));
		a_axi_valid_tlast_known : assume( ~udp_axis_tvalid_i | ( udp_axis_tvalid_i &  ~$isunknown( udp_axis_tlast_i )));
		a_axi_valid_tuser_known : assume( ~udp_axis_tvalid_i | ( udp_axis_tvalid_i &  ~$isunknown( udp_axis_tuser_i )));
		// tkeep is a thermometer
		a_axi_tkeep_thermo : assume( ~udp_axis_tvalid_i | ( udp_axis_tvalid_i & $onehot0( udp_axis_tkeep_i - AXI_KEEP_W'd1 ))); 
		// tkeep is only not only 1s on the last payload
		a_axi_tkeep_n1s_only_tlast : assume ( ~udp_axis_tvalid_i | ( udp_axis_tvalid_i & ~udp_axis_tlast_i & &udp_axis_tkeep_i ));
		
		// backpresure should only last 1 cycle 
		sva_backpresure_max_1_cycle : assert ( udp_axis_tready_o | ( $past(udp_axis_tready_o, 1 ) & ~udp_axis_tready_o ));	
	
		// msg length lite incremented by 2 should never overlow when used
		sva_msg_len_lite_inc_2_overflow : assert( ~fsm_msg_len_flop_q | ( fsm_msg_len_flop_q & ~msg_len_lite_inc_2_overflow ));
	
		// fsm
		sva_fsm_onehot : assert( $onehot( fsm_f )); 
		
		// msg cnt init should happen when we receive the last part of the
		// header
		sva_msg_cnt_init_h2 : assert ( init_msg_cnt_v == fsm_h2_msg_q);
		sva_xcheck_msg_cnt : assert ( ~|fsm_f[7:4] | ( |fsm_f[7:4] & ~$isunknown( msg_cnt_q )));

		// flop shift
		// there should not exist a senario were the flop is shifted entriely
		// into the output message, flop shift is designed to hold a max of
		// 56 bits, not the full 64
		sva_flop_holds_partial_msg : assert ( ~msg_v | ( msg_v & ~flop_msg_mask[AXI_KEEP_W-1] ));

		// no msg_end on h1 of header, would break seq_next mux logic
		sva_header_msg_end_zero : assert ( ~fsm_h1_q  | (  fsm_h1_q  & ~msg_end ));

	end
end
`endif
endmodule
