/* Copyright (c) 2023, Julia Desmazes. All rights reserved.
 * 
 * This work is licensed under the Creative Commons Attribution-NonCommercial
 * 4.0 International License. 
 * 
 * This code is provided "as is" without any express or implied warranties. */ 


/* Module is a slave connected to an AXI steam interface */

module top #(
	parameter AXI_DATA_W  = 64,
	parameter AXI_KEEP_W  = 8,
	parameter SID_W       = 80,
	parameter SEQ_NUM_W   = 64,
	parameter ML_W        = 16, // Mold length field width in bits
	parameter EOS_MSG_CNT = {ML_W{1'b1}} // end-of-session msg cnt value
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
	output [SEQ_NUM_W-1:0]  mold_msg_seq_num_o,// Mold message
	`endif

	output                  mold_msg_v_o,
	output                  mold_msg_start_o, // start of a new msg
	output [AXI_KEEP_W-1:0] mold_msg_mask_o,
	output [AXI_DATA_W-1:0] mold_msg_data_o

);
localparam AXI_MSG_L   = $clog2( AXI_DATA_W / 8 );
localparam AXI_KEEP_LW = $clog2( AXI_KEEP_W ) + 1;
localparam DFF_DATA_W  = AXI_DATA_W - 8; // 56
localparam DFF_DATA_LW = $clog2( DFF_DATA_W ); // 7 
localparam DATA_DIF_W  = AXI_DATA_W - DFF_DATA_W; // 8

// header data
reg   [SID_W-1:0]     sid_q;
logic [SID_W-1:0]     sid_next;

`ifdef MOLD_MSG_IDS
reg   [SEQ_NUM_W-1:0] seq_q;
logic [SEQ_NUM_W-1:0] seq_next;
logic [SEQ_NUM_W-1:0] seq_add;
logic                 seq_add_overflow;
logic                 seq_msb_en;
logic                 seq_lsb_en;
logic                 seq_en;
`else
reg   [47:0]          seq_q;
logic [47:0]          seq_next;
`endif

logic        init_sid_p0_v; 
logic [63:0] init_sid_p0;
logic        init_sid_p1_v;
logic [15:0] init_sid_p1;
logic        init_seq_num_p0_v;
logic [47:0] init_seq_num_p0;
logic        init_seq_num_p1_v;
logic [15:0] init_seq_num_p1;
	
// metadata
reg   [ML_W-1:0] msg_cnt_q;
logic [ML_W-1:0] msg_cnt_next;
logic            init_msg_cnt_v;
logic [ML_W-1:0] init_msg_cnt;
logic            init_eos;// end of session
reg   [ML_W-1:0] msg_len_q;
logic [ML_W-1:0] msg_len_next;
logic [ML_W-1:0] init_msg_len;
logic            init_msg_len_v;

logic [AXI_KEEP_LW-1:0] udp_axis_data_len; 
logic [ML_W-1:0]        msg_len_dec;
logic [ML_W:0]          msg_len_got;
logic [AXI_KEEP_LW-1:0] msg_len_got_sat;// saturated version
logic                   msg_len_zero;
logic                   msg_end;
logic                   msg_end_align;
logic [AXI_KEEP_W-1:0]  msg_end_mask;                  
logic                   msg_overlap;
logic                   cnt_en;
logic                   cnt_end;
logic                   cnt_end_next;


logic                  msg_v;
logic [AXI_DATA_W-1:0] msg_data;

// data routing
// data shifted to be consumed next cycle
logic [DFF_DATA_W-1:0] flop_data_next;
logic [DFF_DATA_W-1:0] flop_data_q;

logic [AXI_KEEP_LW-1:0] flop_shift;
logic [AXI_KEEP_LW-1:0] len_shift;
logic [AXI_KEEP_LW-1:0] flop_len_next;
logic [AXI_KEEP_LW-1:0] flop_len_q;

logic [AXI_KEEP_W-1:0] axis_msg_mask;
logic [AXI_KEEP_W-1:0] flop_msg_mask;

logic [AXI_KEEP_LW-1:0] axis_msg_tdata_shift;
logic [AXI_KEEP_LW-1:0] axis_flop_tdata_shift;

// data shifted to be consumed in this cycle
logic [AXI_DATA_W-1:0] axis_msg_tdata_shifted;
// length
logic [7:0]       init_msg_len_p0;
logic [7:0]       init_msg_len_p0_q;// flopped in case of len cut over 2 payloads
logic [7:0]       init_msg_len_p1;

logic                   unused_msg_mask_int;
logic [AXI_KEEP_LW-1:0] msg_mask_int;
logic [AXI_KEEP_W-1:0]  msg_mask;

// FSM
reg   fsm_invalid_q;
logic fsm_invalid_next;
reg   fsm_h0_q;
reg   fsm_h1_q;
reg   fsm_h2_msg_q;
logic fsm_h0_next;
logic fsm_h1_next;
logic fsm_h2_msg_next;
reg   fsm_msg_q;
reg   fsm_msg_overlap_q;
reg   fsm_msg_len_split_q;
reg   fsm_msg_len_align_q;
logic fsm_msg_next;
logic fsm_msg_overlap_next;
logic fsm_msg_len_split_next;
logic fsm_msg_len_align_next;

// AXI 
reg [AXI_DATA_W-1:0]   udp_axis_tdata_q;
reg [AXI_KEEP_W-1:0]   udp_axis_tkeep_q;
reg                    udp_axis_tvalid_q;
reg                    udp_axis_tlast_q;
reg                    udp_axis_tuser_q;
logic [AXI_DATA_W-1:0] udp_axis_tdata_next;
logic [AXI_KEEP_W-1:0] udp_axis_tkeep_next;
logic                  udp_axis_tvalid_next;
logic                  udp_axis_tlast_next;
logic                  udp_axis_tuser_next;

// axi payload buffering ( for timing, might replace with clk domain crossing )
assign udp_axis_tdata_next  = udp_axis_tdata_i;  
assign udp_axis_tkeep_next  = udp_axis_tkeep_i;
assign udp_axis_tvalid_next = udp_axis_tvalid_i;
assign udp_axis_tlast_next  = udp_axis_tlast_i;
assign udp_axis_tuser_next  = udp_axis_tuser_i;

always @(posedge clk) 
begin
	if ( ~nreset ) begin
		udp_axis_tvalid_q  <= 1'b0;
	end else begin
		udp_axis_tdata_q   <= udp_axis_tdata_next; 	
		udp_axis_tkeep_q   <= udp_axis_tkeep_next;
		udp_axis_tvalid_q  <= udp_axis_tvalid_next;
		udp_axis_tlast_q   <= udp_axis_tlast_next;
		udp_axis_tuser_q   <= udp_axis_tuser_next;
	end
end
 
// Header
header m_header(
	.data_i(udp_axis_tdata_q),
	.h0_v_i(fsm_h0_q),
	.h1_v_i(fsm_h1_q),
	.h2_v_i(fsm_h2_msg_q),

	.sid_p0_v_o(init_sid_p0_v), 
	.sid_p0_o  (init_sid_p0),
	.sid_p1_v_o(init_sid_p1_v),
	.sid_p1_o  (init_sid_p1),
	.seq_num_p0_v_o(init_seq_num_p0_v),
	.seq_num_p0_o  (init_seq_num_p0),
	.seq_num_p1_v_o(init_seq_num_p1_v),
	.seq_num_p1_o  (init_seq_num_p1),
	.msg_cnt_v_o(init_msg_cnt_v),
	.msg_cnt_o  (init_msg_cnt)
);
// sid
always @(posedge clk) begin
	if( init_sid_p0_v )
		sid_q[63:0] <= init_sid_p0;
	if( init_sid_p1_v ) 
		sid_q[79:64] <= init_sid_p1;
end
// seq
`ifdef MOLD_MSG_IDS
assign { seq_add_overflow, seq_add } = seq_q + {{SEQ_NUM_W-1{1'b0}}, 1'b1};
assign seq_next[47:0]  = init_seq_num_p0_v ? init_seq_num_p0 : seq_add[47:0];
assign seq_next[63:48] = init_seq_num_p1_v ? init_seq_num_p1 : seq_add[63:48];

assign seq_en     = msg_end & msg_v;
assign seq_msb_en = seq_en | init_seq_num_p1_v;
assign seq_lsb_en = seq_en | init_seq_num_p0_v;

always @(posedge clk) begin
	if( seq_lsb_en )
		seq_q[47:0] <= seq_next[47:0];
	if( seq_msb_en ) 
		seq_q[63:48] <= seq_next[63:48];
end
`else
always @(posedge clk) begin
	if( init_seq_num_p0_v )
		seq_q[47:0] <= init_seq_num_p0;
end
`endif
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

	.v_i      (fsm_h2_msg_q                  ),
	.sid_i    (sid_q                         ),
	.seq_num_i({init_seq_num_p1, seq_q[47:0]}),
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

		.start_v_i   (fsm_h0_q   ),
		.finished_o(flatlined_v_o)
	);
`endif
// message and sequence tracking

// msg length based on tkeep
cnt_ones_thermo #(.D_W(AXI_KEEP_W),.D_LW(AXI_KEEP_LW))
	m_cnt_ones_tkeep(
	.data_i(udp_axis_tkeep_q),
	.cnt_o(udp_axis_data_len)
);

assign msg_v = fsm_msg_q | fsm_msg_overlap_q | fsm_msg_len_split_q;
// decrement the number of bytes of the current message that have been
// recieved ( ! not sent ) 
assign msg_len_zero  = ~|msg_len_q;
assign msg_end       = ~|msg_len_q[ML_W-1:AXI_KEEP_LW] & ( msg_len_q[AXI_KEEP_LW-1:0] <= (AXI_DATA_W/8));
assign msg_end_align = ~|msg_len_q[AXI_MSG_L-1:0] & ~|flop_shift; // msg end aligns with the end of the AXI payload
 
// init msg
assign init_msg_len_v = fsm_h2_msg_q 
			          | (msg_v & msg_end & ~msg_end_align & ~cnt_end )
					  | fsm_msg_len_split_q 
					  | fsm_msg_len_align_q; 
assign init_msg_len   = { ML_W{ fsm_h2_msg_q }} & ( udp_axis_tdata_q[32+ML_W-1:32] - 'd2 )// TODO : support 1st msg len=0
					  | { ML_W{ fsm_msg_q | fsm_msg_len_align_q }} &  { init_msg_len_p1, init_msg_len_p0 }
					  | { ML_W{ fsm_msg_len_split_q }} & { init_msg_len_p1 ,init_msg_len_p0_q} ;// len split over 2 axi payloads

assign msg_len_got     = ( {AXI_KEEP_LW{udp_axis_tvalid_q}} & udp_axis_data_len) + flop_len_q;
assign msg_len_got_sat = ( msg_len_got[3] ) ? {{AXI_KEEP_LW-4{1'b0}} , 4'd8} : msg_len_got[AXI_KEEP_LW-1:0] ; 

assign msg_len_dec  = msg_len_q - { {ML_W - AXI_KEEP_LW { 1'b0 }}, msg_len_got_sat };
assign msg_len_next = init_msg_len_v ? init_msg_len :
					  udp_axis_tvalid_q ? msg_len_dec : msg_len_q;
always @(posedge clk)
begin
	msg_len_q  <= msg_len_next;
end
// output mask
assign { unused_msg_mask_int , msg_mask_int } = msg_len_q[AXI_KEEP_LW-1:0] ; 
len_to_mask #(.LEN_W(AXI_KEEP_LW), .LEN_MAX(AXI_KEEP_W)) m_msg_end_mask(
	.len_i(msg_mask_int),
	.mask_o(msg_mask)
);
// len
logic [7:0] init_msg_len_p0_arr[AXI_KEEP_W-1:0];
logic [7:0] init_msg_len_p1_arr[AXI_KEEP_W-1:0];
genvar j;
generate 
	assign init_msg_len_p0_arr[0] = udp_axis_tdata_q[7:0];	
	assign init_msg_len_p1_arr[0] = udp_axis_tdata_q[15:8];	
	for(j=1; j<AXI_KEEP_W; j++) begin
		assign init_msg_len_p0_arr[j] = udp_axis_tdata_q[63-8*(j-1): 64-8*j];
		if ( j == 1 ) assign init_msg_len_p1_arr[j] = udp_axis_tdata_q[7:0];
		else assign init_msg_len_p1_arr[j] = udp_axis_tdata_q[63-8*(j-2):64-8*(j-1)];	
	end
endgenerate
assign len_shift = flop_shift & {ML_W{~fsm_msg_len_align_q}};
always_comb begin
	init_msg_len_p0 = {8{1'bX}};
	init_msg_len_p1 = {8{1'bX}};
	for( int unsigned i=0; i <= AXI_KEEP_W-1; i++) begin
		if ( i == ( len_shift )) init_msg_len_p0 = init_msg_len_p0_arr[i];
		if ( i == ( len_shift )) init_msg_len_p1 = init_msg_len_p1_arr[i];
	end
end
// init message len : flop if lenght ( 2 bytes ) are spread over 2 different
// AXI payloads
always @(posedge clk) begin
	init_msg_len_p0_q <= init_msg_len_p0;
end


	
// Message data buffering 
// When possible we want to gather message bits into 64 bits continus chunks

assign flop_len_next = {ML_W{fsm_h1_q}} & {ML_W{1'b0}} // reset flop len to 0
					 | {ML_W{fsm_h2_msg_q}} & 'd2  // TODO : add support for first msg len=0 
					 | {ML_W{fsm_msg_q & ~msg_end }} & flop_len_q // keep current flop len shift until the end of the message
				     | {ML_W{fsm_msg_len_align_q}} & 'd6; 
assign flop_shift  = {ML_W{fsm_h2_msg_q}} & 'd2 
				   | {ML_W{fsm_msg_q}} & flop_len_q
				   | {ML_W{fsm_msg_len_align_q}} & 'd6; 
 
//assign axis_flop_tdata_shift = flop_len_next; 

//assign axis_msg_tdata_shift = flop_len_next;

// TODO : move declaration to top ?
logic [AXI_DATA_W-1:0] axis_flop_tdata_shifted_arr[DFF_DATA_W:0];
logic [AXI_DATA_W-1:0] axis_msg_tdata_shifted_arr[DFF_DATA_W:0];

generate
	assign axis_flop_tdata_shifted_arr[0] = {AXI_DATA_W{1'bX}}; 
	assign axis_msg_tdata_shifted_arr[0]  = udp_axis_tdata_q[AXI_DATA_W-1:0]; 
	for( j = 1; j <= DFF_DATA_LW; j++) begin
		assign axis_flop_tdata_shifted_arr[j] =	{ { 64-(8*j) {1'b0} }, udp_axis_tdata_q[63:(64-(8*j))] }; 
		assign axis_msg_tdata_shifted_arr[j]  = { udp_axis_tdata_q[(63-(8*j)):0], {8*j{1'b0}} };
	end
endgenerate

always_comb begin
	// default
	flop_data_next = { AXI_DATA_W{1'bX}}; 
	axis_msg_tdata_shifted = { AXI_DATA_W{1'bX}};
	for( int unsigned i=0; i <= DFF_DATA_LW; i++) begin
	 	if (i == flop_shift) flop_data_next = axis_flop_tdata_shifted_arr[i];
	 	if (i == flop_shift) axis_msg_tdata_shifted  = axis_msg_tdata_shifted_arr[i]; 
	end
end

always @(posedge clk) begin
	flop_len_q  <= flop_len_next;
	flop_data_q <= flop_data_next;
end

// mask
len_to_mask #(.LEN_W(AXI_KEEP_LW), .LEN_MAX(AXI_KEEP_W)) m_flop_msg_mask(
	.len_i(flop_len_q),
	.mask_o(flop_msg_mask)
);

generate 
	for ( j = 0; j < AXI_KEEP_W; j++) begin
		if ( j == AXI_KEEP_W-1 ) begin
			assign msg_data[j*8+7:j*8] = {8{flop_msg_mask[j]}} & 8'bx
									   | {8{~flop_msg_mask[j]}} & axis_msg_tdata_shifted[j*8+7:j*8];
		end else begin
			assign msg_data[j*8+7:j*8] = {8{flop_msg_mask[j]}} & flop_data_q[j*8+7:j*8]
									   | {8{~flop_msg_mask[j]}} & axis_msg_tdata_shifted[j*8+7:j*8];
		end
	end
endgenerate

// decrement the number of messages we are still expected to see if we have
// reaced the end of the current message
assign msg_cnt_next = init_msg_cnt_v ? init_msg_cnt :
					  (msg_end & ~cnt_end) ? msg_cnt_q - { {ML_W-1{1'b0}}, 1'b1 } : msg_cnt_q;
assign cnt_end_next = ~|msg_cnt_next;
assign cnt_end = ~|msg_cnt_q;

assign cnt_en = init_msg_cnt_v | ~cnt_end;
always @(posedge clk)
begin
	msg_cnt_q <= msg_cnt_next;	
end
// fsm

assign fsm_invalid_next = fsm_invalid_q & ~udp_axis_tvalid_i // first payload received
						| fsm_msg_q & ( msg_end & cnt_end_next );
// header 
// hX  : header is received over multiple cycles 
// msg : during last cycle part of the packed is the begining of the message
assign fsm_h0_next     = fsm_invalid_q & udp_axis_tvalid_i;
assign fsm_h1_next     = fsm_h0_q;
assign fsm_h2_msg_next = fsm_h1_q; 

// message
// overlap : part of the next axi payload is of a different modludp64 message
//           it will be routed to the free moldudp64 module
assign fsm_msg_next = fsm_h2_msg_q 
					| (fsm_msg_q & ~(msg_end & cnt_end_next) & ~( fsm_msg_len_split_next | fsm_msg_len_align_next ))
					| fsm_msg_len_split_q
					| fsm_msg_len_align_q;

assign fsm_msg_overlap_next   = 1'b0;  
// msg len split over 2 AXI payloads
assign fsm_msg_len_split_next = fsm_msg_q & msg_end & ~cnt_end_next & (flop_shift == 'd1);
// msg len missing : present in start of the next packet
assign fsm_msg_len_align_next = fsm_msg_q & msg_end & ~cnt_end_next & msg_end_align;

always @(posedge clk)
begin
	if ( ~nreset ) begin
		fsm_invalid_q    <= 1'b1;
		fsm_h0_q         <= 1'b0;
		fsm_h1_q         <= 1'b0;
		fsm_h2_msg_q     <= 1'b0;
		fsm_msg_q         <= 1'b0;
		fsm_msg_overlap_q <= 1'b0;
		fsm_msg_len_split_q <= 1'b0;
		fsm_msg_len_align_q <= 1'b0;
		end else begin
		fsm_invalid_q    <= fsm_invalid_next; 
		fsm_h0_q         <= fsm_h0_next;     
		fsm_h1_q         <= fsm_h1_next;    
		fsm_h2_msg_q     <= fsm_h2_msg_next;   
		fsm_msg_q         <= fsm_msg_next;
		fsm_msg_overlap_q   <= fsm_msg_overlap_next;
		fsm_msg_len_split_q <= fsm_msg_len_split_next;
		fsm_msg_len_align_q <= fsm_msg_len_align_next;
	end
end


// output
assign udp_axis_tready_o = 1'b1; // we are always ready to accept a new packet 

assign mold_msg_v_o       = msg_v; 
assign mold_msg_data_o    = msg_data; 
assign mold_msg_start_o   = 'X; 
assign mold_msg_mask_o    = msg_end ? msg_mask : '1; 

`ifdef MOLD_MSG_IDS
assign mold_msg_sid_o     = sid_q;
assign mold_msg_seq_num_o = seq_q;
`endif

`ifdef FORMAL

logic [0:7] fsm_f;
assign fsm_f = {
	fsm_invalid_q, 
	fsm_h0_q, fsm_h1_q, fsm_h2_msg_q,
	fsm_msg_q, fsm_msg_overlap_q, fsm_msg_len_split_q, fsm_msg_len_align_q};

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
