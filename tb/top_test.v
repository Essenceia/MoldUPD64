
parameter AXI_DATA_W = 64;
parameter AXI_KEEP_W = AXI_DATA_W/8;
parameter KEEP_LW = $clog2(AXI_KEEP_W) + 1;
parameter LEN   = 8;
parameter ML_W  = 2*LEN;
parameter SID_W = 10*LEN;// session id
parameter SEQ_NUM_W = 8*LEN; // sequence number
parameter MH_W  = 20*LEN;// header 
parameter ITCH_N = 2;
`ifdef DEBUG_ID
parameter DEBUG_ID_W = SEQ_NUM_W + SID_W;
`endif

module moldudp64_tb;	
reg clk = 0;
reg nreset = 1'b0;	

logic [MH_W-1:0]       moldudp_header;
logic [ML_W-1:0]       moldudp_msg_len;
logic                  udp_axis_tvalid_i;
logic [AXI_KEEP_W-1:0] udp_axis_tkeep_i;
logic [AXI_DATA_W-1:0] udp_axis_tdata_i;
logic                  udp_axis_tlast_i;
logic                  udp_axis_tuser_i;
logic                  udp_axis_tready_o;

logic [ITCH_N-1:0]             mold_msg_v_o;
logic [ITCH_N-1:0]             mold_msg_start_o;
logic [ITCH_N*KEEP_LW-1:0]     mold_msg_len_o;
logic [ITCH_N*AXI_DATA_W-1:0]  mold_msg_data_o;

`ifdef DEBUG_ID
logic [DEBUG_ID_W-1:0] mold_msg_debug_id_o;
`endif

`ifdef MOLD_MSG_IDS
logic [SID_W-1:0]      mold_msg_sid_o;
logic [SEQ_NUM_W-1:0]  mold_msg_seq_num_o;
`endif

`ifdef MISS_DET
logic                 miss_seq_num_v_o;
logic [SID_W-1:0]     miss_seq_num_sid_o;
logic [SEQ_NUM_W-1:0] miss_seq_num_start_o;	
logic [SEQ_NUM_W-1:0] miss_seq_num_cnt_o;
logic                 miss_sid_v_o;
logic [SID_W-1:0]     miss_sid_start_o;
logic [SEQ_NUM_W-1:0] miss_sid_seq_num_start_o;
logic [SID_W-1:0]     miss_sid_cnt_o;
logic [SEQ_NUM_W-1:0] miss_sid_seq_num_end_o;
`endif

`ifdef HEARTBEAT
logic flatlined_v_o;
`endif
initial
begin
	$dumpfile("build/wave.vcd"); // create a VCD waveform dump called "wave.vcd"
    $dumpvars(0, moldudp64_tb);
	$display("Test start");
	udp_axis_tvalid_i = 1'b0;
	udp_axis_tkeep_i  = {AXI_KEEP_W{1'bx}};
	udp_axis_tdata_i  = {AXI_DATA_W{1'bx}};
	udp_axis_tlast_i  = 1'bx;
	udp_axis_tuser_i  = 1'bx;
	# 10
	nreset = 1'b1;
	#10
	/* axi stream */ 
	udp_axis_tvalid_i = 1'b1;	
	udp_axis_tkeep_i  = {AXI_KEEP_W{ 1'b1}};
	udp_axis_tlast_i = 1'b0;
	udp_axis_tuser_i = 1'b0;
	// header : sid
	moldudp_header[SID_W-1:0] = 80'hDEADBEEF;
	// header : seq num
	moldudp_header[(SID_W+SEQ_NUM_W)-1:SID_W] = 64'hF0F0F0F0F0F0F0F0;
	// header : msg cnt
	moldudp_header[MH_W-1:MH_W-ML_W] = { 8'd3, 8'd0 };

	moldudp_msg_len = { 8'd16, 8'd0 };
	/* Header 0*/
	udp_axis_tdata_i = moldudp_header[AXI_DATA_W-1:0];
	#10
	/* header 1*/
	udp_axis_tdata_i = moldudp_header[(AXI_DATA_W*2)-1:AXI_DATA_W];
	#10
	/* header 2 + msg 0*/
	udp_axis_tdata_i ={ 16'hffff, moldudp_msg_len, moldudp_header[MH_W-1:AXI_DATA_W*2] };
	#10
	/* payload 0 of msg 0 */
	udp_axis_tdata_i = {16{4'ha}};
	#10
	/* payload 1 of msg 0 + payload 0 of msg 1*/
	moldudp_msg_len = { 8'd8, 8'd0 };
	udp_axis_tdata_i = { moldudp_msg_len, {12{4'hB}}};
	#10
	/* payload 1 of msg 1 */
	udp_axis_tdata_i = {16{4'hD}};
	#10
	/* payload 0 of msg 2 */
	moldudp_msg_len = { 8'd11, 8'd0 };
	udp_axis_tdata_i = { {12{4'hE}} , moldudp_msg_len};

	#10
	/* payload 1 of msg 2 */
	udp_axis_tdata_i = {'X ,8'hAB ,{8{4'hF}}};
	udp_axis_tkeep_i = { '0, 4'b1111};
	udp_axis_tlast_i = 1'b1;
	#10
	/* no msg */
	udp_axis_tvalid_i = 1'b0;
	udp_axis_tkeep_i  = 'x;
	udp_axis_tlast_i  = 'x; 
	udp_axis_tdata_i  = 'x;
	#10	
	#10	
	#10	
	#10	
	$display("Test end");
	$finish;
end
 /* Make a regular pulsing clock. */
always #5 clk = !clk;

moldudp64 #(
	`ifdef DEBUG_ID
	.DEBUG_ID_W(DEBUG_ID_W),
	`endif
	.AXI_DATA_W(AXI_DATA_W),
	.AXI_KEEP_W(AXI_KEEP_W),
	.SID_W(SID_W),
	.SEQ_NUM_W(SEQ_NUM_W),
	.ML_W(ML_W),
	.EOS_MSG_CNT(16'hffff),
	.ITCH_N(ITCH_N)
) m_moldudp64(
	.clk(clk),
	.nreset(nreset),
	
	.udp_axis_tvalid_i(udp_axis_tvalid_i),
	.udp_axis_tkeep_i (udp_axis_tkeep_i ),
	.udp_axis_tdata_i (udp_axis_tdata_i ),
	.udp_axis_tlast_i (udp_axis_tlast_i ),
	.udp_axis_tuser_i (udp_axis_tuser_i ),
	.udp_axis_tready_o(udp_axis_tready_o),
	
	`ifdef MISS_DET
	.miss_seq_num_v_o    (miss_seq_num_v_o),
	.miss_seq_num_sid_o  (miss_seq_num_sid_o),
	.miss_seq_num_start_o(miss_seq_num_start_o),	
	.miss_seq_num_cnt_o  (miss_seq_num_cnt_o),
		
	.miss_sid_v_o            (miss_sid_v_o),
	.miss_sid_start_o        (miss_sid_start_o),
	.miss_sid_seq_num_start_o(miss_sid_seq_num_start_o),
	.miss_sid_cnt_o          (miss_sid_cnt_o),
	.miss_sid_seq_num_end_o  (miss_sid_seq_num_end_o),
	`endif
	
	`ifdef HEARTBEAT
	.flatlined_v_o   (flatlined_v_o     ),
	`endif
	
	`ifdef MOLD_MSG_IDS
	.mold_msg_sid_o    (mold_msg_sid_o    ),
	.mold_msg_seq_num_o(mold_msg_seq_num_o),
	`endif

	`ifdef DEBUG_ID
	.mold_msg_debug_id_o(mold_msg_debug_id_o),
	`endif
	
	.mold_msg_v_o    (mold_msg_v_o    ),
	.mold_msg_start_o(mold_msg_start_o),
	.mold_msg_len_o (mold_msg_len_o ),
	.mold_msg_data_o (mold_msg_data_o )

);
// xchecks
always @(posedge clk) begin
	if ( nreset ) begin
		`ifdef HEARTBEAT
		assert( ~$isunknown(flatlined_v_o));
		`endif
		assert( ~$isunknown(mold_msg_v_o ));
		if ( mold_msg_v_o ) begin
			assert( ~$isunknown(mold_msg_start_o));
			assert( ~$isunknown(mold_msg_len_o));
			`ifdef MOLD_MSG_IDS
			assert( ~$isunknown(mold_msg_seq_num_o));
			assert( ~$isunknown(mold_msg_sid_o));
			`endif
			`ifdef DEBUG_ID
			assert( ~$isunknown(mold_msg_debug_id_o));
			`endif
			end
	end
end
/*
genvar s,i;
generate
for( s = 0; s < ITCH_N; s++ ) begin
	for( i = 0; i < AXI_KEEP_W; i++) begin
		logic [7:0] masked_data;
		assign masked_data ={8{ (mold_msg_len_o[s*KEEP_LW+KEEP_LW-1:s*KEEP_LW] >= i) & mold_msg_v_o[s] }} & mold_msg_data_o[s*AXI_DATA_W+8*i+7:s*AXI_DATA_W+8*i];
		always @(posedge clk) begin
			if ( nreset ) begin
				assert( ~$isunknown( masked_data ));
				`ifdef DEBUG
				if ( $isunknown( masked_data )) begin
					$display("%t i %d masked data %h, len %d, data %h",
						$time,i,masked_data, mold_msg_len_o[s*KEEP_LW+KEEP_LW-1:s*KEEP_LW],
						 mold_msg_data_o[s*AXI_DATA_W+8*i+7:s*AXI_DATA_W+8*i]);
				end
				`endif
			end
		end
	
	end
end
endgenerate
*/

endmodule
