
module top_test;
	localparam AXI_DATA_W = 64;
	localparam AXI_KEEP_W = AXI_DATA_W/8;
	localparam LEN   = 8;
	localparam ML_W  = 2*LEN;
	localparam SID_W = 10*LEN;// session id
	localparam SEQ_NUM_W = 8*LEN; // sequence number
	localparam MH_W  = 20*LEN;// header 

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

	logic                  mold_msg_v_o;
	logic                  mold_msg_start_o;
	logic [SEQ_NUM_W-1:0]  mold_msg_seq_num_o;
	logic [SID_W-1:0]      mold_msg_sid_o;
	logic [AXI_KEEP_W-1:0] mold_msg_mask_o;
	logic [AXI_DATA_W-1:0] mold_msg_data_o;

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
        $dumpvars(0, top_test);
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
		moldudp_header[MH_W-1:MH_W-ML_W] = 'd3;

		moldudp_msg_len = 16'd16;
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
		moldudp_msg_len = 16'd8;
		udp_axis_tdata_i = { moldudp_msg_len, {12{4'hB}}};
		#10
		/* payload 1 of msg 1 */
		udp_axis_tdata_i = {16{4'hD}};
		#10
		/* payload 0 of msg 2 */
		moldudp_msg_len = 16'd11;
		udp_axis_tdata_i = { {12{4'hE}} , moldudp_msg_len};
		#10
		/* payload 1 of msg 2 */
		udp_axis_tdata_i = {'X , {10{4'hF}}};
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

	top #(
	.AXI_DATA_W(AXI_DATA_W),
	.AXI_KEEP_W(AXI_KEEP_W),
	.SID_W(SID_W),
	.SEQ_NUM_W(SEQ_NUM_W),
	.ML_W(ML_W),
	.EOS_MSG_CNT(16'hffff)
	) m_top(
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

	.mold_msg_v_o    (mold_msg_v_o    ),
	.mold_msg_start_o(mold_msg_start_o),
	.mold_msg_mask_o (mold_msg_mask_o ),
	.mold_msg_data_o (mold_msg_data_o )
	
	);
// xchecks
always @(posedge clk) begin
	if ( nreset ) begin
		assert( ~$isunknown(mold_msg_v_o));
		if ( mold_msg_v_o ) begin
			assert( ~$isunknown(mold_msg_start_o));
			assert( ~$isunknown(mold_msg_seq_num_o));
			assert( ~$isunknown(mold_msg_sid_o));
			assert( ~$isunknown(mold_msg_mask_o));
			end
	end
end

genvar i;
generate
for( i = 0; i < AXI_KEEP_W; i++) begin
	always @(posedge clk) begin
		if ( nreset & mold_msg_v_o ) begin
			assert( ~$isunknown( {8{mold_msg_mask_o[i]}} & mold_msg_data_o[8*i+7:8*i]));
		end
	end
end
endgenerate


endmodule
