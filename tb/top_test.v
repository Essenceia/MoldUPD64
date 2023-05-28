module top_test;
	localparam AXI_DATA_W_ = 64;
	localparam AXI_KEEP_W  = $clog2(AXI_DATA_W);
	localparam LEN = 8;
	localparam ML_W = 2*LEN;
	localparam SID_W = 10*LEN;// session id
	localparam SEQ_W = 8*LEN;// sequence number

	reg clk = 0;
	reg nreset = 1'b0;	

	logic 	
	logic                  upd_axis_tvalid_o = 1'b0;
	logic [AXI_KEEP_W-1:0] upd_axis_tkeep_o;
	logic [AXI_DATA_W-1:0] upd_axis_tdata_o;
	logic                  upd_axis_tlast_o;
	logic                  upd_axis_tuser_o;
	logic                  upd_axis_tready_i;

	logic                  mold_msg_v_i;
	logic                  mold_msg_start_i;
	logic [ML_W-1:0]       mold_msg_len_i;
	logic [AXI_KEEP_W-1:0] mold_msg_mask_i;
	logic [AXI_DATA_W-1:0] mold_msg_data_i;

	initial
	begin
		$display("Test start");
		# 10
		nreset = 1'b1;
		$finish;
	end
	 /* Make a regular pulsing clock. */
	always #5 clk = !clk;

	/* axi stream */ 
	/* Header 0*/
	assign upd_axis_tvalid_o = 1'b1;	
	assign upd_axis_tkeep_o = '1;
	assign upd_axis_tdata_o;
	assign upd_axis_tlast_o;
	assign upd_axis_tuser_o;
	/* header 1*/

	/* header 2*/

	/* msg 0 */

	top m_top(
	.clk(clk),
	.nreset(nreset),

	.upd_axis_tvalid_i(upd_axis_tvalid_o),
	.upd_axis_tkeep_i (upd_axis_tkeep_o ),
	.upd_axis_tdata_i (upd_axis_tdata_o ),
	.upd_axis_tlast_i (upd_axis_tlast_o ),
	.upd_axis_tuser_i (upd_axis_tuser_o ),
	.upd_axis_tready_o(upd_axis_tready_i),

	.mold_msg_v_o    (mold_msg_v_i    ),
	.mold_msg_start_o(mold_msg_start_i),
	.mold_msg_len_o  (mold_msg_len_i  ),
	.mold_msg_mask_o (mold_msg_mask_i ),
	.mold_msg_data_o (mold_msg_data_i )
	
	);
endmodule
