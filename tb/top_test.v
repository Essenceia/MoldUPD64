`timescale 1ns/100ps

module top_test;
	localparam AXI_DATA_W = 64;
	localparam AXI_KEEP_W = AXI_DATA_W/8;
	localparam LEN   = 8;
	localparam ML_W  = 2*LEN;
	localparam SID_W = 10*LEN;// session id
	localparam SEQ_W = 8*LEN; // sequence number
	localparam MH_W  = 20*LEN;// header 

	reg clk = 0;
	reg nreset = 1'b0;	

	logic [MH_W-1:0]       moldudp_header;
	logic [ML_W-1:0]       moldudp_msg_len;
	logic                  upd_axis_tvalid_o;
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
 		$dumpfile("build/wave.vcd"); // create a VCD waveform dump called "wave.vcd"
        $dumpvars(0, top_test);
		$display("Test start");
		upd_axis_tvalid_o = 1'b0;
		upd_axis_tkeep_o  = {AXI_KEEP_W{1'bx}};
		upd_axis_tdata_o  = {AXI_DATA_W{1'bx}};
		upd_axis_tlast_o  = 1'bx;
		upd_axis_tuser_o  = 1'bx;
		# 10
		nreset = 1'b1;
		#10
		/* axi stream */ 
		upd_axis_tvalid_o = 1'b1;	
		upd_axis_tkeep_o  = {AXI_KEEP_W{ 1'b1}};
		upd_axis_tlast_o = 1'b0;
		upd_axis_tuser_o = 1'b0;
		// header : sid
		moldudp_header[SID_W-1:0] = 'hDEADBEEF;
		// header : seq num
		moldudp_header[(SID_W+SEQ_W)-1:SID_W] = 'hF0F0F0F0F0F0F0F0;
		// header : msg cnt
		moldudp_header[MH_W-1:MH_W-ML_W] = 'd3;

		moldudp_msg_len = 16'd16;
		/* Header 0*/
		upd_axis_tdata_o = moldudp_header[AXI_DATA_W-1:0];
		#10
		/* header 1*/
		upd_axis_tdata_o = moldudp_header[(AXI_DATA_W*2)-1:AXI_DATA_W];
		#10
		/* header 2 + msg 0*/
		upd_axis_tdata_o ={ 16'hffff, moldudp_msg_len, moldudp_header[MH_W-1:AXI_DATA_W*2] };
		#10
		/* payload 0 of msg 0 */
		upd_axis_tdata_o = {16{4'ha}};
		#10
		/* payload 1 of msg 0 + payload 0 of msg 1*/
		moldudp_msg_len = 16'd8;
		upd_axis_tdata_o = { moldudp_msg_len, {12{4'hB}}};
		#10
		/* payload 1 of msg 1 */
		upd_axis_tdata_o = {16{4'hD}};
		#10
		/* payload 0 of msg 2 */
		moldudp_msg_len = 16'd11;
		upd_axis_tdata_o = { {12{4'hE}} , moldudp_msg_len};
		#10
		/* payload 1 of msg 2 */
		upd_axis_tdata_o = {'X , {10{4'hF}}};
		upd_axis_tkeep_o = { '0, 4'b1111};
		upd_axis_tlast_o = 1'b1;
		#10
		/* no msg */
		upd_axis_tvalid_o = 1'b0;
		upd_axis_tkeep_o  = 'x;
		upd_axis_tlast_o  = 'x; 
		upd_axis_tdata_o  = 'x;
		#10	
		#10	
		#10	
		#10	
		$display("Test end");
		$finish;
	end
	 /* Make a regular pulsing clock. */
	always #5 clk = !clk;

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
