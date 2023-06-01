`timescale 1ns/100ps

module miss_msg_det_test;

localparam SEQ_NUM_W   = 64;
localparam SID_W       = 80;
localparam ML_W        = 16;
localparam SID_GAP_MAX =(  1 << SEQ_NUM_W-1 );

reg clk = 0;
reg nreset = 1'b0;	

logic                 v_o;
logic [SID_W-1:0]     sid_o;
logic [SEQ_NUM_W-1:0] seq_num_o;
logic [ML_W-1:0]      msg_cnt_o;
logic                 eos_o; // end of session
logic                 miss_seq_num_v_i;
logic                 miss_seq_num_sid_i;
logic [SEQ_NUM_W-1:0] miss_seq_num_start_i;	
logic [SEQ_NUM_W-1:0] miss_seq_num_cnt_i;
logic                 miss_sid_v_i;
logic [SID_W-1:0]     miss_sid_start_i;
logic [SEQ_NUM_W-1:0] miss_sid_seq_num_start_i;
logic [SID_W-1:0]     miss_sid_cnt_i;
logic [SEQ_NUM_W-1:0] miss_sid_seq_num_end_i;

always #5 clk = ~clk;

initial begin
	$dumpfile("build/miss_tb.vcd");
	$dumpvars(0, miss_msg_det_test);
	$display("Starting packet miss detection tb");
	// reset
	#10
	nreset = 1'b1;
	#30
	$display("Test end");
	$finish;
end

miss_msg_det #(
	.SEQ_NUM_W(SEQ_NUM_W),
	.SID_W(SID_W),
	.ML_W(ML_W),
	.SID_GAP_MAX(SID_GAP_MAX)	
	) m_miss_det (
	.clk(clk),
	.nreset(nreset),
	
	.v_i(v_o),
	.sid_i(sid_o),
	.seq_num_i(seq_num_o),
	.msg_cnt_i(msg_cnt_o),
	.eos_i(eos_o),
	
	.miss_seq_num_v_o(miss_seq_num_v_i),
	.miss_seq_num_sid_o(miss_seq_num_sid_i),
	.miss_seq_num_start_o(miss_seq_num_start_i),	
	.miss_seq_num_cnt_o(miss_seq_num_cnt_i),
	.miss_sid_v_o(miss_sid_v_i),
	.miss_sid_start_o(miss_sid_start_i),
	.miss_sid_seq_num_start_o(miss_sid_seq_num_start_i),
	.miss_sid_cnt_o(miss_sid_cnt_i),
	.miss_sid_seq_num_end_o(miss_sid_seq_num_end_i)

);
endmodule
