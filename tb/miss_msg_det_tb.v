class miss_det;
logic                 tb_inc_sid;
logic [64-1:0] tb_seq;
rand logic [64-1:0] tb_seq_inc;
logic [80-1:0]     tb_sid;
logic [80-1:0]     tb_sid_inc;

function new ();
	//std::srandom(TB_SEED);
	tb_seq = '0;
	tb_sid = '0;
endfunction

// increment tb
task new_session;
	output          v_o;
	output [80-1:0] sid_o;
	output [64-1:0] seq_num_o;
	output [16-1:0] msg_cnt_o;
	output          eos_o;
	logic           tb_seq_inc_overflow;
	logic [64-1:0]  tb_seq_exp;
	int randvar;	
	$display("Task start");
	do begin
		// No support for std::randomize in icarus verilog, it being only 32
		// bits isn't an issue in our case
		$display("0");
		randvar = $random(); 
		$display("1");
		tb_seq_inc = randvar[15:0];
		$display("2");
		{ tb_seq_inc_overflow, tb_seq_exp } = tb_seq + tb_seq_inc + 1;
		$display("tb_seq_exp %d, tb_seq_inc %d, overflow %d", tb_seq_exp, tb_seq_inc, tb_seq_inc_overflow);
		if ( tb_seq_inc_overflow == 1'b0 ) begin 
			#10
			v_o = 1'b1;
			sid_o = tb_sid;
			seq_num_o = tb_seq;
			msg_cnt_o = tb_seq_inc;
			
			// increment
			tb_seq = tb_seq_exp;
		end
	end while (tb_seq_inc_overflow == 1'b1 );
	//eof
	#10
	v_o = 1'b1;
	sid_o = tb_sid;
	seq_num_o = tb_seq;
	msg_cnt_o = '0;
	eos_o = 1'b1;
	#10
	v_o = 1'b0;
	eos_o = 1'b0;
	tb_sid = tb_sid + 1;
	tb_seq = '0;
endtask


endclass // miss_det



module miss_msg_det_tb;

localparam SID_GAP_MAX =(  1 << 63 );

reg clk = 0;
reg nreset = 1'b0;	

logic                 v_o;
logic [80-1:0]     sid_o;
logic [64-1:0] seq_num_o;
logic [16-1:0]      msg_cnt_o;
logic                 eos_o; // end of session
logic                 miss_seq_num_v_i;
logic                 miss_seq_num_sid_i;
logic [64-1:0] miss_seq_num_start_i;	
logic [64-1:0] miss_seq_num_cnt_i;
logic                 miss_sid_v_i;
logic [80-1:0]     miss_sid_start_i;
logic [64-1:0] miss_sid_seq_num_start_i;
logic [80-1:0]     miss_sid_cnt_i;
logic [64-1:0] miss_sid_seq_num_end_i;

miss_det tb_drive;

always #5 clk = ~clk;
initial begin
	$dumpfile("build/miss_tb.vcd");
	$dumpvars(0, miss_msg_det_tb);
	$display("Starting packet miss detection tb");
	tb_drive = new();
	// reset
	#10
	nreset = 1'b1;
	// start test
	tb_drive.new_session(v_o,sid_o,seq_num_o,msg_cnt_o,eos_o);
	
	#30
	$display("Test end");
	$finish;
end

miss_msg_det #(
	.SEQ_NUM_W(64),
	.SID_W(80),
	.ML_W(16),
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
