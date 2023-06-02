`define SEQ_NUM_W 18
`define SID_W 80
`define ML_W 16
`define SIM_LOOP 3


module miss_msg_det_tb;

localparam SID_GAP_MAX =(  1 << 63 );

reg clk    = 0;
reg nreset = 1'b0;	

logic                  v_o = 1'b0;
logic [`SID_W-1:0]     sid_o;
logic [`SEQ_NUM_W-1:0] seq_num_o;
logic [`ML_W-1:0]      msg_cnt_o;
logic                  eos_o; // end of session
logic                  miss_seq_num_v_i;
logic                  miss_seq_num_sid_i;
logic [`SEQ_NUM_W-1:0] miss_seq_num_start_i;	
logic [`SEQ_NUM_W-1:0] miss_seq_num_cnt_i;
logic                  miss_sid_v_i;
logic [`SID_W-1:0]     miss_sid_start_i;
logic [`SEQ_NUM_W-1:0] miss_sid_seq_num_start_i;
logic [`SID_W-1:0]     miss_sid_cnt_i;
logic [`SEQ_NUM_W-1:0] miss_sid_seq_num_end_i;

logic      [`SEQ_NUM_W-1:0]  tb_seq = '0;
logic      [`SID_W-1:0]      tb_sid = '0;


always #5 clk = ~clk;
initial begin
	$dumpfile("build/miss_tb.vcd");
	$dumpvars(0, miss_msg_det_tb);
	`ifdef DEBUG
	$display("Starting packet miss detection tb");
	`endif
	// reset
	#10
	nreset = 1'b1;
	// start test
	for( int i=0; i < `SIM_LOOP ; i++ ) begin
		new_session();
	end
	
	#10
	`ifdef DEBUG
	$display("Test end");
	`endif
	$finish;
end

miss_msg_det #(
	.SEQ_NUM_W(`SEQ_NUM_W),
	.SID_W(`SID_W),
	.ML_W(`ML_W),
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
	.miss_seq_num_cnt_o(miss_seq_num_cnt_i)
,
	.miss_sid_v_o(miss_sid_v_i),
	.miss_sid_start_o(miss_sid_start_i),
	.miss_sid_seq_num_start_o(miss_sid_seq_num_start_i),
	.miss_sid_cnt_o(miss_sid_cnt_i),
	.miss_sid_seq_num_end_o(miss_sid_seq_num_end_i)

);

// increment tb
task new_session();
	int                    randvar;	
	logic                  tb_seq_inc_overflow;
	logic [`SEQ_NUM_W-1:0] tb_seq_inc;
	logic [`SEQ_NUM_W-1:0] tb_seq_miss_cnt = '0;
	logic                  tb_inc_sid;
	logic [`SEQ_NUM_W-1:0] tb_seq_exp;
	logic [`SEQ_NUM_W-1:0] tb_seq_seen = '0;
	$display("Task start");
	do begin
		// No support for std::randomize in icarus verilog, it being only 32
		// bits isn't an issue in our case
		randvar    = $random(); 
		tb_seq_inc = randvar[15:0];
		{ tb_seq_inc_overflow, tb_seq_exp } = tb_seq + tb_seq_inc + 1;
		`ifdef DEBUG
		$display("%t tb_seq_exp %d, tb_seq_inc %d, overflow %d",$time, tb_seq_exp, tb_seq_inc, tb_seq_inc_overflow);
		`endif
		if ( tb_seq_inc_overflow == 1'b0 ) begin
			if (randvar % 4 == 0 ) begin
				// don't send packet, increment miss cnt
				v_o = 1'b0;
				tb_seq_miss_cnt = tb_seq_inc + tb_seq_miss_cnt;
				#10
				v_o = 1'b0; // prevent syntax error
				`ifdef DEBUG
				$display("Miss triggered, missed %d messages", tb_seq_miss_cnt);
				`endif
			end else begin
				// send packet
				v_o       = 1'b1;
				sid_o     = tb_sid;
				seq_num_o = tb_seq + tb_seq_miss_cnt ;
				msg_cnt_o = tb_seq_inc;
				eos_o     = 1'b0;	
				`ifdef DEBUG
				$display("%t write seq_num %d, msg_cnt %d", $time, tb_seq, tb_seq_inc);
				`endif
				// check if miss seen
				#1
				check_miss( tb_seq_miss_cnt, '0, tb_seq_seen, tb_sid);
				#1
				// increment
				tb_seq = tb_seq_exp + tb_seq_miss_cnt;
				tb_seq_seen = tb_seq;
				tb_seq_miss_cnt = '0;
				#8
				check_exp_match( tb_seq, tb_sid );	
			end
		end
	end while (tb_seq_inc_overflow == 1'b0 );
	//eof
	#10
	v_o       = 1'b1;
	sid_o     = tb_sid;
	seq_num_o = tb_seq;
	msg_cnt_o = '0;
	eos_o     = 1'b1;
	#10
	v_o    = 1'b0;
	eos_o  = 1'b0;
	tb_sid = tb_sid + 1;
	tb_seq = '0;
endtask

// check the next expected seq number and sid matches expected
function check_exp_match( logic [`SEQ_NUM_W-1:0] tb_seq, logic [`SID_W-1:0] tb_sid );
	logic seq_match;
	logic sid_match;
	assign seq_match =  tb_seq == m_miss_det.seq_q;
	assign sid_match =  tb_sid == m_miss_det.sid_q;
	assert(seq_match);
	assert(sid_match);
endfunction

// check miss signals
// *_miss_cnt : number of missing messages/sessions not sent to uut
// *_sent : last index seen by the uut
function check_miss( logic [`SEQ_NUM_W-1:0] tb_seq_miss_cnt, logic [`SID_W-1:0] tb_sid_miss,
		logic [`SEQ_NUM_W-1:0] tb_seq_sent, logic [`SID_W-1:0] tb_sid_sent );
	logic seq_miss_match;
	logic sid_miss_match;
	sid_miss_match = ( tb_sid_miss != 0 ) == miss_sid_v_i ;
	seq_miss_match =  ( tb_sid_miss != 0 ) | ( ( tb_sid_miss == 0 ) & (( tb_seq_miss_cnt != 0 ) == miss_seq_num_v_i  )) ;
	assert ( sid_miss_match );
	assert ( seq_miss_match );

	// check metadata for replay
	// seq num 
	if (( tb_seq_miss_cnt != 0 ) & ( tb_sid_miss == 0 )) begin
		assert( miss_seq_num_sid_i == tb_sid_sent );
		assert( miss_seq_num_start_i == tb_seq_sent );
		assert( miss_seq_num_cnt_i == tb_seq_miss_cnt );
	end
endfunction
endmodule
