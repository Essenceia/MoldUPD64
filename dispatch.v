/* Data dispatcher */
module dispatch #{
	parameter AXI_DATA_W = 64,
	parameter AXI_KEEP_W = (AXI_DATA_W/8),
	parameter KEEP_LW    = $ceil(AXI_KEEP_W) + 1,

	parameter LEN_W = 16,// length field
	// number of dispatch outputs
	parameter OUT   = 2
}{
	input clk,
	input nreset,

	input                  valid_i,
	input [AXI_DATA_W-1:0] data_i,
	input [AXI_KEEP_W-1:0] keep_i,
	input                  init_v_i,
	input                  last_i,

	output [OUT-1:0]            pipe_valid_o,
	output [OUT*AXI_DATA_W-1:0] pipe_data_o,
	output [OUT*KEEP_LW-1:0]    pipe_len_o
}
// selector of primary pipe to drive data to
logic [OUT-1:0] pipe_sel_next;
reg   [OUT-1:0] pipe_sel_q;

logic [LEN_W-1:0] data_len;
logic [LEN_W-1:0] pipe_sel_len;
// remaining bytes to be got
logic [LEN-1:0] len_next[OUT-1:0];
reg   [LEN-1:0] len_q[OUT-1:0];
logic [LEN-1:0] len_dec[OUT-1:0];
// pipe_msg has ended
logic [OUT-1:0] pipe_msg_end;
logic [OUT-1:0] pipe_v; 

// received bytes
logic [AXI_KEEP_W-1:0] pipe_keep[OUT-1:0];
logic [LEN-1:0]        pipe_len[OUT-1:0];

// transmitted bytes
logic [LEN-1:0] tx_len[OUT-1:0];

// fsm
logic fsm_invalid_next;
logic fsm_msg_next;
logic fsm_len_align_next;
logic fsm_len_split_next;
reg   fsm_invalid_q;
reg   fsm_msg_q;
reg   fsm_len_align_q;
reg   fsm_len_split_q;

// selection of primary pipe logic
always @(posedge clk) begin
	if ( ~nreset ) begin
		pipe_sel_q <= 'd1;
	end else begin
		pipe_sel_q <= pipe_sel_next;
	end
end
cnt_ones_thermo #(.D_W(AXI_KEEP_W), .D_LW(KEEP_LW) 
m_axis_cnt_ones_thermo(
	.data_i(keep_i),
	.cnt_o(data_len)
);	
always_comb begin
	for( i=0; i < OUT; i++) begin
		if ( pipe_sel_q[i] ) pipe_sel_len = pipe_len[i]; 
	end
end

genvar s;
generate 
for ( s = 0; s < OUT; s++ ) begin

// length countdown logic until the end of message

		cnt_ones_thermo #(.D_W(AXI_KEEP_W), .D_LW(KEEP_LW) m_cnt_ones_thermo(
			.data_i(pipe_keep[s]),
			.cnt_o(pipe_len[s])
		);	
		assign pipe_len_dec[s] = pipe_len_q[s] - pipe_len[s]; 

		assign pipe_msg_end[s] = pipe_len_q[s] <= pipe_len[s];
always @(posedge clk) begin
	if ( ~nreset ) begin
		pipe_len_q[s] <= 'd0;
	end else begin
		pipe_len_q[s] <= pipe_len_next[s];
	end
end
 
// count received length 
end // end for

// FSM
assign fsm_invalid_next = valid_i & last_i;
assign fsm_msg_next = (( valid_i & init_v_i ) // init
				    | fsm_len_align_q 
					| fsm_len_split_q
					| fsm_msg_q & ~( fsm_len_split_next | fsm_len_align_next)
					) & ~fsm_invalid_next;
assign fsm_len_align_next = 1'b0; 
assign fsm_len_split_next = 1'b0;

always @(posedge clk) begin
	if ( ~nreset ) begin
		fsm_invalid_q   <= 1'b1;
		fsm_msg_q       <= 1'b0;
		fsm_len_align_q <= 1'b0;
		fsm_len_split_q <= 1'b0;
	end else begin
		fsm_invalid_q   <= fsm_invalid_next;
		fsm_msg_q       <= fsm_msg_next;
		fsm_len_align_q <= fsm_len_align_next;
		fsm_len_split_q <= fsm_len_split_next;
	end
end 
endgenerate

endmodule
