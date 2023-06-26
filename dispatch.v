/* Copyright (c) 2023, Julia Desmazes. All rights reserved.
 * 
 * This work is licensed under the Creative Commons Attribution-NonCommercial
 * 4.0 International License. 
 * 
 * This code is provided "as is" without any express or implied warranties. */ 

/* Data dispatcher */
module dispatch #(
	parameter AXI_DATA_W = 64,
	parameter AXI_KEEP_W = (AXI_DATA_W/8),
	parameter KEEP_LW    = 3,//$ceil(AXI_KEEP_W) + 1,

	parameter LEN_W = 16,// length field
	// number of dispatch outputs
	parameter OUT   = 2
)(
	input clk,
	input nreset,

	input                  valid_i,
	input [AXI_DATA_W-1:0] data_i,
	input [AXI_KEEP_W-1:0] keep_i,
	input                  init_v_i,
	input                  last_i,

	output [OUT-1:0]            pipe_valid_o,
	output [OUT-1:0]            pipe_start_o,
	output [OUT*AXI_DATA_W-1:0] pipe_data_o,
	output [OUT*KEEP_LW-1:0]    pipe_len_o
);
// received bytes
logic [AXI_KEEP_W-1:0] pipe_keep[OUT-1:0];
// transmitted bytes

// fsm
logic fsm_invalid_next;
logic fsm_msg_next;
logic fsm_len_align_next;
logic fsm_len_split_next;
reg   fsm_invalid_q;
reg   fsm_msg_q;
reg   fsm_len_align_q;
reg   fsm_len_split_q;

// selector of primary pipe to drive data to
logic [OUT-1:0] pipe_sel_next;
reg   [OUT-1:0] pipe_sel_q;

// remaining bytes to be got
logic [LEN_W-1:0] pipe_msg_tx_len[OUT-1:0];
// pipe_msg has ended
logic [OUT-1:0] pipe_msg_end;
logic [OUT-1:0] pipe_v; 

// selection of primary pipe logic
logic               pipe_sel_msg_end;
logic [LEN_W-1:0]   pipe_sel_msg_len_q;
logic [LEN_W-1:0]   pipe_sel_msg_len_dec;
logic [LEN_W-1:0]   pipe_sel_msg_len_next;
logic [KEEP_LW-1:0] data_len;

always @(posedge clk) begin
	if ( ~nreset ) begin
		pipe_sel_q <= 'd1;
	end else begin
		pipe_sel_q <= pipe_sel_next;
	end
end
// recieved data length
/*
cnt_ones_thermo #(.D_W(AXI_KEEP_W), .D_LW(KEEP_LW)) 
m_axis_cnt_ones_thermo(
	.data_i(keep_i),
	.cnt_o(data_len)
);*/
assign data_len = AXI_KEEP_W; 
assign pipe_sel_msg_end = ~pipe_sel_msg_len_q[LEN_W-1:KEEP_LW] & ( pipe_sel_msg_len_q[KEEP_LW-1:0] <= data_len );
assign pipe_sel_msg_len_dec = pipe_sel_msg_len_q - data_len;
// check if msg end overlaps with the same pl with the begining of the
// next message.
// When this happens start streaming the beging of the next message into the
// other pipe and toggle primary pipe selector
// number of overlap bytes
logic               pload_overlap_v;
logic [KEEP_LW-1:0] pload_overlap_len;
logic [KEEP_LW-1:0] msg_overlap_len;
logic [KEEP_LW-1:0] pipe_sel_len_inc2;
logic               pipe_sel_len_inc2_overflow;
logic               msg_len_split;
logic               msg_len_align;
logic               msg_len_align_end;
logic               msg_len_inner;

assign pload_overlap_v   = valid_i & msg_len_inner;
assign pload_overlap_len = data_len - pipe_sel_msg_len_q[KEEP_LW-1:0];

assign { pipe_sel_len_inc2_overflow , pipe_sel_len_inc2 } = pipe_sel_msg_len_q[KEEP_LW-1:0] + 'd2;
assign msg_overlap_len   = data_len - pipe_sel_len_inc2;

assign msg_len_split = pload_overlap_len == 'd1; // only 1 bytes of the length gotten
assign msg_len_align = pload_overlap_len == 'd0; // no bytes gotten
assign msg_len_inner =(pload_overlap_len >= 'd2) & ~msg_len_align_end; // full length available
 
assign msg_len_align_end = ( data_len == pipe_sel_len_inc2 ) & ~pipe_sel_len_inc2_overflow; // no bytes gotten
// toggle select
// select message is going to  end in this payload, if it fails mid way 
// we should re-route the begining of the next message into the next 
// output
if ( OUT == 2 ) begin
	assign pipe_sel_next[0] = pload_overlap_v ? ~pipe_sel_next[1] : pipe_sel_next[1]; 
	assign pipe_sel_next[1] = pload_overlap_v ? ~pipe_sel_next[0] : pipe_sel_next[0];
end else begin
// not supported yet
end
// init new message length
logic               init_len_v;
logic [LEN_W-1:0]   init_len;
logic [LEN_W-1:0]   header_msg_len;
logic [7:0]         init_len_p1;
logic [7:0]         init_len_split_half_next;
logic [7:0]         init_len_split_half_q;
logic [7:0]         init_len_p0;

assign init_len_v = valid_i & ( pipe_sel_msg_end | init_v_i );

assign init_len   = {LEN_W{init_v_i}}  & { data_i[39:32] , data_i[47:40] }
				  | {LEN_W{fsm_msg_q}} & { init_len_p1, init_len_p0 }
				  | {LEN_W{fsm_len_align_q }} & { data_i[7:0], data_i[15:8] }
				  | {LEN_W{fsm_len_split_q }} & { init_len_split_half_q, data_i[7:0] };
assign pipe_sel_msg_len_next = init_len_v ? init_len : ( pipe_
// get length bytes
// will discard shift indexes covered by fsm states:
//  0 : align
//  1 : split
//  KEEP_W-1 : split
logic [KEEP_LW-1:0] len_shift;
logic [LEN_W-1:0]  len_shifted_arr[AXI_KEEP_W-2:2];
logic [LEN_W-1:0]  len_shifted;

assign len_shift = pipe_sel_msg_len_q[KEEP_LW-1:0];
genvar s;
generate
for ( s = 2; s < AXI_KEEP_W-1; s++ ) begin
	assign len_shifted_arr[s] = data_i[s*8 + LEN_W-1: s*8];
end
endgenerate
always_comb begin
	for(int i=2; i< AXI_KEEP_W-1; i++) begin
		if( len_shift == i ) len_shifted = len_shifted_arr[i]; 
	end
end
assign init_len_p0 = len_shifted[15:8];
assign init_len_p1 = len_shifted[7:0];

assign init_len_split_half_next = data_i[AXI_DATA_W-1:AXI_DATA_W-8];
always @(posedge clk) begin
	init_len_split_half_q <= init_len_split_half_next;
end

// data len and mask 
logic [KEEP_LW-1:0]    pipe_sel_data_len;
logic [KEEP_LW-1:0]    pipe_new_data_len;

assign pipe_sel_data_len = pipe_sel_msg_end ? pipe_sel_msg_len_q : data_len;
assign pipe_new_data_len = msg_overlap_len;

// doubling shifting logic to save a on additional logic depth, could share mux logic
// between sel and new data.
// new data shift : select new message data in case of partial presence on payload
// sel data shift : shift to compensate for the presence of length bytes at the begining of
// the payload
logic [KEEP_LW-1:0]    sel_data_shift;
logic [KEEP_LW-1:0]    new_data_shift;
logic [AXI_DATA_W-1:0] sel_data_shifted; 
logic [AXI_DATA_W-1:0] new_data_shifted; 
logic [AXI_DATA_W-1:0] data_shifted_arr[AXI_KEEP_W-1:0]; 

// shift of 0 for other cases
assign sel_data_shift = {KEEP_LW{fsm_len_split_q}} & 'd1
					  | {KEEP_LW{fsm_len_align_q}} & 'd2; 
assign new_data_shift = pipe_sel_len_inc2;

generate
for ( s = 0; s < AXI_KEEP_W; s++ ) begin
	assign data_shifted_arr[s] = { {s*8{1'bx}} , data_i[AXI_DATA_W-1: 8*s]};
end
endgenerate
always_comb begin
	for(int i=0; i< AXI_KEEP_W; i++) begin
		if( sel_data_shift == i ) sel_data_shifted = data_shifted_arr[i]; 
		if( new_data_shift == i ) new_data_shifted = data_shifted_arr[i]; 
	end
end
// new msg start
logic pipe_sel_data_start;
logic pipe_new_data_start;
assign pipe_sel_data_start = ( fsm_len_split_q | fsm_len_align_q | init_v_i ) & ( valid_i & ~last_i);
assign pipe_new_data_start = pload_overlap_v & ~last_i;

// drive output pipes
generate 
	for ( s = 0; s < OUT; s++ ) begin
		assign pipe_valid_o[s] = valid_i & ( pipe_sel_q[s] | pload_overlap_v );
		assign pipe_start_o[s] = pipe_sel_q[s]? pipe_sel_data_start : pipe_new_data_start;
		assign pipe_data_o[s]  = pipe_sel_q[s]? sel_data_shifted : new_data_shifted;
		assign pipe_len_o[s]   = pipe_sel_q[s]? pipe_sel_data_len : pipe_new_data_len;
	end
endgenerate

// FSM
assign fsm_invalid_next = fsm_invalid_q & ~valid_i 
						| valid_i & last_i;
assign fsm_msg_next = (( valid_i & init_v_i ) // init
				    | fsm_len_align_q 
					| fsm_len_split_q
					| fsm_msg_q & ~( fsm_len_split_next | fsm_len_align_next)
					) & ~( valid_i & last_i );
assign fsm_len_align_next = fsm_msg_q & pipe_sel_msg_end & msg_len_align; 
assign fsm_len_split_next = fsm_msg_q & pipe_sel_msg_end & msg_len_split; 

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
`ifdef FORMAL
logic [3:0] f_fsm;
assign f_fsm = { fsm_invalid_q, fsm_msg_q, fsm_len_align_q, fsm_len_split_q };

initial begin
	a_reset : assume( ~nreset );
end
always @(posedge clk) begin
	sva_fsm_onehot : assert( $onehot(f_fsm)); 
end
`endif
endmodule
