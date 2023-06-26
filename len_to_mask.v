/* Copyright (c) 2023, Julia Desmazes. All rights reserved.
 * 
 * This work is licensed under the Creative Commons Attribution-NonCommercial
 * 4.0 International License. 
 * 
 * This code is provided "as is" without any express or implied warranties. */ 

/* Convert a length expressed in decimal into a thermometer mask */
module len_to_mask #(
	parameter LEN_W   = 4, 
	parameter LEN_MAX = 8 // max length in decimal
)(
	input        [LEN_W-1:0]   len_i,
	output logic [LEN_MAX-1:0] mask_o
);
	
genvar i;
generate 
	for(i=0; i<LEN_MAX; i++)begin
		assign mask_o[i] = ( len_i > i);
	end
endgenerate

`ifdef FORMAL
always_comb begin
	sva_mask_thermo : assert( $onehot(mask_o + 1) );
	sva_num_ones_match_len : assert( len_i == $countones(mask_o));
end
`endif
endmodule


/* Convert a length expressed in decimal into a MSB thermometer mask.
 * Mask will be applied to MSB bits unlike in normal verision where mask
 * is applied to LSB bits.
 * 
 * Illustration :
 * LEN_MAX = 8, len_i = 4'd2 -> mask_o = 8'b1100_0000
 */
module len_to_mask_msb #(
	parameter LEN_W   = 4, 
	parameter LEN_MAX = 8 // max length in decimal
)(
	input        [LEN_W-1:0]   len_i,
	output logic [LEN_MAX-1:0] mask_o
);
	
genvar i;
generate 
	for(i=0; i<LEN_MAX; i++)begin
		assign mask_o[LEN_MAX-1-i] = ( len_i > i);
	end
endgenerate

`ifdef FORMAL
logic [LEN_MAX-1:0] f_mask_rev;
// reverse bit order
generate
	for(i=0; i< LEN_MAX; i++) begin
		assign f_mask_rev[i] = mask_o[LEN_MAX-1-i];
	end
always_comb begin
	sva_mask_thermo : assert( $onehot(f_mask_rev + 1) );
	sva_num_ones_match_len : assert( len_i == $countones(mask_o));
end
`endif
endmodule
