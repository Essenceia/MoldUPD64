/* Copyright (c) 2023, Julia Desmazes. All rights reserved.
 * 
 * This work is licensed under the Creative Commons Attribution-NonCommercial
 * 4.0 International License. 
 * 
 * This code is provided "as is" without any express or implied warranties.
 * 
 * For purchasing a commertial license contact : julia.desmazes@gmail.com  */ 

/* Convert a length expressed in decimal into a thermometer mask */
module len_to_mask #(
	parameter LEN_W   = 4, 
	parameter LEN_MAX = 8 // max length in decimal
)(
	input [LEN_W-1:0]      len_i,
	output logic [LEN_MAX] mask_o
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
