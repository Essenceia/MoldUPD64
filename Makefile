ifndef debug
#debug :=
endif

TB_DIR=tb
BUILD=build
CONF=conf
FLAGS=-Wall -g2012 -gassertions -gstrict-expr-width
DEFINES=-DMISS_DET -DHEARTBEAT -DMOLD_MSG_IDS $(if $(debug),-DDEBUG -DDEBUG_ID)
WAVE_FILE=wave.vcd
VIEW=gtkwave
WAVE_CONF=wave.conf
all: top run

cnt_ones_thermo : cnt_ones_thermo.v
	iverilog ${FLAGS} -s cnt_ones_thermo -o ${BUILD}/cnt_ones_thermo cnt_ones_thermo.v

countdown: countdown.v
	iverilog ${FLAGS} -s countdown -o ${BUILD}/countdown countdown.v

len_to_mask: len_to_mask.v
	iverilog ${FLAGS} -s len_to_mask -o ${BUILD}/len_to_mask len_to_mask.v

header: header.v endian_flip
	iverilog ${FLAGS} -s header -o ${BUILD}/header header.v endian_flip.v

miss_msg_det: miss_msg_det.v
	iverilog ${FLAGS} -s miss_msg_det -o ${BUILD}/miss_msg_det_tb miss_msg_det.v

endian_flip: endian_flip.v
	iverilog ${FLAGS} -s endian_flip  -o ${BUILD}/endian_flip.v endian_flip.v

miss_msg_det_tb: miss_msg_det ${TB_DIR}/miss_msg_det_tb.v
	iverilog ${FLAGS} -s miss_msg_det_tb ${DEFINES} -o ${BUILD}/miss_msg_det_tb miss_msg_det.v ${TB_DIR}/miss_msg_det_tb.v
	vvp ${BUILD}/miss_msg_det_tb

tb: moldudp64.v ${TB_DIR}/top_test.v cnt_ones_thermo header len_to_mask miss_msg_det countdown endian_flip
	iverilog ${FLAGS} -s moldudp64_tb ${DEFINES} -o ${BUILD}/tb cnt_ones_thermo.v countdown.v len_to_mask.v endian_flip.v header.v miss_msg_det.v moldudp64.v  ${TB_DIR}/top_test.v

lib:top
	echo "TODO"

run: tb
	vvp ${BUILD}/tb

wave: run
	${VIEW} ${BUILD}/${WAVE_FILE} ${CONF}/${WAVE_CONF}

clean:
	rm -fr ${BUILD}/*
	
