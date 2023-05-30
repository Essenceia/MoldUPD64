TB_DIR=tb
BUILD=build
CONF=conf
FLAGS=-g2012
WAVE_FILE=wave.vcd
VIEW=gtkwave
WAVE_CONF=wave.conf
all: top run

cnt_ones_thermo : cnt_ones_thermo.v
	iverilog ${FLAGS} -s cnt_ones_thermo -o ${BUILD}/cnt_ones_thermo cnt_ones_thermo.v

len_to_mask: len_to_mask.v
	iverilog ${FLAGS} -s len_to_mask -o ${BUILD}/len_to_mask len_to_mask.v

header: header.v
	iverilog ${FLAGS} -s header -o ${BUILD}/header header.v

top: top.v ${TB_DIR}/top_test.v cnt_ones_thermo header len_to_mask
	iverilog ${FLAGS} -s top_test -o ${BUILD}/top cnt_ones_thermo.v len_to_mask.v header.v top.v ${TB_DIR}/top_test.v

run: top
	vvp ${BUILD}/top

wave: run
	${VIEW} ${BUILD}/${WAVE_FILE} ${CONF}/${WAVE_CONF}

clean:
	rm -fr ${BUILD}/*
	
