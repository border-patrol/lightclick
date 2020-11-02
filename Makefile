.PHONY: clean test lightclick

all: lightclick test

lightclick: src/
	idris2 --build lightclick.ipkg


clean:
	idris2 --clean lightclick.ipkg
	make -C tests clean


export LIGHT_CLICK_TEST_JUST
export LIGHT_CLICK_TEST_INTERACTIVE
export LIGHT_CLICK_BIN=../../build/exec/lightclick

test:
	make -C tests testbin
	make -C tests test
