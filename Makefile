.PHONY: clean test lightclick

all: lightclick test

lightclick: src/
	idris --build lightclick.ipkg


clean:
	idris --clean lightclick.ipkg
	make -C tests clean

test:
	make -C tests testbin test
