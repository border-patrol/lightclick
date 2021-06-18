LCLICK=lightclick
IDRIS2=idris2
HYPERFINE=hyperfine

TARGETDIR = ${CURDIR}/build/exec
TARGET = ${TARGETDIR}/${LCLICK}

bopts ?=

lightclick:
	idris2 --build ${LCLICK}.ipkg


clean:
	idris2 --clean ${LCLICK}.ipkg
	make -C tests clean

clobber: clean
	${MAKE} -C tests clobber
	${RM} -rf build/


testbin:
	${MAKE} -C tests testbin IDRIS2=$(IDRIS2)

test: testbin
	${MAKE} -C tests test \
			 IDRIS2=$(IDRIS2) \
			 LCLICK_BIN=${TARGET} \
			 LCLICK_TEST_U=$(LCLICK_TEST_U) \
			 LCLICK_TEST_O=$(LCLICK_TEST_O)

bench: ${TARGET} testbin
	${MAKE} -C tests bench \
	  IDRIS2=$(IDRIS2) \
	  LCLICK_BIN=${TARGET} \


bench-all: lightclick testbin
	${MAKE} -C tests \
		bench-all \
		LCLICK_BIN=$(abspath $(TARGET))
		LCLICK_BENCH_OPTS=$(bopts)

.PHONY: clobber clean lightclick test testbin bench bench-all
