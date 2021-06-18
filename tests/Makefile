IDRIS2=idris2
HYPERFINE=hyperfine

TARGETDIR = ${CURDIR}/build/exec
TARGET = ${TARGETDIR}/runtests

LCLICK_TEST_U ?= --interactive

testbin:
	${IDRIS2} --build tests.ipkg

test: testbin
	${TARGET} \
	  $(LCLICK_BIN) \
	  --timing \
	  $(LCLICK_TEST_U) \
	  --only $(LCLICK_TEST_O)

bench:
	$(HYPERFINE) --warmup 10 --ignore-failure \
	  -L test 007-firewall/firewall.click,008-core-alliance-swerv-eh1/core-alliance-swerv-eh1-top.click \
	  '$(LCLICK_BIN) {test}'


space :=
space +=
comma := ,

TESTS_RAW = $(shell find . -name "*.click")
TESTS_ABS = $(foreach T,$(TESTS_RAW),$(abspath $(T)))
TESTS     = $(subst $(space),$(comma),$(TESTS_ABS))


bench-all: testbin
	$(HYPERFINE) --ignore-failure \
		     --export-markdown report.md \
		     --export-csv report.csv \
		     -L test $(TESTS) \
		     --warmup 10 \
		     '${LCLICK_BIN} {test}'

clean: clobber
	find . -name 'output' | xargs rm -f

clobber: clean
	${RM} -rf build


.PHONY: testbin test clean clobber bench bench-all
