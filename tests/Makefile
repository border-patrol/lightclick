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

bench: testbin
	$(HYPERFINE) --warmup 10 \
	  -L test 007-firewall,008-core-alliance-swerv-eh1 \
	  '$(TARGET) $(LCLICK_BIN) --only {test}'


space :=
space +=
comma := ,

TESTS_LIST = $(shell cat tests.txt)
TESTS = $(subst $(space),$(comma),$(TESTS_LIST))

bench-all: testbin
	$(HYPERFINE) --export-markdown report.md \
		     --export-csv report.csv \
		     -L test $(TESTS) \
		     --warmup 10 \
		     '$(TARGET) $(LCLICK_BIN) --only {test}'

clean: clobber
	find . -name 'output' | xargs rm -f

clobber: clean
	${RM} -rf build


.PHONY: testbin test clean clobber bench bench-all
