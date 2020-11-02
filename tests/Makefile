.PHONY: testbin test

#LIGHT_CLICK_TEST_INTERACTIVE ?= --interactive

test:
	./build/exec/runtests $(LIGHT_CLICK_BIN) --timing $(LIGHT_CLICK_TEST_INTERACTIVE) --only $(LIGHT_CLICK_TEST_JUST)

testbin:
	idris2 --build tests.ipkg

clean:
	rm -r build
	find . -name '*.ibc' | xargs rm -f
	find . -name 'output' | xargs rm -f
