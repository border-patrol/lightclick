CLICK = ../../build/exec/lightclick

test:
	./build/exec/runtests $(CLICK) --timing $(INTERACTIVE) --only ${only}

testbin:
	idris2 --build tests.ipkg

clean:
	rm -r build
	find . -name '*.ibc' | xargs rm -f
	find . -name 'output' | xargs rm -f
