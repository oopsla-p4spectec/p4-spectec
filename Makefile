SPEC = p4spectec
STAT = p4stat
PERF = p4perf
SPECTEST = p4spectec-test

# Compile

.PHONY: build stat perf spec-test

EXESPEC = p4spec/_build/default/bin/main.exe
EXESTAT = p4spec/_build/default/bin/stat.exe
EXEPERF = p4spec/_build/default/bin/perf.exe
EXESPECTEST = p4spec/_build/default/bin/test.exe

build:
	rm -f ./$(SPEC)
	rm -f ./p4spec/lib/parsing/parser.ml ./p4spec/lib/parsing/parser.mli
	opam switch 5.1.0
	cd p4spec && opam exec -- dune build bin/main.exe && echo
	ln -f $(EXESPEC) ./$(SPEC)

stat:
	opam switch 5.1.0
	cd p4spec && opam exec -- dune build bin/stat.exe && echo
	ln -f $(EXESTAT) ./$(STAT)

perf:
	opam switch 5.1.0
	cd p4spec && opam exec -- dune build bin/perf.exe && echo
	ln -f $(EXEPERF) ./$(PERF)

spec-test:
	opam switch 5.1.0
	cd p4spec && opam exec -- dune build bin/test.exe && echo
	ln -f $(EXESPECTEST) ./$(SPECTEST)

release:
	rm -f ./$(SPEC)
	rm -f ./p4spec/lib/parsing/parser.ml ./p4spec/lib/parsing/parser.mli
	opam switch 5.1.0
	cd p4spec && opam exec -- dune build --profile=release bin/main.exe && echo
	ln -f $(EXESPEC) ./$(SPEC)

# Spec

spec:
	cd docs && make release && cd ..
spec-html:
	cd docs && make release-html && cd ..

# Format

.PHONY: fmt

fmt:
	opam switch 5.1.0
	cd p4spec && opam exec dune fmt

# Cleanup

.PHONY: clean

clean:
	rm -f ./$(SPEC)
	cd p4spec && dune clean
