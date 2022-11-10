.PHONY: default
default : main

.PHONY: main
main:
	@rm -f adelfa
	@dune build @install
	@cp _build/default/bin/adelfa.exe ./adelfa

all: main

.PHONY: debug
debug:
	@dune build bin/ --profile release

.PHONY: install
install: main
	@dune install

.PHONY: tar
tar :
	@dune exec ./bundle/bundle.exe

.PHONY: test
test:
	@dune runtest --release

.PHONY: fmt
fmt:
	@dune build @fmt

.PHONY: doc
doc:
	@dune build @doc-private

.PHONY: clean
clean:
	@dune clean
	@rm -f adelfa.tar
	@rm -f adelfa
