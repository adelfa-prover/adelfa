.PHONY: default
default : main

.PHONY: main
main:
	@dune build @install --release

.PHONY: debug
debug:
	@dune build bin/ --profile release

.PHONY: install
install: main
	@dune install

.PHONY: tar
tar :
	@tar -cvf adelfa.tar Makefile README system_description.txt system_reference.txt --exclude=**/*~ bin/ src/ test/ emacs/ _tags --exclude=examples/first_order/lists_2 --exclude=examples/first_order/lists_3 --exclude=examples/first_order/lists_4 --exclude=examples/lambda_calc/draft_snippets --exclude=examples/lambda_calc/strongly_normalizing --exclude=examples/lambda_calc/subject_reduction/informal --exclude=examples/lambda_calc/subject_reduction/reduce.lf --exclude=examples/lambda_calc/subject_reduction/large_step.ath --exclude=examples/lambda_calc/subject_reduction/small_step.ath --exclude=examples/prog_lang/miniml --exclude=examples/prog_lang/poplmark/twelf_files --exclude=examples/prog_lang/poplmark/proof_structure.txt examples/

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
