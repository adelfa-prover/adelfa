.PHONY: default
default : main

.PHONY: main
main:
	@dune build @install --profile release

.PHONY: debug
debug:
	@dune build bin/ --profile release

.PHONY: install
install :
	@dune install

.PHONY: tar
tar :
	@tar -cvf adelfa.tar Makefile README system_description.txt system_reference.txt --exclude=**/*~ bin/ src/ test/ emacs/ _tags --exclude=examples/first_order/lists_2 --exclude=examples/first_order/lists_3 --exclude=examples/first_order/lists_4 --exclude=examples/lambda_calc/draft_snippets --exclude=examples/lambda_calc/strongly_normalizing --exclude=examples/lambda_calc/subject_reduction/informal --exclude=examples/lambda_calc/subject_reduction/reduce.lf --exclude=examples/lambda_calc/subject_reduction/large_step.ath --exclude=examples/lambda_calc/subject_reduction/small_step.ath --exclude=examples/prog_lang/miniml --exclude=examples/prog_lang/poplmark/twelf_files --exclude=examples/prog_lang/poplmark/proof_structure.txt examples/

.PHONY: test
test:
	@dune exec test/test.exe --profile release

.PHONY: clean
clean:
	@dune clean
	@rm -f adelfa.tar
