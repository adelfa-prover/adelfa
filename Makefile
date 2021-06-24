.PHONY: default
default : main

.PHONY: main
main :
	ocamlbuild -yaccflags -v -use-ocamlfind main.byte
	mv main.byte adelfa.byte

.PHONY: debug
debug :
	ocamlbuild -yaccflags -v -use-ocamlfind -tag 'debug' main.byte
	mv main.byte adelfa.byte

.PHONY: tar
tar :
	tar -cvf adelfa.tar Makefile README system_description.txt system_reference.txt --exclude=**/*~ src/ emacs/ _tags --exclude=examples/first_order/lists_2 --exclude=examples/first_order/lists_3 --exclude=examples/first_order/lists_4 --exclude=examples/lambda_calc/draft_snippets --exclude=examples/lambda_calc/strongly_normalizing --exclude=examples/lambda_calc/subject_reduction/informal --exclude=examples/lambda_calc/subject_reduction/reduce.lf --exclude=examples/lambda_calc/subject_reduction/large_step.ath --exclude=examples/lambda_calc/subject_reduction/small_step.ath --exclude=examples/prog_lang/miniml --exclude=examples/prog_lang/poplmark/twelf_files --exclude=examples/prog_lang/poplmark/proof_structure.txt examples/


.PHONY: test
test:
	ocamlbuild -use-ocamlfind test.byte

.PHONY: clean
clean:
	ocamlbuild -clean
	rm adelfa.tar
