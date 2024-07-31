merge_demo: merge_sort.mli merge_sort.ml
	opam exec -- ocamlc -c merge_sort.mli
	opam exec -- ocamlc -c merge_sort.ml
	opam exec -- ocamlopt -o merge_demo merge_sort.ml merge_demo.ml

run: merge_demo
	./merge_demo

clean:
	rm -fv *.o *.cmx *.cmo *.cmi merge_demo
.PHONY: clean
