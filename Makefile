
#FLAGS = -noassert -g
FLAGS = -g

all:
	ocamlc $(FLAGS) -c parser_utils.mli
	ocamlc $(FLAGS) -c parser_utils.ml
	ocamlyacc parser.mly
	ocamlc $(FLAGS) -c parser.mli
	ocamllex lexer.mll
	ocamlc $(FLAGS) -c lexer.ml
	ocamlc $(FLAGS) -c parser.ml
	ocamlc $(FLAGS) -c main.ml
	ocamlc $(FLAGS) -o main parser_utils.cmo lexer.cmo parser.cmo main.cmo

clean:
	rm -f parser.mli lexer.mli *.cmo *.cmi parser.ml lexer.ml main

