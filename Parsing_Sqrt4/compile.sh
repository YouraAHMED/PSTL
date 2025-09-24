#!/bin/sh

ocamllex lexer.mll;
ocamlc -c ast.ml;
ocamlc -c eval.ml;
ocamlc -c conversion4.ml;
ocamlyacc parser.mly;
ocamlc -c parser.mli;
ocamlc -c lexer.ml;
ocamlc -c parser.ml;
ocamlc -c main.ml;
ocamlc -o main ast.cmo eval.cmo conversion4.cmo lexer.cmo parser.cmo main.cmo