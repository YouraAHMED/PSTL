#!/bin/sh

ocamllex lexer.mll;
ocamlc -c ast.ml;
y
ocamlc -o main ast.cmo eval.cmo conversion3.cmo lexer.cmo parser.cmo main.cmo