open Ast
open Eval 
open Conversion4 

let _ =
  let filename = Sys.argv.(1) in
  let channel = open_in filename in
  let lexbuf = Lexing.from_channel channel in
  let ast = Parser.prog Lexer.token lexbuf in
  let result = Conversion4.conv ast "sqrt4.why" in
  print_string result; print_newline(); flush stdout
 
(*
let _ =
  let filename = Sys.argv.(1) in
  let channel = open_in filename in
  let lexbuf = Lexing.from_channel channel in
  let ast = Parser.prog Lexer.token lexbuf in
  let result = Eval.eval ast  in
  print_string result; print_newline(); flush stdout
*)
