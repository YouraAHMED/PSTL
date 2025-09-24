open Ast
open Eval 
open Conversion2 

let _ =
  let filename = Sys.argv.(1) in
  let output =
    if Array.length Sys.argv > 2 then Sys.argv.(2)
    else "output.why"
  in
  let channel = open_in filename in
  let lexbuf = Lexing.from_channel channel in
  let ast = Parser.prog Lexer.token lexbuf in
  let result = conversion2.conv_etape3 ast output in
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
