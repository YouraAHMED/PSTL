{
  open Parser
  exception Eof
}

let integer = ['0'-'9']+
let alpha = ['a'-'z''A'-'Z''_']['a'-'z''A'-'Z''0'-'9''_']* ('.' ['a'-'z''A'-'Z''0'-'9''_']+)*
let eol = '\n'
let whitespace = [' ' '\t' '\r' '\n']+
let comment = "/*" [^ '*']* "*/"

rule token = parse
    | "use"     { print_endline "USE"; USE }
    | "let"     { print_endline "LET"; LET }
    | "requires" { print_endline "REQUIRES"; REQUIRES }
    | "<>"      { print_endline "EMPTY"; EMPTY }
    | "ensures"  { print_endline "ENSURES"; ENSURES }
    | "while"  { print_endline "WHILE"; WHILE }
    | "invariant"  { print_endline "INVARIANT"; INVARIANT }
    | "variant"  { print_endline "VARIANT"; VARIANT }
    | "do"      { print_endline "DO"; DO}
    | "done"    { print_endline "DONE"; DONE}
    | "/\\"     { print_endline "AND"; AND }
    | "<->"     { print_endline "EQUIVALENT"; EQUIVALENT }
    | "->"      { print_endline "INTO"; INTO }
    | "<="      { print_endline "LEQ"; LEQ }
    | ">="      { print_endline "GEQ"; GEQ }
    | "<"       { print_endline "LT"; LT }
    | ">"       { print_endline "GT"; GT }
    | "="       { print_endline "EQUAL"; EQUAL }
    | "*"       { print_endline "TIMES"; TIMES }
    | "+"       { print_endline "PLUS"; PLUS }
    | "-"       { print_endline "MINUS"; MINUS }
    | "("       { print_endline "LPAR"; LPAR }
    | ")"       { print_endline "RPAR"; RPAR }
    | ":"       { print_endline "COLON"; COLON }
    | "{"       { print_endline "LBRACE"; LBRACE }
    | "}"       { print_endline "RBRACE"; RBRACE }
    | "!"       { print_endline "EXCLAMATION"; EXCLAMATION }
    | ","       { print_endline "VIRGULE"; VIRGULE}
    | "."       { print_endline "POINT"; POINT}
    | "forall"  { print_endline "FORALL"; FORALL}
    | "ref"     { print_endline "REF"; REF }
    | "old"     { print_endline "OLD"; OLD }
    | "writes"  { print_endline "WRITES"; WRITES }
    | "in"      { print_endline "IN"; IN}
    | "spec"    { print_endline "SPEC"; SPEC}
    | "axiom"   { print_endline "AXIOM"; AXIOM}
    | integer as num {print_endline ("NUM " ^ num); NUM (int_of_string num) }
    | alpha as id { print_endline ("IDENT " ^ id); IDENT id }
    | "(*"               { comment lexbuf }  (* Comment until closing *)
    | eol           { print_endline "EOL"; EOL }
    | whitespace { token lexbuf }  
    | eof       { print_endline "EOF" ;EOF}

and comment = parse
| "*)"    { token lexbuf }
| ['\n']  { Lexing.new_line lexbuf; comment lexbuf }
| _       {comment lexbuf }