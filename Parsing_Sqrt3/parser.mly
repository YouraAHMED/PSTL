%{
open Ast
%}

%token USE LET REQUIRES ENSURES LPAR RPAR COLON LBRACE RBRACE EMPTY EQUAL EOL EXCLAMATION REF OLD WRITES IN SPEC VIRGULE POINT FORALL 
%token AXIOM INTO EQUIVALENT WHILE INVARIANT VARIANT AND DO DONE COLON_EQUAL IF THEN ELSE SEMI
%token LEQ GEQ LT GT PLUS MINUS TIMES 
%token EOF

%token <int> NUM
%token <string> IDENT

%start prog
%type <Ast.file_decl> prog
%type <Ast.ident list> ls_uses 
%type <Ast.function_body list> body
%type <Ast.expr list> exprlist
%type <Ast.axiom> axiome
%% 


prog : 
    | ls_uses axiome LET IDENT LPAR IDENT COLON REF IDENT RPAR COLON IDENT EQUAL body EOF
      { { uses = $1 ; axiomes = Some($2) ; func_name = $4 ; parameter = ($6, Ref (ASTId $9)) ; return_type = $12 ; functions = $14 } }
    | ls_uses LET IDENT LPAR IDENT COLON REF IDENT RPAR COLON IDENT EQUAL body EOF
      { { uses = $1 ; axiomes = None ; func_name = $3 ; parameter = ($5, Ref (ASTId $8)) ; return_type = $11 ; functions = $13 } }
    ;

axiome :
    |AXIOM IDENT COLON ax_body { {name = $2 ; body = $4} }
    ;

ax_body: 
    | FORALL ls_ident COLON IDENT POINT axiom_exprlist { ForAll ($2, $4, $6) }
    ;
ls_ident:
    | IDENT { [$1]}
    | IDENT ls_ident { $1 :: $2 }
    ;

ls_uses:
    | use_line ls_uses { $1 :: $2 }
    |                    { [] }
    ;
use_line:
    | USE IDENT EOL { $2 }
    | USE IDENT { $2 }
    ;

body: exprlist_equal { $1 } ;

exprlist_equal:
    | exprlist { [$1] }
    | exprlist EQUAL exprlist_equal { $1 :: $3 }
;

exprlist:
    | expr { [$1] }
    | expr exprlist { $1 :: $2 }
;

writelist:
    | expr { [$1] }
    | expr VIRGULE exprlist { $1 :: $3 }
;
axiom_exprlist:
    | axiom_expr { [$1] }
    | axiom_expr axiom_exprlist { $1 :: $2 }
;

axiom_expr :
        | INTO {Into}
        | LPAR axiom_expr RPAR {Paran $2}
        | axiom_expr EQUIVALENT axiom_expr {ASTBinOp ("<->", $1, $3)}
        | axiom_expr EQUAL axiom_expr {ASTBinOp ("=", $1, $3)}
        | axiom_expr PLUS axiom_expr {ASTBinOp ("+", $1, $3)}
        | axiom_expr MINUS axiom_expr {ASTBinOp ("-", $1, $3)}
        | axiom_expr TIMES axiom_expr {ASTBinOp ("*", $1, $3)}
        | axiom_expr LEQ axiom_expr {ASTBinOp ("<=", $1, $3)}
        | axiom_expr GEQ axiom_expr {ASTBinOp (">=", $1, $3)}
        | axiom_expr LT axiom_expr {ASTBinOp ("<", $1, $3)}
        | axiom_expr GT axiom_expr {ASTBinOp (">", $1, $3)}
        | IDENT {ASTId($1)}
        | NUM {ASTNum($1)}
        ;
expr :    expr EMPTY expr {ASTBinOp ("<>", $1, $3)}
        | LET IDENT EQUAL expr IN expr {Let ($2, $4, $6)}
        | IF expr THEN expr ELSE expr {If ($2, $4, Some($6))}
        | IF expr THEN expr {If ($2, $4,None)}
        | expr SEMI expr {ASTBinOp (";", $1, $3)}
        | SPEC {Spec}  
        | INTO {Into}
        | REF expr {Ref $2}
        | REQUIRES LBRACE expr RBRACE {Requires $3}
        | ENSURES LBRACE expr RBRACE {Ensures $3}
        | LPAR expr RPAR {Paran $2}
        | WHILE expr DO exprlist DONE {While ($2,$4)}
        | VARIANT LBRACE expr RBRACE {Variant $3}
        | INVARIANT LBRACE expr RBRACE {Invariant $3}
        | expr AND expr {ASTBinOp ("/\\", $1, $3)}
        | expr EQUIVALENT expr {ASTBinOp ("<->", $1, $3)}
        | expr EQUAL expr {ASTBinOp ("=", $1, $3)}
        | expr COLON_EQUAL expr {ASTBinOp (":=", $1, $3)}
        | expr PLUS expr {ASTBinOp ("+", $1, $3)}
        | expr MINUS expr {ASTBinOp ("-", $1, $3)}
        | expr TIMES expr {ASTBinOp ("*", $1, $3)}
        | expr LEQ expr {ASTBinOp ("<=", $1, $3)}
        | expr GEQ expr {ASTBinOp (">=", $1, $3)}
        | expr LT expr {ASTBinOp ("<", $1, $3)}
        | expr GT expr {ASTBinOp (">", $1, $3)}
        | EOL {End_of_line}
        | OLD expr {Old $2}
        | WRITES LBRACE writelist RBRACE {Writes $3}
        | IDENT {ASTId($1)}
        | NUM {ASTNum($1)}
        | EXCLAMATION expr {Exclamation $2}
        | EMPTY {Empty}
;