(*OCAMLRUNPARAM=p ./exe   pour voir le parsing en détail*)
(* separated_list va être utile *)
(* obtenu sur le site : https://dev.realworldocaml.org/parsing-with-ocamllex-and-menhir.html *)
(*Un problème à cause de la ligne vide entre les use. et le let*)
type ident = string

(*type axiom = string*)

type expr = 
	| ASTNum of int
	| ASTId of ident
	| Requires of expr
	| ASTBinOp of string * expr * expr
	| Ensures of expr 
	| Writes of expr list 
	| Reads of expr list
	| Comment of string 
	| Let of string * expr * expr
	| Div of expr * expr
	| Spec
	| Old of expr 
	| Invariant of expr 
	| Variant of expr 
	| Exclamation of expr 
	| Ref of expr 
	| If of expr * expr * expr option 
	| While of expr * expr list
	| Paran of expr 
	| Brace of expr
	| End_of_line
	| Empty 
	| Into 
	| ForAll of ident list * ident * expr list 


type function_body = expr list


type axiom = {
	name : ident;
	body : expr 
}

type file_decl = {
	uses : ident list ;
	axiomes: axiom option; 
	func_name : ident;
	parameter : ident * expr;
	return_type : string;
	functions : function_body list;
}

