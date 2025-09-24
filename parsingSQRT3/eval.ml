open Ast
(*Les fonctions pour l'affichage ont été réalisé par mistral.ai car j'avais pas envie d'écrire tout ça alors que je viens de réussir et aussi pour 
visualiser rapidement l'ast produite par le parseur*)

let rec unconcat_list (ls :string list) : string =
  match ls with 
  |[] -> ""
  |h::t -> h ^ (unconcat_list t)
;;
let rec string_of_expr = function
  | ASTNum n -> "ASTNum " ^ string_of_int n
  | ASTId id -> "ASTId " ^ id
  | Requires e -> "Requires (" ^ string_of_expr e ^ ")"
  | ASTBinOp (op, e1, e2) -> "ASTBinOp (" ^ op ^ ", " ^ string_of_expr e1 ^ ", " ^ string_of_expr e2 ^ ")"
  | Ensures e -> "Ensures (" ^ string_of_expr e ^ ")"
  | Writes e -> "Writes (" ^  (unconcat_list (List.map string_of_expr e)) ^ ")"
  | Comment c -> "Comment " ^ c
  | Let (s,e1,e2) -> "Let (" ^ s ^ ", " ^ string_of_expr e1 ^ ", " ^ string_of_expr e2 ^ ")"
  | Spec -> "Spec "
  | Old e -> "Old (" ^ string_of_expr e ^ ")"
  | Invariant e -> "Invariant (" ^ string_of_expr e ^ ")"
  | Variant e -> "Variant (" ^ string_of_expr e ^ ")"
  | Exclamation e -> "Exclamation (" ^ string_of_expr e ^ ")"
  | Ref e -> "Ref (" ^ string_of_expr e ^ ")"
  | If (e1, e2, e3_opt) ->
      let e3_str = match e3_opt with
        | None -> "None"
        | Some e3 -> string_of_expr e3
      in
      "If (" ^ string_of_expr e1 ^ ", " ^ string_of_expr e2 ^ ", " ^ e3_str ^ ")"
  | While (e1, e2) -> "While (" ^ string_of_expr e1 ^ ", " ^ " dans le do " ^ ")"
  | Paran e -> "Paran (" ^ string_of_expr e ^ ")"
  | Brace e -> "Brace (" ^ string_of_expr e ^ ")"
  | End_of_line -> "End_of_line"
  | Empty -> "Empty"
  | Into -> "Into"
  | ForAll (id_ls, id, e) -> "forall " ^ (unconcat_list id_ls) ^ " : " ^id ^". body"

let string_of_function_body fb =
  "[" ^ String.concat "; " (List.map string_of_expr fb) ^ "]"

let eval fd =
  let uses_str = "Uses: [" ^ String.concat "; " fd.uses ^ "]" in
  let axiomes_str = match fd.axiomes with
    | None -> "Axiomes: None"
    | Some a -> "Axiomes: "
  in
  let func_name_str = "Func Name: " ^ fd.func_name in
  let parameter_str = "Parameter: (" ^ fst fd.parameter ^ ", " ^ string_of_expr (snd fd.parameter) ^ ")" in
  let return_type_str = "Return Type: " ^ fd.return_type in
  let functions_str = "Functions: [" ^ String.concat "; " (List.map string_of_function_body fd.functions) ^ "]" in
  uses_str ^ "\n" ^ axiomes_str ^ "\n" ^ func_name_str ^ "\n" ^ parameter_str ^ "\n" ^ return_type_str ^ "\n" ^ functions_str
