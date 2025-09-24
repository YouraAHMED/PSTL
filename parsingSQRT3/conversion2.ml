open Ast
open Eval 
(* Fichier pour convertir l'ast produite en un fichier .why *) 

let spec_seen = ref false ;; (* variable qui me sert à savoir si l'objet spec à déjà été vu *) (*pas utilisé*)

let rec affiche_uses fd ls = 
  match ls with 
  | [] -> ()
  | h :: t -> Printf.fprintf fd "use %s\n" h;
              affiche_uses fd t

let rec astID_to_string ast = 
  match ast with 
  | ASTId id -> id
  | Ref exp -> "ref " ^ astID_to_string exp
  | _ -> ""

let rec astWrite_to_string ls = 
  let aux = function
  | ASTId id -> "" ^ id ^ ""
  | _ -> ""
  in 
  match ls with 
  | [] -> ""
  | elm::[] -> aux elm
  | h::t -> aux h ^ ", " ^ (astWrite_to_string t)


let rec is_id_in_list (ls : string list) (elm : string) : bool = 
  match ls with 
  |[] -> false
  |h::t -> if h=elm then  true else is_id_in_list t elm
;;

(* Les parametre parametre et verif de string_of_expr sont là pour les raisons suivantes :
parametre c'est pour savoir si on doit ajouter le "!" pour la référence si la variable qu'on voit est un parametre
verif existe afin de ne pas générer des "!!" ou des "writes {!x}" car seulement laisser un test d'égalité sur le cas 
ASTId ferait que le "!" soit sur toutes les variables x ce qu'on ne veut pas *)
let rec string_of_expr (parametre : ident) (ref : string list) (verif : bool) = function
  | ASTNum n -> "" ^ (string_of_int n) ^ ""
  | ASTId id -> if (id=parametre||(is_id_in_list ref id )) && verif=true then "!" ^ id ^ "" else  "" ^ id ^ ""; 
  | Requires e -> " requires { " ^ string_of_expr parametre ref verif e  ^ " }\n" 
  | ASTBinOp (op, e1, e2) -> if e1==End_of_line || e1 == Empty || e2 ==End_of_line || e2 ==Empty then ""
    else (string_of_expr parametre ref verif e1 ) ^ " " ^ op ^" " ^ (string_of_expr parametre ref verif e2 )
  | Ensures e -> " ensures { " ^ string_of_expr parametre ref verif e  ^ " }\n" 
  | Writes e -> " writes { " ^ astWrite_to_string e ^ " }\n" 
  | Comment _ -> ""
  | Let (_,_,_) -> ""
  | Spec -> ""
  | Old e -> " old " ^ string_of_expr parametre ref verif e 
  | Invariant _ -> ""
  | Variant _ -> ""
  | Exclamation e -> "!"^string_of_expr parametre ref false e 
  | Ref _ -> ""
  | If (_, _, _) -> ""
  | While (_, _) -> ""
  | Paran e -> "(" ^ string_of_expr parametre ref verif e  ^ ")"
  | Brace _ -> ""
  | End_of_line -> ""
  | Empty -> ""
  | Into -> ""
  | ForAll (_,_,_) -> ""

let are_both_id_num (a : expr) (b : expr) : bool = 
  match a,b with 
  |ASTId(g),ASTId(d) -> true
  |ASTId(g),ASTNum(d) -> true 
  |ASTNum(g),ASTId(d) -> true 
  |ASTNum(g),ASTNum(d) -> true 
  |_,_ -> false 
(* pas utilisé *) (* idée qui a été mis dans le placard *)
let rec string_of_spec_body (parametre : ident) (verif : bool) = function
  | ASTNum n -> if !spec_seen then "" ^ (string_of_int n) ^ "" else ""
  | ASTId id -> if !spec_seen then if id=parametre && verif=true then "!" ^ id ^ "" else "" ^ id ^ "" else "" 
  | Requires e -> if !spec_seen then " requires { " ^ string_of_spec_body parametre verif e  ^ " }\n" else "" 
  | ASTBinOp (op, e1, e2) -> if e1==End_of_line || e1 == Empty || e2 ==End_of_line || e2 ==Empty then ""
    else (string_of_spec_body parametre verif e1 ) ^ " " ^ op ^" " ^ (string_of_spec_body parametre verif e2 )
  | Ensures e -> if !spec_seen then " ensures { " ^ string_of_spec_body parametre verif e  ^ " }\n" else ""
  | Writes e -> if !spec_seen then " writes { " ^ astWrite_to_string e ^ " }\n" else ""
  | Comment _ -> ""
  | Let (_,_,_) -> ""
  | Spec -> spec_seen := true; ""
  | Old e -> if !spec_seen then " old " ^ string_of_spec_body parametre verif e else "" 
  | Invariant _ -> ""
  | Variant _ -> ""
  | Exclamation e -> if !spec_seen then "!"^string_of_spec_body parametre false e else ""
  | Ref _ -> ""
  | If (_, _, _) -> ""
  | While (_, _) -> ""
  | Paran e -> if !spec_seen then "(" ^ string_of_spec_body parametre verif e  ^ ")" else ""
  | Brace _ -> ""
  | End_of_line -> ""
  | Empty -> ""
  | Into -> "Into"
  | ForAll (_,_,_) -> ""
;;
(* *)
let rec stop_spec_expr_string (parametre : ident) (verif : bool) = function 
  | ASTNum n -> "" ^ (string_of_int n) ^ ""
  | ASTId id -> if id=parametre && verif=true then "!" ^ id ^ "" else "" ^ id ^ ""; 
  | Requires e -> "  requires { " ^ stop_spec_expr_string parametre verif e  ^ " }\n" 
  | ASTBinOp (op, e1, e2) -> if e1==End_of_line || e1 == Empty || e2 ==End_of_line || e2 ==Empty then ""
    else (stop_spec_expr_string parametre verif e1 ) ^ " " ^ op ^" " ^ (stop_spec_expr_string parametre verif e2 )
  | Ensures e -> "  ensures { " ^ stop_spec_expr_string parametre verif e  ^ " }\n" 
  | Writes e -> "" 
  | Comment _ -> ""
  | Let (id,value,e) -> " let "^id ^" = "^ (stop_spec_expr_string parametre verif value ) ^" in\n" ^ (stop_spec_expr_string parametre verif e ) 
  | Spec -> ""
  | Old e -> " old " ^ stop_spec_expr_string parametre verif e 
  | Invariant _ -> ""
  | Variant _ -> ""
  | Exclamation e -> " !"^stop_spec_expr_string parametre false e 
  | Ref e -> "ref " ^ stop_spec_expr_string parametre verif e 
  | If (_, _, _) -> ""
  | While (_, _) -> ""
  | Paran e -> "(" ^ stop_spec_expr_string parametre verif e  ^ ")"
  | Brace _ -> ""
  | End_of_line -> ""
  | Empty -> ""
  | Into -> ""
  | ForAll (_,_,_) -> ""
;;

let are_both_id_num (a : expr) (b : expr) : bool = (*work as intended*)
  match a,b with 
  |ASTId(g),_ -> true
  |_,ASTNum(d) -> true 
  |_,ASTId(d) -> true 
  |ASTNum(g),_ -> true 
  |Old(e),_ -> true 
  |_,Old(e) -> true 
  |Exclamation(e),_ -> true 
  |_,Exclamation(e) -> true 
  |_,_ -> false 
;;

(* sert à séparer la liste produite par l'ast qui devrait être une liste de liste séparé par le signe = entre les instructions *)
(* dans une vraie liste de liste séparé ou chaque liste correspond à un bloc d'expression entre les "=" *)
let rec separe_list_expr (ls: expr list) (result : expr list list ) : expr list list = (* valide aussi *) 
  let rec aux (lsv : expr list) (storage : expr list) (result_acc : expr list list) : (expr list * expr list list) =
    match lsv with
    |[] -> ([],result_acc @ [storage])
    |h::t -> match h with
            |ASTBinOp(op,g,d) -> if (are_both_id_num g d ) then (aux t (storage @ [h]) result_acc )
                              else ([d] @ t,result_acc @ [(storage @ [g])] )
            |_ -> aux t (storage @ [h]) result_acc
  in
  if ls = [] then result else let res = (aux ls [] result) in separe_list_expr (fst res) (snd res)
;;
(* renvoie true si Spec est dans l'expression false sinon *)
let rec is_spec = function 
| ASTNum n -> false
| ASTId id -> false
| Requires e -> is_spec e
| ASTBinOp (_, e1, e2) -> is_spec e1 || is_spec e2 
| Ensures e -> is_spec e 
| Writes e -> false
| Comment _ -> false
| Let (_,e1,e2) -> is_spec e1 || is_spec e2 
| Spec -> true 
| Old e -> is_spec e 
| Invariant _ -> false
| Variant _ -> false
| Exclamation e -> is_spec e 
| Ref _ -> false 
| If (_, _, _) -> false
| While (_, _) -> false
| Paran e -> is_spec e  
| Brace _ -> false
| End_of_line -> false
| Empty -> false
| Into -> false
| ForAll (_,_,_) -> false
;;

(* sert à trouver la liste qui contient l'expression spec *)
let find_spec (lss : expr list list) : int = (* validé *) 
  let rec aux (ls : expr list ) : bool  = 
    match ls with 
    |[] -> false 
    |h :: t -> is_spec h || aux t
  in 
    let rec aux2 (lss : expr list list) (n : int) : int =
      match lss with 
      |[] -> -1 
      |h::t -> let value = aux h in if value then n else aux2 t (n+1) 
    in
      aux2 lss 0 
;;
(* renvoie une liste d'expression de la liste de liste d'expression *)
let rec get_ls_from_lss (lss : expr list list) (index : int) : expr list = 
  match lss with 
  |[] -> []
  |h::t -> if index = 0 then h else get_ls_from_lss t (index-1)
;;
(* prend une liste de liste d'expression et renvoie la liste de liste sans la liste qui contient l'élément spec indiqué par l'index de cette liste *)
let rec get_all_but_spec (lss : expr list list) (index : int) (cpt : int): expr list list =
  match lss with 
  |[] -> []
  |h::t -> if cpt = index then get_all_but_spec t index (cpt+1) else h::(get_all_but_spec t index (cpt+1))
;;
(* construit la chaine de caractère des expressions de la liste avec string_of_expr *)
let rec ls_expr (ls: expr list) parametre (ref : string list) =
  match ls with
  | [] -> ""
  | h :: t -> string_of_expr parametre ref true h ^ ls_expr t parametre ref
;;
(* construit la chaine de caractère de la liste de liste représentant ses expressions en faisant appel à ls_expr pour chaque liste *)
let rec main_body (lss: function_body list) parametre (ref : string list): string =
  match lss with
  | [] -> ""
  | h :: t -> (ls_expr h parametre ref) ^ main_body t parametre ref
;;
(* même chose que ls_expr mais doit être servi uniquement pour corps de la fonction sqrt *)
let rec ls_expr_1 (ls: expr list) (index:int) (ls_param : string ) parametre =
  match ls with
  | [] -> ""
  | h :: t -> if index != 0 then stop_spec_expr_string parametre true h ^ ls_expr_1 t index ls_param parametre else 
              "=" ^ stop_spec_expr_string parametre true h ^ " sqrt1_spec " ^ ls_param ^ ";\n" 
;;
(* même chose que main_body mais doit être servi uniquement pour corps de la fonction sqrt *)
let rec main_body_1 (lss: function_body list) (index : int ) (ls_param : string ) parametre : string =
  match lss with
  | [] -> ""
  | h :: t -> (ls_expr_1 h index ls_param parametre) ^ main_body_1 t (index-1) ls_param parametre
;;
(* fonction qui permet d'insérer une liste d'expression à un index précis d'une liste de liste d'expression*)
(* n'a pas été utile pour le moment *)
let rec insert_listAt (lss : expr list list ) (ls : expr list ) (index : int) : expr list list =
  match lss with 
  |[]->if index = 0 then ls :: [] else [] 
  |h::t -> if index = 0 then ls :: (h :: t) else h :: (insert_listAt t ls (index-1) )
;;
(* permet d'obtenir les paramètres d'une val spec *)
let rec spec_param (lss : expr list list ) : ident list = (* validé *)(* ne pas oublier d'ajouter le paramètre de sqrt dans la liste resultat*)
  let rec aux = function
    | ASTNum n -> []
    | ASTId id -> []
    | Requires e -> aux e
    | ASTBinOp (_, e1, e2) -> aux e1 @ aux e2 
    | Ensures e -> aux e 
    | Writes e -> []
    | Comment _ -> []
    | Let (x,e1,e2) -> [x] @ aux e1 @ aux e2 
    | Spec -> ["spec"]
    | Old e -> [] 
    | Invariant _ -> []
    | Variant _ -> []
    | Exclamation e -> [] 
    | Ref _ -> [] 
    | If (_,_, _) -> []
    | While (_, _) -> []
    | Paran e -> []   
    | Brace _ -> []
    | End_of_line -> []
    | Empty -> []
    | Into -> []
    | ForAll (_,_,_) -> []
  in let rec aux1 (ls : expr list ) : ident list = 
    match ls with 
    |[] -> []
    |h::t -> aux h @ aux1 t 
  in let rec aux2 (lss : expr list list ) (index : int) (resultat : ident list): ident list =
    match lss with 
    |[] -> []
    |h::t -> if index < 0 then resultat else aux2 t (index-1) (resultat @ (aux1 h)) 
  in let rec aux3 (id_ls : ident list) : ident list = 
    match id_ls with 
    |[] -> []
    |h::t -> if h="spec" then [] else h :: (aux3 t)  
  in aux3 (aux2 lss (find_spec lss) [])
;;
(* permet de transformer une liste de chaine de caractère en une chaine *)
let rec unconcat_list (ls :string list ) : string = 
  match ls with 
  |[] -> ""
  |h::t -> h ^ " "^(unconcat_list t)
;;  
(* permet d'écrire les paramètres de val spec *)
let rec spec_param_toString (ls : string list) : string = 
  match ls with 
  |[] -> ""
  |h::t -> "("^h ^ " : ref int) " ^ (spec_param_toString t)
;;




let param_list_to_string l =
  String.concat " " (List.map (fun s -> s ^ " : ref int") l)

(* === Étape 3 uniquement : extraction d'une spec imbriquée dans une boucle === *)

let conv_etape3 ast name : string = 
  let file = open_out_gen [Open_creat; Open_trunc; Open_text] 0o666 name in
  
  (* Affiche les "use" *)
  affiche_uses file ast.uses;

  (* Affiche les axiomes si présents *)
  (match ast.axiomes with
  | Some ax -> Printf.fprintf file "\naxiom %s : forall x y : int. 0 <= x -> 0 <= y -> (x < y <-> x*x < y*y)\n\n" ax.name
  | None -> ());

  (* Analyse de la fonction *)
  let ast_body = separe_list_expr (get_ls_from_lss ast.functions 0) [] in 
  let index_spec = find_spec ast_body in 
  let ref_params = spec_param ast_body in
  let parametre = fst ast.parameter in

  (* Génère la val sqrt3_spec *)
  let val_spec_name = Printf.sprintf "%s3_spec" ast.func_name in
  let val_spec = Printf.sprintf "val %s (%s : ref int) %s : ()\n" val_spec_name parametre (spec_param_toString ref_params) in 
  let spec_exprs = get_ls_from_lss ast_body index_spec in
  let spec_body = List.fold_left (fun acc expr -> acc ^ string_of_expr parametre ref_params true expr) "" spec_exprs in 
  Printf.fprintf file "%s%s\n" val_spec spec_body;

  (* Génère la let sqrt2 *)
  let sqrt2_args = parametre :: ref_params in
  let fct2_name = Printf.sprintf "%s2" ast.func_name in
  Printf.fprintf file "let %s (%s) : ()\n" fct2_name (param_list_to_string sqrt2_args);
  Printf.fprintf file "  requires { 0 <= !r }\n  requires { !r + 1 < !h }\n  requires { !r * !r <= !x < !h * !h }\n";
  Printf.fprintf file "  reads { x, r, h }\n  writes { r, h }\n";
  Printf.fprintf file "  ensures { 0 <= !r }\n  ensures { 0 <= !h }\n  ensures { (old !r) * (old !r) <= !r * !r <= !x < !h * !h <= (old !h * old !h) }\n";
  Printf.fprintf file "  ensures { (!h - !r) < old (!h - !r) }\n  ensures { !x = old !x }\n=\n";
  Printf.fprintf file "  let m = ref 0 in\n  %s r m h;\n  if !m * !m < !x then r := !m\n  else if !m * !m > !x then h := !m\n  else (r := !m; h := !m + 1)\n\n" val_spec_name;

  (* Génère le sqrt0 *)
  let sqrt0_name = ast.func_name ^ "0" in
  Printf.fprintf file "let %s (%s : %s) : int\n" sqrt0_name parametre (astID_to_string (snd ast.parameter));
  Printf.fprintf file "  requires { !%s >= 0 }\n" parametre;
  Printf.fprintf file "  writes { %s }\n" parametre;
  Printf.fprintf file "  ensures { result * result <= !%s <= (result + 1) * (result + 1) }\n" parametre;
  Printf.fprintf file "  ensures { !%s = old !%s }\n" parametre parametre;
  Printf.fprintf file "=\n  let r = ref 0 in\n  let h = ref (!%s + 1) in\n  while !h <> !r + 1 do\n    invariant { 0 <= !r /\ 0 <= !h /\ old !r * old !r <= !r * !r <= !x < !h * !h <= old !h * old !h }\n    variant { !h - !r }\n    %s %s r h\n  done;\n  !r\n" fct2_name parametre;

  close_out file;
  eval ast