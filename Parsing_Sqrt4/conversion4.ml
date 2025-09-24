open Ast 
open Eval 
(* Fichier pour convertir l'ast produite en un fichier .why *) 

let empty_seen = ref false ;; (* variable qui me sert à savoir si l'objet <> à déjà été vu à la fin du fichier*) (*pas utilisé*)
let spec_arg = ref "" ;; (* sert à mettre les paramètres de la fonction spec dans une variable pour les afficher dans le .why quand spec est appelé*)
let first_ensures = ref true ;; (* sert à savoir si on est dans le premier ensures du corps de la fonction sqrt*)
let requires_val = "requires { !r + 1 < !h }";;
let requires_body = " requires { 0 <= !r }
  requires { !r + 1 < !h }
  requires { !r * !r <= !x < !h * !h }"
;;
let ensures_val = " ensures { !r < !m < !h }"
let convert_str_in_ens = [("result","(old !r)");("x","!r * !r <= !x < (!r + 1) * (!r + 1)");("result + 1","(old !h)")];;
let rec affiche_uses fd ls  = 
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
;;

let rec is_id_in_list (ls : string list) (elm : string) : bool = 
  match ls with 
  |[] -> false
  |h::t -> if h=elm then  true else is_id_in_list t elm
;;
(* Les parametre parametre et verif de string_of_expr sont là pour les raisons suivantes :
parametre c'est pour savoir si on doit ajouter le "!" pour la référence si la variable qu'on voit est un parametre
verif existe afin de ne pas générer des "!!" ou des "writes {!x}" car seulement laisser un test d'égalité sur le cas 
ASTId ferait que le "!" soit sur toutes les variables x ce qu'on ne veut pas *)
let rec string_of_expr  = function
  | ASTNum n -> "" ^ (string_of_int n) ^ ""
  | ASTId id -> "" ^ id ^ ""; 
  | Requires e -> " requires { " ^ string_of_expr e  ^ " }\n" 
  | Div (e1,e2) -> " div (" ^ string_of_expr e1 ^ ") " ^ string_of_expr e2
  | ASTBinOp (op, e1, e2) -> if e1==End_of_line || e1 == Empty || e2 ==End_of_line || e2 ==Empty then ""
    else if op = "=" then (string_of_expr e1 ) ^ " " ^ op ^"\n  " ^ (string_of_expr e2 ) else
      (string_of_expr e1 ) ^ " " ^ op ^" " ^ (string_of_expr e2 )
  | Ensures e -> " ensures { " ^ string_of_expr e  ^ " }\n" 
  | Writes e -> " writes { " ^ astWrite_to_string e ^ " }\n" 
  | Reads e -> " reads { " ^ astWrite_to_string e ^ " }\n" 
  | Comment _ -> ""
  | Let (id,e1,e2) -> "let " ^ id ^ " = " ^ string_of_expr e1 ^ " in \n" ^
                      string_of_expr e2 ^ "\n"	
  | Spec -> ""
  | Old e -> " old " ^ string_of_expr e 
  | Invariant e -> "  invariant {" ^ string_of_expr e ^ "}"
  | Variant e -> "  variant {" ^ string_of_expr e ^ "}"
  | Exclamation e -> "!"^string_of_expr  e 
  | Ref e -> "ref " ^ string_of_expr e
  | Into -> "-> "
  | If (cond,e,alt) -> (match alt with
          | Some e -> "if " ^ string_of_expr cond ^ " then " ^ string_of_expr e ^ "\n else " ^ string_of_expr e
          | None -> "if " ^ string_of_expr cond ^ " then " ^ string_of_expr e ^ "\n")
  | While (e1, e2) -> "while " ^ string_of_expr  e1 ^ " do\n" ^
                      String.concat "\n" (List.map (string_of_expr ) e2) ^ "\ndone\n"
  | Paran e -> "(" ^ string_of_expr  e  ^ ")"
  | Brace _ -> ""
  | End_of_line -> ""
  | Empty -> "  sqrt3_spec "^ !spec_arg ^";"
  | ForAll (_,_,_) -> ""
;;
let rec string_of_expr_pure = function 
  | ASTNum n -> "" ^ (string_of_int n) ^ ""
  | ASTId id -> "" ^ id ^ ""; 
  | Requires e -> " requires { " ^ string_of_expr_pure e  ^ " }\n" 
  | Div (e1,e2) -> " / " ^ string_of_expr_pure e1 ^ " / " ^ string_of_expr_pure e2
  | ASTBinOp (op, e1, e2) -> if e1==End_of_line || e1 == Empty || e2 ==End_of_line || e2 ==Empty then ""
    else (string_of_expr_pure e1 ) ^ " " ^ op ^" " ^ (string_of_expr_pure e2 )
  | Ensures e -> " ensures { " ^ string_of_expr_pure e  ^ " }\n" 
  | Writes e -> " writes { " ^ astWrite_to_string e ^ " }\n" 
  | Reads e -> " reads { " ^ astWrite_to_string e ^ " }\n" 
  | Comment _ -> ""
  | Let (id,e1,e2) -> "let " ^ id ^ " = " ^ string_of_expr_pure e1 ^ " in \n" ^
    string_of_expr_pure e2 ^ "\n"	
  | Spec -> ""
  | Old e -> " old " ^ string_of_expr_pure e 
  | Invariant e -> "  invariant {" ^ string_of_expr_pure e ^ "}"
  | Variant e -> "  variant {" ^ string_of_expr_pure e ^ "}"
  | Exclamation e -> "!"^string_of_expr_pure  e 
  | Ref _ -> ""
  | If (cond,e,alt) -> (match alt with
        | Some e -> "if " ^ string_of_expr_pure cond ^ " then " ^ string_of_expr_pure e ^ "\n else " ^ string_of_expr_pure e
        | None -> "if " ^ string_of_expr_pure cond ^ " then " ^ string_of_expr_pure e ^ "\n")
  | While (e1, e2) -> "while " ^ string_of_expr_pure  e1 ^ " do\n" ^
                      String.concat "\n" (List.map (string_of_expr_pure ) e2) ^ "\ndone\n"
  | Paran e -> "(" ^ string_of_expr_pure  e  ^ ")"
  | Brace _ -> ""
  | End_of_line -> ""
  | Empty -> ""
  | Into -> "->"
  | ForAll (_,_,_) -> ""
;;

(* construit la chaine de caractère des expressions de la liste avec string_of_expr *)
let rec ls_expr (ls: expr list)  =
  match ls with
  | [] -> ""
  | h :: t -> (*Printf.printf "ls_expr = %s \n" (string_of_expr h);*)
    let current_expr = string_of_expr h in current_expr  ^ " "^ls_expr t	
          
;;
(* construit la chaine de caractère de la liste de liste représentant ses expressions en faisant appel à ls_expr pour chaque liste *)
let rec main_body (lss: function_body list) : string =
  match lss with
  | [] -> ""
  | h :: t -> (ls_expr h ) ^ main_body t 
;;
(* renvoie la liste à partir de l'expression let*)
let rec find_expr_let (ls: expr list) : expr list = (*validé*)
  match ls with
  | [] -> []
  | h :: t -> (*Printf.printf "h = %s \n" (string_of_expr h);*)
    match h with
    | Let (id,value,e) -> (*Printf.printf "Let id = %s \n" id;*)
      [Let (id,value,e)] @ t
    | While(_,ex_ls) -> find_expr_let ex_ls
    | _ -> find_expr_let t  
;;

(*permet d'obtenir une chaine representant les reads writes du fichier .why partie fonction en ayant le paramètre de fonction et les déclarations let var in ...*)
let convert_write (first_param : ident) (param_let : ident list) : string = 
  let rec separe_param (l : ident list) : string =
    match l with 
    |[] -> ""
    |h::[] -> h
    |h::t -> h ^","^separe_param t
  in
  let res = separe_param param_let in
    (*Printf.printf "param_let: [%s]\n" (String.concat "; " param_let);*)
    " reads {"^first_param^","^res^"}\n writes {"^res^" }\n"
;;
let rec is_value_in_list (value : string) (ls : (string*string) list) : (bool*string) = 
  match ls with 
    |[] -> (false,"")
    |(h1,h2)::t -> 
        (*Printf.printf "value : %s ET h1 : %s avec h2 = %s \n" value h1 h2;*)
        if  value=h1 then (true,h2) else is_value_in_list value t 
;;
(* fonction qui va prendre la première partie séparer par le = du corps de la fonction dans le .rew pour la reproduire dans le .why*)
let rec convert_val_of_expr (a : expr list) (str_for_require : string) (param_func : ident) (spec_params : ident list) (inv_var_to_ens : expr list) : string = 
  let rec extract_ensures = function
    | Invariant (ASTBinOp ("/\\", e1, e2)) -> (extract_ensures (Invariant e1)) @ (extract_ensures (Invariant e2))
    | Invariant e -> ["ensures {" ^ expr_to_string e ]
    | _ -> []
  and expr_to_string = function
    | ASTNum n -> string_of_int n
    | ASTId id -> id
    | ASTBinOp (op, e1, e2) -> if op="/\\" then expr_to_string e1 ^"}\n "^ unconcat_list(extract_ensures (Invariant(e2))) else
         (expr_to_string e1) ^ " " ^ op ^ " " ^ (expr_to_string e2) 
    | Exclamation e -> "!" ^ (expr_to_string e)
    | Old e -> "old " ^ (expr_to_string e)
    | Invariant _ -> ""
    | Empty -> ""
    |_->""
  in
  let rec concat_ensures (cls : ident list) : ident = 
    match cls with
    |[] -> ""
    |h::[] -> h ^ "}"
    |h::t -> h ^"\n"^ (concat_ensures t)
  in
  let invariant_to_string (inv : expr) : string =
    let ensures_ls = extract_ensures inv in
    concat_ensures ensures_ls
  in
  let variant_to_string (var : expr) :string = 
    let value = string_of_expr_pure var in 
    "ensures { "^ value ^ " < old " ^ value ^ " }"
  in
  let rec parcours_expr (ls :expr list) : ident list = 
    match ls with 
    |[]-> []
    |h::t -> match h with 
            |Invariant e -> 
              [(invariant_to_string (Invariant(e)))^"\n"] @ parcours_expr t
            |Variant e -> [variant_to_string e] @ parcours_expr t
            |While(e1,e2) -> parcours_expr e2
            |_-> parcours_expr t
  in
  let rec encounter_ensures (ls : expr list) (conv_in_ens : expr list) : string =
    match ls with 
    |[] -> ""
    |h::t -> match h with 
              |Ensures(e) -> (match !first_ensures with 
                              |true -> first_ensures := false;
                                unconcat_list (parcours_expr conv_in_ens) ^ "\n" ^ (encounter_ensures t conv_in_ens)
                              |false -> (string_of_expr h ^ encounter_ensures t conv_in_ens))
              |_ -> encounter_ensures t conv_in_ens
  in   
  str_for_require^"\n"^(convert_write param_func spec_params) ^encounter_ensures a inv_var_to_ens
;;

let rec convert_spec_of_expr (a : expr list) (str_for_require : string) (reads_params : ident list) (writes_params : ident list): string = 
  (*Printf.printf "valeur de la list de parametre = %s |\n" (unconcat_list reads_params);*)
  " "^str_for_require^"\n"^" reads {"^(String.concat "," reads_params)^"}\n writes {"^ String.concat "," writes_params ^ "}\n"^ensures_val ^"\n"
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
| Div (e1,e2) -> is_spec e1 || is_spec e2
| ASTBinOp (_, e1, e2) -> is_spec e1 || is_spec e2 
| Ensures e -> is_spec e 
| Writes e -> false
| Reads e -> false
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
let rec is_div = function 
| ASTNum n -> false
| ASTId id -> false
| Requires e -> is_div e
| Div (e1,e2) -> true
| ASTBinOp (_, e1, e2) -> is_div e1 || is_div e2 
| Ensures e -> is_div e
| Writes e -> false
| Reads e -> false
| Comment _ -> false
| Let (_,e1,e2) -> is_div e1 || is_div e2 
| Spec -> false 
| Old e -> is_div e 
| Invariant e -> is_div e 
| Variant e -> is_div e 
| Exclamation e -> is_div e 
| Ref _ -> false 
| If (_, e1, e2) -> (match e2 with
    | Some e -> is_div e1 || is_div e
    | None -> is_div e1)
| While (_, ex_ls) -> List.exists is_div ex_ls
| Paran e -> is_div e  
| Brace _ -> false
| End_of_line -> false
| Empty -> false
| Into -> false
| ForAll (_,_,_) -> false
;;
(* determine si l'expression est empty ou contient empty*)
let rec is_empty (e:expr) : bool =
  match e with 
  |Empty -> true
  |ASTBinOp(_,e1,e2) -> is_empty e1 || is_empty e2 
  |Let(_,e1,e2) -> is_empty e1 || is_empty e2
  |If(_,e1,e2) -> (match e2 with 
    |Some e -> is_empty e1 || is_empty e
    |None -> is_empty e1)
  |Paran e -> is_empty e
  |Brace e -> is_empty e
  |Requires e -> is_empty e
  |Ensures e -> is_empty e
  |Invariant e -> is_empty e
  |Variant e -> is_empty e
  |_ -> false
;;
(*fonction qui va me servir à obtenir la liste d'expression qui suit la déclaration de spec dans le .rew*)
let rec ls_expr_afterSpec (ls: expr list) =
  match ls with
  | [] -> []
  | h :: t -> if is_spec h then t else ls_expr_afterSpec t
;; 
(*fonction qui va me construire la liste des d'expressions qu'il rencontre jusqu'à Div*)
let rec ls_expr_untilDiv (ls : expr list) =
  match ls with
  | [] -> []
  | h :: t -> if is_div h then [h] else h :: ls_expr_untilDiv t
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
(* sert à trouver la liste qui contient l'expression empty *)
let find_empty (lss : expr list list) : int = (* validé *) 
  let rec aux (ls : expr list ) : bool  = 
    match ls with 
    |[] -> false 
    |h :: t -> is_empty h || aux t
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


(* fonction qui permet d'insérer une liste d'expression à un index précis d'une liste de liste d'expression*)
(* n'a pas été utile pour le moment *)
let rec insert_listAt (lss : expr list list ) (ls : expr list ) (index : int) : expr list list =
  match lss with 
  |[]->if index = 0 then ls :: [] else [] 
  |h::t -> if index = 0 then ls :: (h :: t) else h :: (insert_listAt t ls (index-1) )
;;
let rec ls_expr_pure (ls: expr list) =
  match ls with
  | [] -> ""
  | h :: t -> string_of_expr_pure h ^ ls_expr_pure t 
;;
(* version de main_body qui va appeler la version de string_of_expr qui renvoie les paramètres tels qu'ils sont*)
let rec main_body_pure (lss: function_body list) : string =
  match lss with
  | [] -> ""
  | h :: t -> (ls_expr_pure h ) ^ main_body_pure t 
;;

(* permet d'obtenir les paramètres d'une val spec *)
let rec spec_param (lss : expr list list ) : ident list = (* validé *)(* ne pas oublier d'ajouter le paramètre de sqrt dans la liste resultat*)
  let rec aux = function
    | ASTNum n -> []
    | ASTId id -> []
    | Requires e -> aux e
    | Div (e1, e2) -> aux e1 @ aux e2
    | ASTBinOp (_, e1, e2) -> aux e1 @ aux e2 
    | Ensures e -> aux e 
    | Writes e -> []
    | Reads e -> []
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
let rec get_decl_let_in_list (ls : expr list) : string list = 
  let rec aux = function
    | ASTNum n -> []
    | ASTId id -> []
    | Requires e -> aux e
    | Div (e1, e2) -> aux e1 @ aux e2
    | ASTBinOp (_, e1, e2) -> aux e1 @ aux e2 
    | Ensures e -> aux e 
    | Writes e -> []
    | Reads e -> []
    | Comment _ -> []
    | Let (x,e1,e2) -> [x] @ aux e1 @ aux e2 
    | Spec -> []
    | Old e -> [] 
    | Invariant _ -> []
    | Variant _ -> []
    | Exclamation e -> [] 
    | Ref _ -> [] 
    | If (cond,e,alt) -> (match alt with
        | Some e -> aux cond @ aux e
        | None -> aux cond)
    | While (_,ex_ls) -> aux1 ex_ls 
    | Paran e -> []   
    | Brace _ -> []
    | End_of_line -> []
    | Empty -> []
    | Into -> []
    | ForAll (_,_,_) -> []
  and aux1 (ls : expr list ) : ident list = 
    match ls with 
    |[] -> []
    |h::t -> aux h @ aux1 t
  in  
  aux1 ls
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
(*comme son nom l'indique elle va prendre toutes les variables déclarer dans un let du fichier parser*)
let get_all_let_var (lss : expr list list) : string list = 
  let rec aux (ls : expr list ) : string list = 
    match ls with 
    |[] -> []
    |h::t -> match h with 
            |Let (id,value,e) -> [id] @ aux [e] @ aux t
            |ASTBinOp(_,e1,e2) -> aux [e1] @ aux [e2] @ aux t
            |While(_,ex_ls) -> aux ex_ls @ aux t
            |If(_,e1,e2) -> (match e2 with 
                            |Some e -> aux [e1] @ aux [e] @ aux t
                            |None -> aux [e1] @ aux t)
            |_ -> aux t
  in let rec aux1 (lss : expr list list ) : string list = 
    match lss with 
    |[] -> []
    |h::t -> aux h @ aux1 t
  in aux1 lss
;;
(* comme son nom l'indique cette fonction est là pour afficher un axiom*)
let rec affiche_axiom fd (ax :axiom option) =
  let rec axiom_expr_to_string (e : expr) : string = 
    match e with 
    |ASTId(id) -> id^" " 
    |ASTNum(nb) -> (string_of_int nb) ^ " "
    |ASTBinOp(op,e1,e2) -> (axiom_expr_to_string e1) ^ op ^ " "^(axiom_expr_to_string e2) 
    |Paran(e)-> "("^axiom_expr_to_string e^")"
    |Into -> "-> "
    |_-> ""
  in
  let rec axiom_body_to_list (ls : expr list) : string = 
    match ls with 
    |[] -> ""
    |h::t -> (axiom_expr_to_string h) ^ axiom_body_to_list t
  in 
  let affiche_body (e : expr) : string = 
    match e with 
      |ForAll(id_ls,name,ex_ls) -> (List.fold_left (fun acc id -> acc ^ id ^ " " ) " " id_ls ) ^ ": "^name^". " ^ axiom_body_to_list ex_ls
      |_ -> ""
  in 
  match ax with 
    |None -> ()
    |Some(x) -> Printf.fprintf fd "axiom %s : forall %s \n" x.name (affiche_body x.body)
;;
(*Permet d'obtenir une liste de tout les requires convertis en ensures à partir d'une liste d'expression*)
let rec requires_to_ensures (ls : expr list) (res : expr list) =
  match ls with 
  |[] -> res
  |h::t -> match h with 
          |Requires e ->  requires_to_ensures t (res @ [Ensures e])
          |_ -> requires_to_ensures t res
;;
(* fonction qui a pour but de me confirmer l'existence de div dans l'ast *)
let find_div (lss : expr list list) : int = (* validé *) 
  let rec aux (ls : expr list ) : bool  = 
    match ls with 
    |[] -> false 
    |h :: t -> is_div h || aux t
  in 
    let rec aux2 (lss : expr list list) (n : int) : int =
      match lss with 
      |[] -> -1 
      |h::t -> let value = aux h in if value then n else aux2 t (n+1) 
    in
      aux2 lss 0 
;;
let body_to_string (ls :expr list) : string =
  let start_let = find_expr_let ls in let mid_let = ls_expr_afterSpec start_let in
  let end_let = ls_expr_untilDiv mid_let in ls_expr end_let
  
let conv ast name : string = 
  let file = open_out_gen [Open_creat; Open_append; Open_text] 0o666 name in
  let ast_body = separe_list_expr (get_ls_from_lss ast.functions 0) [] in
  let sqrt_body = get_ls_from_lss ast_body ((List.length ast_body)-1) in 
  let div_exist =find_div ast_body in
  if div_exist != -1 then Printf.fprintf file "use int.ComputerDivision\n";
  affiche_uses file ast.uses ;
  Printf.fprintf file "\n";
  affiche_axiom file ast.axiomes;
  Printf.fprintf file "\n";
  let var_let = get_all_let_var ast_body in
  spec_arg := unconcat_list var_let;
  let fct_def = Printf.sprintf "let %s3 (%s : %s) : () \n" ast.func_name (!spec_arg) (astID_to_string (snd ast.parameter)) in
  let fct_body = body_to_string sqrt_body in 
  Printf.fprintf file "%s %s"  fct_def fct_body ;
  close_out file;
  eval ast 
