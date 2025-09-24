open Ast 
open Eval 
(* Fichier pour convertir l'ast produite en un fichier .why *) 

let empty_seen = ref false ;; (* variable qui me sert à savoir si l'objet <> à déjà été vu à la fin du fichier*) (*pas utilisé*)
let requires_val = "requires { 0 <= !r }
  requires { !r + 1 < !h }
  requires { !r * !r <= !x < !h * !h }";;
let requires_body = " requires { !x >= 0 }
 requires { !r >= 0 }
 requires { !r+1 <= !h }
 requires { !r * !r <= !x < !h * !h }"
;;
let ensures_val = " ensures { !x = old !x }"
let convert_str_in_ens = [("result","(old !r)");("x","!r * !r <= !x < (!r + 1) * (!r + 1)");("result + 1","(old !h)")];;
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
| ASTBinOp (op, e1, e2) -> if e1==End_of_line || e1 == Empty || e2 ==End_of_line || e2 ==Empty then ""
  else (string_of_expr e1 ) ^ " " ^ op ^" " ^ (string_of_expr e2 )
| Ensures e -> " ensures { " ^ string_of_expr e  ^ " }\n" 
| Writes e -> " writes { " ^ astWrite_to_string e ^ " }\n" 
| Comment _ -> ""
| Let (_,_,_) -> ""
| Spec -> ""
| Old e -> " old " ^ string_of_expr e 
| Invariant e -> "  invariant {" ^ string_of_expr e ^ "}"
| Variant e -> "  variant {" ^ string_of_expr e ^ "}"
| Exclamation e -> "!"^string_of_expr  e 
| Ref _ -> ""
| If (_, _, _) -> ""
| While (e1, e2) -> "while " ^ string_of_expr  e1 ^ " do\n" ^
                    String.concat "\n" (List.map (string_of_expr ) e2) ^ "\ndone\n"
| Paran e -> "(" ^ string_of_expr  e  ^ ")"
| Brace _ -> ""
| End_of_line -> ""
| Empty -> "  sqrt2_spec x r h"
| Into -> ""
| ForAll (_,_,_) -> ""
;;
let rec string_of_expr_pure = function 
  | ASTNum n -> "" ^ (string_of_int n) ^ ""
  | ASTId id -> "" ^ id ^ ""; 
  | Requires e -> " requires { " ^ string_of_expr_pure e  ^ " }\n" 
  | ASTBinOp (op, e1, e2) -> if e1==End_of_line || e1 == Empty || e2 ==End_of_line || e2 ==Empty then ""
    else (string_of_expr_pure e1 ) ^ " " ^ op ^" " ^ (string_of_expr_pure e2 )
  | Ensures e -> " ensures { " ^ string_of_expr_pure e  ^ " }\n" 
  | Writes e -> " writes { " ^ astWrite_to_string e ^ " }\n" 
  | Comment _ -> ""
  | Let (_,_,_) -> ""
  | Spec -> ""
  | Old e -> " old " ^ string_of_expr_pure e 
  | Invariant e -> "  invariant {" ^ string_of_expr_pure e ^ "}"
  | Variant e -> "  variant {" ^ string_of_expr_pure e ^ "}"
  | Exclamation e -> "!"^string_of_expr_pure  e 
  | Ref _ -> ""
  | If (_, _, _) -> ""
  | While (e1, e2) -> "while " ^ string_of_expr_pure  e1 ^ " do\n" ^
                      String.concat "\n" (List.map (string_of_expr_pure ) e2) ^ "\ndone\n"
  | Paran e -> "(" ^ string_of_expr_pure  e  ^ ")"
  | Brace _ -> ""
  | End_of_line -> ""
  | Empty -> ""
  | Into -> ""
  | ForAll (_,_,_) -> ""
;;
(* *)
let rec stop_spec_expr_string (parametre : ident) (verif : bool) = function 
  | ASTNum n -> "" ^ (string_of_int n) ^ ""
  | ASTId id -> if id=parametre && verif=true then "!" ^ id ^ "" else "" ^ id ^ ""  
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

(**)
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
let rec convert_val_of_expr (a : expr list) (str_for_require : string) (param_func : ident) (spec_param : ident list) ( str_for_ensure : (string*string) list) : string = 
  let rec ensures_expr_string (ls_conv : (string *string) list ) = function 
  | ASTNum n -> "" ^ (string_of_int n) ^ "" 
  | ASTId id -> (*Printf.printf "ASTId = %s \n" id;*)
    let res = is_value_in_list id ls_conv in if (fst res) then snd res else id
  | Requires e -> ""
  | ASTBinOp (op, e1, e2) -> let id = (ensures_expr_string ls_conv e1 ^ op ^ " "^ensures_expr_string ls_conv e2) in let res = is_value_in_list id ls_conv in
    (*Printf.printf "ASTBinop : id = %s ET res = ( %b , %s )\n" id (fst res) (snd res) ;*)
    if (fst res) then snd res else id
  | Ensures _ -> ""
  | Writes _ -> "" 
  | Comment _ -> ""
  | Let (id,value,e) -> " "
  | Spec -> ""
  | Old e -> ""
  | Invariant _ -> ""
  | Variant _ -> ""
  | Exclamation e -> " !" ^ string_of_expr_pure e 
  | Ref e -> "ref "
  | If (_, _, _) -> ""
  | While (_, _) -> ""
  | Paran e -> let id = (string_of_expr_pure e ) in let res = is_value_in_list id ls_conv in
    Printf.printf "Paran : id = %s ET res = ( %b , %s )\n" id (fst res) (snd res) ;
    if (fst res) then snd res else id
  | Brace _ -> ""
  | End_of_line -> ""
  | Empty -> ""
  | Into -> ""
  | ForAll(_,_,_)->""
  in
  let convert_ensures (e : expr) ( ls_conv : (string*string) list) : string = 
    match e with 
      |Ensures h ->let res = (ensures_expr_string ls_conv h) in 
      (*Printf.printf "Ensures = %s \n" res;*)
      " ensures { "^res ^ " }\n"
      |_ -> ""
  in 
  let rec convert_list_ensures (ls : expr list) ( ls_conv : (string*string) list) : string = 
    match ls with 
      |[]->""
      |h::t-> (convert_ensures h ls_conv) ^ (convert_list_ensures t ls_conv)
  in
  str_for_require^"\n"^(convert_write param_func spec_param) ^ convert_list_ensures a str_for_ensure
;;

let rec convert_spec_of_expr (a : expr list) (str_for_require : string) (param_func : ident) (spec_param : ident list)  : string = 
  let rec extract_ensures = function
    | Invariant (ASTBinOp ("/\\", e1, e2)) ->
        (extract_ensures (Invariant e1)) @ (extract_ensures (Invariant e2))
    | Invariant e ->
        ["ensures {" ^ expr_to_string e ]
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
            |Invariant e -> let inv1 = invariant_to_string (Invariant(e)) in 
              Printf.printf " Invariant = %s \n" inv1 ;
              [(invariant_to_string (Invariant(e)))^"\n"] @ parcours_expr t
            |Variant e -> [variant_to_string e] @ parcours_expr t
            |While(e1,e2) -> parcours_expr e2
            |_-> parcours_expr t
  
  in let is_working = (unconcat_list (parcours_expr a)) in Printf.printf " Work = %s \n" is_working ;
  str_for_require^"\n"^(convert_write param_func spec_param) ^ (unconcat_list (parcours_expr a)) ^ "\n "^ensures_val ^"\n"
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
let rec ls_expr (ls: expr list)  =
  match ls with
  | [] -> ""
  | h :: [] -> ""
  | h :: t -> let current_expr = string_of_expr h in 
          Printf.printf " valeur de empty_seen = %b \n" !empty_seen ;
          if !empty_seen = true then Printf.printf " valeur du last = %s\n" (string_of_expr h);
          if !empty_seen = false then current_expr ^ ls_expr t else ""
;;
(* construit la chaine de caractère de la liste de liste représentant ses expressions en faisant appel à ls_expr pour chaque liste *)
let rec main_body (lss: function_body list) : string =
  match lss with
  | [] -> ""
  | h :: t -> (ls_expr h ) ^ main_body t 
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

let body_to_string (lss : expr list list) (param_func : ident) (spec_param : ident list): string = 
  let p1 = get_ls_from_lss lss  0 in let p3 = get_ls_from_lss lss 2 in 
  let body1 = convert_val_of_expr p1 requires_body param_func spec_param convert_str_in_ens in 
  body1 ^ "=\n " ^ ls_expr p3  
  
let conv ast name : string = 
  let file = open_out_gen [Open_creat; Open_append; Open_text] 0o666 name in
  affiche_uses file ast.uses;
  affiche_axiom file ast.axiomes;
  let ast_body = separe_list_expr (get_ls_from_lss ast.functions 0) [] in 
  let fct_def = Printf.sprintf "let %s (%s : %s) : () \n" ast.func_name ((fst ast.parameter) ^ " "^ (unconcat_list (spec_param ast_body)) ) (astID_to_string (snd ast.parameter)) in
  let index_spec = find_spec ast_body in 
  let fct_body = body_to_string ast_body (fst ast.parameter) (spec_param ast_body) in 
  let val_spec = Printf.sprintf "\nval %s2_spec (%s : %s) : () \n" ast.func_name ((fst ast.parameter) ^ " " ^(unconcat_list (spec_param ast_body)))  (astID_to_string (snd ast.parameter)) in 
  let spec_body = convert_spec_of_expr (get_ls_from_lss ast_body (index_spec+1)) requires_val (fst ast.parameter) (spec_param ast_body) in 
  Printf.fprintf file "%s%s \n%s%s" val_spec spec_body fct_def fct_body ;
  close_out file;
  eval ast 
