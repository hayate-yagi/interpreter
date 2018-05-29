type name = string


type binOp =
  | OpAdd
  | OpSub
  | OpMul
  | OpDiv
  | OpEq
  | OpLe
      
type expr =
  | Evalue of value
  | Evar   of name
  | Ebin   of binOp * expr * expr
  | Eif    of expr * expr * expr
  | ELet   of name * expr * expr
  | EFun   of name * expr
  | EApp   of expr * expr
  | ERLet  of name * name * expr * expr
  | ERALet of (name * name * expr) list * expr
  | EMatch of expr * pattern
  | ENil
  | ECons of expr * expr
  | EPair of expr * expr
      
and env = (name * value) list

and value =
  | VInt  of int
  | VBool of bool
  | VFun  of name * expr * env
  | VRFun of name * name * expr * env
  | VARFun of int * (name * name * expr) list * env
  | VList of value list
  | VTuple of value list

and pattern = pair list

and pair = pat * expr
  

and pat =
  | Name of name
  | Value of value
  | PTuple of pat list
  | PList of pat list
  | PWild

      
type command =
  | CExp of expr
  | CLet of name * expr
  | CRLet of name * name * expr
  | CRALet of (name * name * expr) list

type tyname = string  
      
type ty =
  | Int
  | Bool
  | Arrow of ty * ty
  | Var of tyname
  | Tuple of ty list
  | List of ty

type ty_subst = (tyname * ty) list

type ty_constraints = (ty * ty) list

type ty_env = (tyname * ty) list


exception Eval_error
exception Match_failure
exception NotFound of name

let rec print_value = function 
  | VInt i -> print_int i
  | VBool i -> print_string (string_of_bool i)
  | VFun(name,expr,env) -> print_string("<fun>")
  | VRFun(name,name', expr, env) -> print_string("<fun>")
  | VARFun(i,l,e) -> print_string("<fun>")
  | VTuple x ->
     print_string("(");
    let rec print_tuple x =
      match x with
      | [] -> print_string (")")
      | [y] ->
	print_value y; print_string (")")
      | y::rest ->
	 (match y with
	 | VInt i -> print_int i; print_string (",");  print_tuple rest
	 | VBool i -> print_string (string_of_bool i); print_string (","); print_tuple rest
	 | _ -> raise Eval_error ) in
    print_tuple x
  | VList x ->
     print_string("[");
    let rec print_list x =
      match x with
      | [] -> print_string ("]")
      | [y] ->
	print_value y; print_string ("]")
      | y::rest ->
	 print_value y; print_string (";"); print_list rest in
    print_list x
       
    

(*
 小さい式に対しては以下でも問題はないが，
 大きいサイズの式を見やすく表示したければ，Formatモジュール
   http://caml.inria.fr/pub/docs/manual-ocaml/libref/Format.html
 を活用すること
*)


let find_match : pat -> value -> env = fun p v ->
  let rec find_match' p v res =
    match p with
    | Value x ->
       (match (x,v) with
       | (VInt i1, VInt i2) when i1=i2 -> res
       | (VBool b1, VBool b2) when b1=b2 -> res
       | _ -> raise Match_failure )
    | Name x -> ((x,v)::res)
    | PTuple l ->
       (match (l,v) with
       | ([], VTuple []) -> res
       | (p'::ps, VTuple (v'::vs)) -> find_match' (PTuple ps) (VTuple vs) ((find_match' p' v' []) @ res)
       | _ -> raise Match_failure)
    | PList l ->
       (match (l,v) with
       | ([], VList []) -> res
       | ([p'],v') -> find_match' p' v' res
       | (p'::ps, VList (v'::vs)) -> find_match' (PList ps) (VList vs) ((find_match' p' v' []) @ res)
       | _ -> raise Match_failure)
    | PWild -> res in
  find_match' p v []

let rec branch_match : pattern -> value -> (env * expr) = fun l v ->
  match l with
  | [] -> failwith "No matching!"
  | (p,e)::rest ->
     try (find_match p v, e)
     with Match_failure -> branch_match rest v
       

    
let rec eval : env -> expr -> value = fun env e ->
  match e with
    Evalue v -> v
  | Evar v ->
     begin
       try List.assoc v env
       with Not_found -> raise (NotFound v)
     end
  | Eif (e1,e2,e3) -> (match eval env e1 with
    | VBool true -> eval env e2
    | VBool false -> eval env e3
    | _ -> raise Eval_error )
  | Ebin (op,e1,e2) ->
     (match (eval env e1, eval env e2) with
     | (VInt x,VInt y) -> (match op with
       | OpAdd -> VInt(x+y)
       | OpSub -> VInt(x-y)
       | OpMul -> VInt(x*y)
       | OpDiv -> VInt(x/y)
       | OpEq  -> VBool(x=y)
       | OpLe  -> VBool(x<y))
     | (VBool x, VBool y) -> (match op with
       | OpEq -> VBool(x=y)
       | OpLe -> VBool(x<y)
       | _    -> raise Eval_error)
     | (_,_) -> raise Eval_error)    
  | ELet (name,e1,e2) -> eval ((name,eval env e1)::env) e2
  | EFun (name,e) -> VFun(name,e,env)
  | EApp (e1,e2) -> (match eval env e1 with
    | VFun(name,e3,env') -> eval ((name,eval env e2)::env') e3
    | VRFun(f,x,e3,env') ->
       let env2 = (x,eval env e2) :: (f, VRFun(f, x, e3, env')) :: env' in
       eval env2 e3
    | VARFun(n,l,oenv)  ->
       let (_,x,e) = List.nth l (n-1) in
       let rec loop n = function
	 | [] -> []
         | (f',x',e')::rest ->
            (f',VARFun(n,l,oenv))::(loop (n+1) rest) in
       let env' = (x,(eval env e2))::((loop 1 l)@oenv) in
       eval env' e
    | _ -> raise Eval_error)
  | ERLet (f, x, e1, e2) ->
     let env' = (f, VRFun (f, x, e1, env))::env in
     eval env' e2
  | ERALet (l,e) ->
     let rec eralet env l =
       match l with
       | [] -> env
       | (f,x,e')::rest -> eralet ((f,VRFun(f,x,e',env))::env) rest in
     eval (eralet env l) e
  | EMatch (e,l) ->
     let v = eval env e in
     let (env', exp) = branch_match l v in
     eval (env' @ env) exp
  | ENil -> VList []
  | ECons (e1,e2) ->
     let v = eval env e2 in
     (match v with
     | VList l -> VList ((eval env e1)::l)
     | _ ->failwith "Error(cons)")
  |EPair (e1,e2) -> VTuple [eval env e1; eval env e2]
     
	  
     
     
     

let command : env -> command -> env * value = fun env c ->
  match c with
  | CExp e -> (env, eval env e)
  | CLet (name,e) ->
     let e' = eval env e in
     ((name,e')::env, e')
  | CRLet (f, x, e) ->
     ((f, VRFun(f, x, e, env))::env, VRFun(f,x,e,env))
  (* | CRALet list -> *)
  (*    let rec cralet env l = *)
  (*      match l with *)
  (*      | [] -> (env, VRFun("a","b",ENil,env)) *)
  (*      | (f,x,e)::rest -> cralet ((f,VRFun(f,x,e,env))::env) rest in *)
  (*    cralet env list *)
  | CRALet l      ->
     let rec loop i = function
       | [] -> ([],[])
       | (f,_,_)::rest -> let v = VARFun(i,l,env) in
			  let (env', names) = loop (i+1) rest in
			  ((f, v)::env', f::names) in
     let (env', names) = loop 1 l in
     (env'@env, VRFun("a","b",ENil,env))


(* let rec apply_ty_subst : ty_subst -> ty -> ty = fun s t -> *)
(*   match t with *)
(*   | Int -> Int *)
(*   | Bool -> Bool *)
(*   | Imp (t1,t2) -> Imp ((apply_ty_subst s t1),(apply_ty_subst s t2)) *)
(*   | Var n -> *)
(*      try List.assoc n s *)
(*      with Not_found -> Var n *)

(* let compose_ty_subst : ty_subst -> ty_subst -> ty_subst = fun s1 s2 -> *)
(*   (List.map (fun (n,t) -> (n, (apply_ty_subst s1 t))) s2) @ (List.filter (fun (v,_) -> not (List.mem_assoc v s2)) s1) *)
       
(* (\* let compose_ty_subst : ty_subst -> ty_subst -> ty_subst = fun s1 s2 -> *\) *)
(* (\*   let rec compose s1 s2 ans = *\) *)
(* (\*     match s2 with *\) *)
(* (\*     | [] -> *\) *)
(* (\*        (match s1 with *\) *)
(* (\*        | [] -> ans *\) *)
(* (\*        | (n,t)::rest -> *\) *)
(* (\* 	  if List.mem_assoc n ans *\) *)
(* (\* 	  then compose rest [] ans *\) *)
(* (\* 	  else compose rest [] ((n,t)::ans)) *\) *)
(* (\*     | (n,t)::rest -> compose s1 rest ((n,(apply_ty_subst s1 t))::ans) in *\) *)
(* (\*   compose s1 s2 [] *\) *)

(* let ty_sub : ty_constraints -> tyname -> ty -> ty_constraints = fun c n t -> *)
(*   List.map (fun (x,y) -> if y = (Var n) then (x,t) else (x,y)) c *)

(* let rec ty_unify : ty_constraints -> ty_subst = fun c -> *)
(*   match c with *)
(*   | [] -> [] *)
(*   | (x,y)::rest when x=y -> ty_unify rest *)
(*   | (Imp(s,t),Imp(s',t'))::rest -> ty_unify ((s,s')::(t,t')::rest) *)
(*   | (Var n, t)::rest -> compose_ty_subst (ty_unify (ty_sub rest n t)) [(n,t)] *)
(*   | (t, Var n)::rest -> compose_ty_subst (ty_unify (ty_sub rest n t)) [(n,t)] *)
(*   | _ -> failwith "Error(ty_unify)" *)
       
       
(* let gather_ty_constraints : ty_subst -> expr -> ty * ty_constraints = fun s e -> *)
(*   match e with *)
(*   | Evalue v -> *)
(*      (match v with *)
(*      | VInt -> Int *)
(*      | VBool -> Bool *)

    

	


 
