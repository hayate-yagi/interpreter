open Syntax

let rec print_type = function
  | Int -> print_string ("int")
  | Bool -> print_string ("bool")
  | Arrow (t1,t2) ->
     (match (t1,t2) with
     | (Arrow(_,_),Arrow(_,_)) ->
	print_char ('('); print_type t1; print_char (')'); print_string ("->"); print_char ('('); print_type t2; print_char (')')
     | (Arrow(_,_),_) ->
	print_char ('('); print_type t1; print_char (')'); print_string ("->"); print_type t2
     | (_,Arrow(_,_)) ->
	print_type t1; print_string ("->"); print_char ('('); print_type t2; print_char (')')
     | (_,_) ->
	print_type t1; print_string ("->"); print_type t2)
  | Var n -> print_string n;;

let rec apply_ty_subst : ty_subst -> ty -> ty = fun s t ->
  match t with
  | Int -> Int
  | Bool -> Bool
  | Arrow (t1,t2) -> Arrow ((apply_ty_subst s t1),(apply_ty_subst s t2))
  | Var n ->
     try List.assoc n s
     with Not_found -> Var n;;

let compose_ty_subst : ty_subst -> ty_subst -> ty_subst = fun s1 s2 ->
  (List.map (fun (n,t) -> (n, (apply_ty_subst s1 t))) s2)
  @ (List.filter (fun (v,_) -> not (List.mem_assoc v s2)) s1);;
       
(* let compose_ty_subst : ty_subst -> ty_subst -> ty_subst = fun s1 s2 -> *)
(*   let rec compose s1 s2 ans = *)
(*     match s2 with *)
(*     | [] -> *)
(*        (match s1 with *)
(*        | [] -> ans *)
(*        | (n,t)::rest -> *)
(* 	  if List.mem_assoc n ans *)
(* 	  then compose rest [] ans *)
(* 	  else compose rest [] ((n,t)::ans)) *)
(*     | (n,t)::rest -> compose s1 rest ((n,(apply_ty_subst s1 t))::ans) in *)
(*   compose s1 s2 [] *)

(* compose_ty_subst [("a",Bool);("b",Int)] [("b",Var "a")];; *)

let rec search_ty_var : ty -> ty -> bool = fun t1 t2 ->
  match t2 with
  | Int
  | Bool -> false
  | Arrow (t1',t2') -> (search_ty_var t1 t1')||(search_ty_var t1 t2')
  | Var t as s -> if t1 = s then true else false

let ty_sub : ty_constraints -> tyname -> ty -> ty_constraints = fun c n t ->
  List.map (fun (x,y) ->(apply_ty_subst [(n,t)] x,apply_ty_subst [(n,t)] y)) c;;

(* occurence check *)

let rec ty_unify : ty_constraints -> ty_subst = fun c ->
  match c with
  | [] -> []
  | (x,y)::rest when x=y -> ty_unify rest
  | (Arrow(s,t),Arrow(s',t'))::rest -> ty_unify ((s,s')::(t,t')::rest)
  | (Var n, t)::rest
  | (t, Var n)::rest ->
     begin
       match search_ty_var (Var n) t with
       | true  -> failwith "occurence error"
       | false -> compose_ty_subst (ty_unify (ty_sub rest n t)) [(n,t)]
     end
  | _ -> failwith "Error(ty_unify)";;



let ty_var = ref 96;;
let new_ty_var : unit -> tyname = fun () ->
  ty_var := !ty_var + 1;
  Char.escaped (Char.chr (!ty_var));;

(* new_ty_var ();; *)

let gather_ty_constraints_pattern : pat -> ty * ty_env * ty_constraints = fun p ->
  match p with
  | Name v ->
     let t = new_ty_var () in
     (Var t, [(v,Var t)], [])
  | Value v ->
     begin
       match v with
       | VInt i-> (Int,[],[])
       | VBool i-> (Bool,[],[])
       | _ -> failwith "Error(gather1')"
     end
  | _ -> failwith "pattern_error";;

let remove_some : ty option -> ty = fun t ->
  match t with
  | None -> failwith "option_error"
  | Some x -> x ;;
     
let rec gather_ty_constraints : ty_env -> expr -> ty * ty_constraints = fun env e ->
  match e with
  | Evalue v ->
     (match v with
     | VInt i-> (Int,[])
     | VBool i-> (Bool,[])
     | _ -> failwith "Error(gather1)")
  | Evar n ->
     (try (List.assoc n env,[])
      with Not_found -> raise (NotFound n))
  | Ebin (b,e1,e2) ->
     let (t1,c1) = gather_ty_constraints env e1 in
     let (t2,c2) = gather_ty_constraints env e2 in
     (match b with
     | OpAdd 
     | OpSub 
     | OpMul 
     | OpDiv -> (Int, (t1,Int)::(t1,t2)::c1@c2)
     | OpEq  -> (Bool, (t1,Int)::(t1,t2)::c1@c2)
     | OpLe  -> (Bool, (t1,Int)::(t1,t2)::c1@c2))
  | ELet (n,e1,e2) ->
     let (t1,c1) = gather_ty_constraints env e1 in
     let (t2,c2) = gather_ty_constraints ((n,t1)::env) e2 in
     (t2,c1@c2)
  | Eif (e1,e2,e3) ->
     let (t1,c1) = gather_ty_constraints env e1 in
     let (t2,c2) = gather_ty_constraints env e2 in
     let (t3,c3) = gather_ty_constraints env e3 in
     (t2,(t1,Bool)::(t2,t3)::c1@c2@c3)
  | EFun (n,e) ->
     let t = new_ty_var () in
     let (t',c) = gather_ty_constraints ((n,Var t)::env) e in
     (Arrow (Var t,t'), c)
  | EApp (e1,e2) ->
     let (t1,c1) = gather_ty_constraints env e1 in
     let (t2,c2) = gather_ty_constraints env e2 in
     let t' = new_ty_var () in
     (Var t', (t1,Arrow(t2,Var t'))::c1@c2)
  | ERLet (f,x,e1,e2) ->
     let a = new_ty_var () in
     let b = new_ty_var () in
     let env' = (f,Arrow(Var a,Var b))::env in
     let (t1,c1) = gather_ty_constraints ((x,Var a)::env') e1 in
     let (t2,c2) = gather_ty_constraints env' e2 in
     (t2,(t1,Var b)::c1@c2)
  | EMatch (e,p) ->
     let (t0,c0) = gather_ty_constraints env e in
     let rec f : pattern -> ty -> ty option -> ty_constraints -> (ty option * ty_constraints) =
       fun p_list t t' c_ans ->
	 match p_list with
	 | [] -> (t',c_ans)
	 | (pat,ex)::rest ->
	    let (t1,env',c1) = gather_ty_constraints_pattern pat in
	    let (t1',c1') = gather_ty_constraints (env@env') ex in
	    begin
	      match t' with
	      | None -> f rest t1 (Some t1') ((t,t1)::c1@c1'@c_ans)
	      | Some t0' -> f rest t1 (Some t1') ((t,t1)::(t0',t1')::c1@c1'@c_ans)
	    end in
     let (t'',c'') = f p t0 None c0 in
     (remove_some t'', c'')
  | _ -> failwith "Error(gather3)";;
     
(* gather_ty_constraints [] (Ebin(OpAdd,Evalue (VInt 1),Evalue (VBool true)));; *)
(* gather_ty_constraints [] (EFun("x",Ebin(OpAdd,Evalue (VInt 1),Evalue (VInt 3))));; *)
(* gather_ty_constraints [] (EFun("x",Ebin(OpAdd,Evar "x",Evalue (VInt 3))));; *)
(* gather_ty_constraints [("x",Bool)] (EApp (EFun("x",Ebin(OpAdd,Evar "x",Evalue (VInt 3))),Evalue (VInt 1)));; *)
(* let (a,b) = gather_ty_constraints [] (ERLet ("f","x",Eif(Ebin(OpEq,Evar "x",Evalue (VInt 0)),Evalue (VInt 1),Ebin(OpMul,Evar "x",EApp(Evar "f",Ebin(OpSub,Evar "x",Evalue (VInt 1))))),EApp (Evar "f", Evalue (VInt 3))));; *)


let infer_expr : ty_env -> expr -> ty = fun env expr ->
  let (t,c) = gather_ty_constraints env expr in
  let s = ty_unify c in
  apply_ty_subst s t;;

(* infer_expr [] (ERLet ("f","x",Eif(Ebin(OpEq,Evar "x",Evalue (VInt 0)),Evalue (VInt 1),Ebin(OpMul,Evar "x",EApp(Evar "f",Ebin(OpSub,Evar "x",Evalue (VInt 1))))),EApp (Evar "f", Evalue (VInt 3))));; *)

let infer_cmd : ty_env -> command -> ty * ty_env = fun env c ->
  (* let ty_var = ref 96 in *)
  match c with
  | CExp e ->
     let t = infer_expr env e in
     (t,env)
  | CLet (n,e) ->
     let t = infer_expr env e in
     (t,(n,t)::env)
  | CRLet (f,x,e) ->
     let t1 = new_ty_var () in
     let t2 = new_ty_var () in
     let (t',c) =  gather_ty_constraints ((f,Arrow(Var t2,Var t1))::(x,Var t2)::env) e in
     let u = ty_unify c in
     let t' = apply_ty_subst u (Arrow(Var t2,Var t1)) in
     (t',(f,t')::env)
  | _ -> failwith "Error(infer)";;

(* infer_cmd  [] (CExp (ERLet ("f","x",Eif(Ebin(OpEq,Evar "x",Evalue (VInt 0)),Evalue (VInt 1),Ebin(OpMul,Evar "x",EApp(Evar "f",Ebin(OpSub,Evar "x",Evalue (VInt 1))))),EApp (Evar "f", Evalue (VInt 3)))));; *)

(* infer_cmd [] (CLet ("x",Evalue(VInt 1)));; *)

(* infer_cmd [] (CRLet ("f","x",Eif(Ebin(OpEq,Evar "x",Evalue (VInt 0)),Evalue (VInt 1),Ebin(OpMul,Evar "x",EApp(Evar "f",Ebin(OpSub,Evar "x",Evalue (VInt 1)))))));; *)

(* let (t1,t2)=gather_ty_constraints [("f",Var "a");("x",Var "b")] (Eif(Ebin(OpEq,Evar "x",Evalue (VInt 0)),Evalue (VInt 1),Ebin(OpMul,Evar "x",EApp(Evar "f",Ebin(OpSub,Evar "x",Evalue (VInt 1))))));; *)

(* ty_unify t2;; *)

(* infer_expr [("f",Arrow(Int,Int))] (EApp (Evar "f", Evalue (VInt 5)));;  *)
