include Utils

let rec subst_type (s : ty Env.t) (ty : ty) : ty =
  match ty with
  | TUnit | TInt | TFloat | TBool -> ty
  | TVar x -> (match Env.find_opt x s with Some t -> t | None -> TVar x)
  | TList t -> TList (subst_type s t)
  | TOption t -> TOption (subst_type s t)
  | TPair (t1, t2) -> TPair (subst_type s t1, subst_type s t2)
  | TFun (t1, t2) -> TFun (subst_type s t1, subst_type s t2)

let subst_constrs (s : ty Env.t) (cs : constr list) : constr list =
  List.map (fun (t1, t2) -> (subst_type s t1, subst_type s t2)) cs

let unify (cs : constr list) : ty Env.t option =
  let rec occurs x t =
    match t with
    | TVar y -> x = y
    | TList t | TOption t -> occurs x t
    | TPair (t1, t2) | TFun (t1, t2) -> occurs x t1 || occurs x t2
    | _ -> false
  in
  let rec go (s : ty Env.t) (cs : constr list) : ty Env.t option =
    match cs with
    | [] -> Some s
    | (t1, t2) :: rest ->
        let t1 = subst_type s t1 in
        let t2 = subst_type s t2 in
        match t1, t2 with
        | _ when t1 = t2 -> go s rest
        | TVar x, _ when not (occurs x t2) ->
            let s' = Env.add x t2 (Env.map (subst_type (Env.singleton x t2)) s) in
            go s' (subst_constrs (Env.singleton x t2) rest)
        | _, TVar x when not (occurs x t1) ->
            let s' = Env.add x t1 (Env.map (subst_type (Env.singleton x t1)) s) in
            go s' (subst_constrs (Env.singleton x t1) rest)
        | TList t1, TList t2
        | TOption t1, TOption t2 ->
            go s ((t1, t2) :: rest)
        | TPair (a1, b1), TPair (a2, b2)
        | TFun (a1, b1), TFun (a2, b2) ->
            go s ((a1, a2) :: (b1, b2) :: rest)
        | _ -> None
  in go Env.empty cs

let rec free_type_vars (ty : ty) : VarSet.t =
  match ty with
  | TUnit | TInt | TFloat | TBool -> VarSet.empty
  | TVar x -> VarSet.singleton x
  | TList t | TOption t -> free_type_vars t
  | TPair (t1, t2) | TFun (t1, t2) ->
      VarSet.union (free_type_vars t1) (free_type_vars t2)

let principle_type (ty : ty) (cs : constr list) : ty_scheme option =
  match unify cs with
  | None -> None
  | Some subst ->
      let ty' = subst_type subst ty in
      let vars = free_type_vars ty' in
      Some (Forall (vars, ty'))

let rec infer (env : stc_env) (e : expr) : ty * constr list =
  match e with
  | Unit -> (TUnit, [])
  | Bool _ -> (TBool, [])
  | Int _ -> (TInt, [])
  | Float _ -> (TFloat, [])
  | Nil ->
      let a = TVar (gensym ()) in
      (TList a, [])

  | ENone ->
      let a = TVar (gensym ()) in
      (TOption a, [])

  | Var x ->
      (match Env.find_opt x env with
       | Some (Forall (vars, t)) ->
           let subst =
             List.fold_left
               (fun acc v -> Env.add v (TVar (gensym ())) acc)
               Env.empty (VarSet.elements vars)
           in
           let rec apply s ty =
             match ty with
             | TUnit | TInt | TFloat | TBool -> ty
             | TVar v -> (match Env.find_opt v s with Some t -> t | None -> ty)
             | TList t -> TList (apply s t)
             | TOption t -> TOption (apply s t)
             | TPair (t1, t2) -> TPair (apply s t1, apply s t2)
             | TFun (t1, t2) -> TFun (apply s t1, apply s t2)
           in
           (apply subst t, [])
       | None -> failwith ("unbound variable: " ^ x))

  | Assert e ->
      let t, c = infer env e in
      (TUnit, (t, TBool) :: c)

  | ESome e ->
      let t, c = infer env e in
      (TOption t, c)

  | Bop (op, e1, e2) ->
      let t1, c1 = infer env e1 in
      let t2, c2 = infer env e2 in
      let constraints, result_ty =
        match op with
        | Add | Sub | Mul | Div | Mod ->
            [(t1, TInt); (t2, TInt)], TInt
        | AddF | SubF | MulF | DivF | PowF ->
            [(t1, TFloat); (t2, TFloat)], TFloat
        | Lt | Lte | Gt | Gte | Eq | Neq ->
            [(t1, t2)], TBool
        | And | Or ->
            [(t1, TBool); (t2, TBool)], TBool
        | Comma ->
            [], TPair (t1, t2)
        | Cons ->
            [(t2, TList t1)], TList t1
      in
      (result_ty, c1 @ c2 @ constraints)

  | If (e1, e2, e3) ->
      let t1, c1 = infer env e1 in
      let t2, c2 = infer env e2 in
      let t3, c3 = infer env e3 in
      (t3, (t1, TBool) :: (t2, t3) :: (c1 @ c2 @ c3))

  | Fun (x, annot, body) ->
      let arg_ty = match annot with
        | Some t -> t
        | None -> TVar (gensym ())
      in
      let env' = Env.add x (Forall (VarSet.empty, arg_ty)) env in
      let body_ty, c = infer env' body in
      (TFun (arg_ty, body_ty), c)

  | App (e1, e2) ->
      let t1, c1 = infer env e1 in
      let t2, c2 = infer env e2 in
      let res_ty = TVar (gensym ()) in
      (res_ty, (t1, TFun (t2, res_ty)) :: (c1 @ c2))

  | Annot (e, t_annot) ->
      let t_expr, c = infer env e in
      (t_annot, (t_expr, t_annot) :: c)

  | Let { is_rec = false; name; binding; body } ->
      let t1, c1 = infer env binding in
      let t_scheme_opt =
        match principle_type t1 c1 with
        | Some s -> s
        | None -> failwith "let binding not typable"
      in
      let env' = Env.add name t_scheme_opt env in
      infer env' body

  | Let { is_rec = true; name; binding = Fun (x, annot, body_fn); body } ->
      let arg_ty = match annot with
        | Some t -> t
        | None -> TVar (gensym ())
      in
      let ret_ty = TVar (gensym ()) in
      let fun_ty = TFun (arg_ty, ret_ty) in
      let scheme = Forall (VarSet.empty, fun_ty) in
      let env' = Env.add name scheme (Env.add x (Forall (VarSet.empty, arg_ty)) env) in
      let body_ty, c1 = infer env' body_fn in
      let c_all = (ret_ty, body_ty) :: c1 in
      let scheme' = match principle_type fun_ty c_all with
        | Some s -> s
        | None -> failwith "let rec binding not typable"
      in
      infer (Env.add name scheme' env) body

  | Let { is_rec = true; _ } ->
      failwith "let rec must bind function"

  | PairMatch { matched; fst_name; snd_name; case } ->
      let matched_ty, c1 = infer env matched in
      let a = TVar (gensym ()) in
      let b = TVar (gensym ()) in
      let env' = env |> Env.add fst_name (Forall (VarSet.empty, a))
                     |> Env.add snd_name (Forall (VarSet.empty, b)) in
      let body_ty, c2 = infer env' case in
      (body_ty, (matched_ty, TPair (a, b)) :: (c1 @ c2))

  | OptMatch { matched; some_name; some_case; none_case } ->
      let t, c1 = infer env matched in
      let a = TVar (gensym ()) in
      let env' = Env.add some_name (Forall (VarSet.empty, a)) env in
      let t1, c2 = infer env' some_case in
      let t2, c3 = infer env none_case in
      (t2, (t, TOption a) :: (t1, t2) :: (c1 @ c2 @ c3))

  | ListMatch { matched; hd_name; tl_name; cons_case; nil_case } ->
      let t, c1 = infer env matched in
      let a = TVar (gensym ()) in
      let env' = env
        |> Env.add hd_name (Forall (VarSet.empty, a))
        |> Env.add tl_name (Forall (VarSet.empty, TList a))
      in
      let t1, c2 = infer env' cons_case in
      let t2, c3 = infer env nil_case in
      (t2, (t, TList a) :: (t1, t2) :: (c1 @ c2 @ c3))


let parse (s : string) : prog option =
  match Parser.prog Lexer.read (Lexing.from_string s) with
  | prog -> Some prog
  | exception _ -> None

let rec free_vars_env (env : stc_env) : VarSet.t =
  Env.fold
    (fun _ (Forall (vars, ty)) acc ->
       VarSet.union (VarSet.diff (free_type_vars ty) vars) acc)
    env VarSet.empty

let type_of (env : stc_env) (e : expr) : ty_scheme option =
  let ty, cs = infer env e in
  principle_type ty cs

let is_well_typed (p : prog) : bool =
  let rec go (env : stc_env) (p : prog) : bool =
    match p with
    | [] -> true
    | { is_rec = false; name; binding } :: rest ->
        (match type_of env binding with
         | Some sigma ->
             let env' = Env.add name sigma env in
             go env' rest
         | None -> false)

    | { is_rec = true; name; binding = Fun (x, annot, body) } :: rest ->
        let arg_ty = match annot with
          | Some t -> t
          | None -> TVar (gensym ())
        in
        let ret_ty = TVar (gensym ()) in
        let fun_ty = TFun (arg_ty, ret_ty) in
        let scheme = Forall (VarSet.empty, fun_ty) in
        let env' = env
          |> Env.add name scheme
          |> Env.add x (Forall (VarSet.empty, arg_ty))
        in
        (match principle_type ret_ty [(ret_ty, fst (infer env' body))] with
         | Some s ->
             let env'' = Env.add name s env in
             go env'' rest
         | None -> false)

    | { is_rec = true; _ } :: _ ->
        false 
  in go Env.empty p


exception AssertFail
exception DivByZero
exception CompareFunVals

let rec eval_expr (env : dyn_env) (e : expr) : value =
  match e with
  | Unit -> VUnit
  | Bool b -> VBool b
  | Int n -> VInt n
  | Float f -> VFloat f
  | Nil -> VList []
  | ENone -> VNone
  | Var x -> Env.find x env

  | ESome e1 ->
      let v1 = eval_expr env e1 in
      VSome v1

  | Bop (Cons, e1, e2) ->
      let v1 = eval_expr env e1 in
      let v2 = eval_expr env e2 in
      (match v2 with
       | VList vs -> VList (v1 :: vs)
       | _ -> failwith "cons on non-list")

  | ListMatch { matched; hd_name; tl_name; cons_case; nil_case } ->
      (match eval_expr env matched with
       | VList (v1 :: vs) ->
           let env' = env |> Env.add hd_name v1 |> Env.add tl_name (VList vs) in
           eval_expr env' cons_case
       | VList [] -> eval_expr env nil_case
       | _ -> failwith "match on non-list")

  | OptMatch { matched; some_name; some_case; none_case } ->
      (match eval_expr env matched with
       | VSome v -> eval_expr (Env.add some_name v env) some_case
       | VNone -> eval_expr env none_case
       | _ -> failwith "match on non-option")

  | PairMatch { matched; fst_name; snd_name; case } ->
      (match eval_expr env matched with
       | VPair (v1, v2) ->
           eval_expr (env |> Env.add fst_name v1 |> Env.add snd_name v2) case
       | _ -> failwith "match on non-pair")

  | Annot (e, _) -> eval_expr env e

  | Assert e ->
      (match eval_expr env e with
       | VBool true -> VUnit
       | VBool false -> raise AssertFail
       | _ -> failwith "assert on non-bool")

  | Bop (op, e1, e2) ->
      let v1 = eval_expr env e1 in
      let v2 = eval_expr env e2 in
      eval_bop op v1 v2

  | If (e1, e2, e3) ->
      (match eval_expr env e1 with
       | VBool true -> eval_expr env e2
       | VBool false -> eval_expr env e3
       | _ -> failwith "if condition not bool")

  | Fun (x, _, body) ->
      VClos { name = None; arg = x; body; env }

  | App (e1, e2) ->
      let vf = eval_expr env e1 in
      let v2 = eval_expr env e2 in
      (match vf with
       | VClos { name = None; arg; body; env = clos_env } ->
           eval_expr (Env.add arg v2 clos_env) body
       | VClos { name = Some f; arg; body; env = clos_env } ->
           let clos_env' = clos_env |> Env.add f vf |> Env.add arg v2 in
           eval_expr clos_env' body
       | _ -> failwith "application of non-function")

  | Let { is_rec = false; name; binding; body } ->
      let vb = eval_expr env binding in
      eval_expr (Env.add name vb env) body

  | Let { is_rec = true; name; binding = Fun (arg, _, body_fn); body } ->
      let rec_clos = VClos { name = Some name; arg; body = body_fn; env } in
      let env' = Env.add name rec_clos env in
      eval_expr env' body

  | Let { is_rec = true; _ } -> failwith "let rec must bind a function"

and eval_bop op v1 v2 =
  match op, v1, v2 with
  | Add, VInt n1, VInt n2 -> VInt (n1 + n2)
  | Sub, VInt n1, VInt n2 -> VInt (n1 - n2)
  | Mul, VInt n1, VInt n2 -> VInt (n1 * n2)
  | Div, VInt _, VInt 0 -> raise DivByZero
  | Div, VInt n1, VInt n2 -> VInt (n1 / n2)
  | Mod, VInt _, VInt 0 -> raise DivByZero
  | Mod, VInt n1, VInt n2 -> VInt (n1 mod n2)

  | AddF, VFloat x, VFloat y -> VFloat (x +. y)
  | SubF, VFloat x, VFloat y -> VFloat (x -. y)
  | MulF, VFloat x, VFloat y -> VFloat (x *. y)
  | DivF, VFloat x, VFloat y -> VFloat (x /. y)
  | PowF, VFloat x, VFloat y -> VFloat (x ** y)

  | Eq, VClos _, _
  | Eq, _, VClos _
  | Lt, VClos _, _
  | Lt, _, VClos _ -> raise CompareFunVals

  | Eq, v1, v2 -> VBool (v1 = v2)
  | Neq, v1, v2 -> VBool (v1 <> v2)
  | Lt, VInt a, VInt b -> VBool (a < b)
  | Lte, VInt a, VInt b -> VBool (a <= b)
  | Gt, VInt a, VInt b -> VBool (a > b)
  | Gte, VInt a, VInt b -> VBool (a >= b)
  | And, VBool a, VBool b -> VBool (a && b)
  | Or, VBool a, VBool b -> VBool (a || b)
  | Comma, v1, v2 -> VPair (v1, v2)

  | _, _, _ -> failwith "unsupported binary operation"


let eval p =
  let rec nest = function
    | [] -> Unit
    | [{is_rec;name;binding}] -> Let {is_rec;name;binding;body = Var name}
    | {is_rec;name;binding} :: ls -> Let {is_rec;name;binding;body = nest ls}
  in eval_expr Env.empty (nest p)

let interp input =
  match parse input with
  | Some prog ->
    if is_well_typed prog
    then Ok (eval prog)
    else Error TypeError
  | None -> Error ParseError
