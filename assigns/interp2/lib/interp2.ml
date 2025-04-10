include Utils

let parse (s : string) : prog option =
  match Parser.prog Lexer.read (Lexing.from_string s) with
  | e -> Some e
  | exception _ -> None

module TyEnv = Map.Make (String)

let rec desugar_expr (e : sfexpr) : expr =
  match e with
  | SUnit -> Unit
  | SBool b -> Bool b
  | SNum n -> Num n
  | SVar x -> Var x
  | SIf (e1, e2, e3) -> If (desugar_expr e1, desugar_expr e2, desugar_expr e3)
  | SBop (op, e1, e2) -> Bop (op, desugar_expr e1, desugar_expr e2)
  | SAssert e -> Assert (desugar_expr e)
  | SApp (f :: args) ->
      List.fold_left (fun acc arg -> App (acc, arg)) (desugar_expr f) (List.map desugar_expr args)
  | SApp [] -> failwith "empty application"
  | SFun { args; body } ->
      List.fold_right (fun (x, ty) acc -> Fun (x, ty, acc)) args (desugar_expr body)
  | SLet { is_rec; name; args; ty; binding; body } ->
      let func_expr =
        List.fold_right (fun (x, ty) acc -> Fun (x, ty, acc)) args (desugar_expr binding)
      in
      Let { is_rec; name; ty; binding = func_expr; body = desugar_expr body }

let desugar_let { is_rec; name; args; ty; binding } body =
  let func_expr =
    List.fold_right (fun (x, ty) acc -> Fun (x, ty, acc)) args (desugar_expr binding)
  in
  Let { is_rec; name; ty; binding = func_expr; body }

let desugar (prog : prog) : expr =
  match prog with
  | [] -> Unit
  | lets ->
      let rec nest = function
        | [] -> failwith "empty prog"
        | [last] -> desugar_let last (Var last.name)
        | hd :: tl -> desugar_let hd (nest tl)
      in
      nest lets

let rec typecheck (env : ty TyEnv.t) (e : expr) : (ty, error) result =
  match e with
  | Unit -> Ok UnitTy
  | Bool _ -> Ok BoolTy
  | Num _ -> Ok IntTy
  | Var x ->
      (match TyEnv.find_opt x env with Some t -> Ok t | None -> Error (UnknownVar x))
  | Bop (op, e1, e2) ->
      let open Result in
      typecheck env e1 >>= fun t1 ->
      typecheck env e2 >>= fun t2 ->
      match op, t1, t2 with
      | (Add | Sub | Mul | Div | Mod), IntTy, IntTy -> Ok IntTy
      | (Lt | Lte | Gt | Gte | Eq | Neq), IntTy, IntTy -> Ok BoolTy
      | (And | Or), BoolTy, BoolTy -> Ok BoolTy
      | (Add | Sub | Mul | Div | Mod), t1, _ when t1 <> IntTy -> Error (OpTyErrL (op, IntTy, t1))
      | (Add | Sub | Mul | Div | Mod), _, t2 -> Error (OpTyErrR (op, IntTy, t2))
      | (Lt | Lte | Gt | Gte | Eq | Neq), t1, _ when t1 <> IntTy -> Error (OpTyErrL (op, IntTy, t1))
      | (Lt | Lte | Gt | Gte | Eq | Neq), _, t2 -> Error (OpTyErrR (op, IntTy, t2))
      | (And | Or), t1, _ when t1 <> BoolTy -> Error (OpTyErrL (op, BoolTy, t1))
      | (And | Or), _, t2 -> Error (OpTyErrR (op, BoolTy, t2))
  | If (e1, e2, e3) ->
      let open Result in
      typecheck env e1 >>= fun t1 ->
      if t1 <> BoolTy then Error (IfCondTyErr t1)
      else
        typecheck env e2 >>= fun t2 ->
        typecheck env e3 >>= fun t3 ->
        if t2 = t3 then Ok t2 else Error (IfTyErr (t2, t3))
  | Fun (x, ty_x, body) ->
      let env' = TyEnv.add x ty_x env in
      typecheck env' body >>= fun ty_body -> Ok (FunTy (ty_x, ty_body))
  | App (e1, e2) ->
      let open Result in
      typecheck env e1 >>= fun t1 ->
      typecheck env e2 >>= fun t2 ->
      (match t1 with
       | FunTy (arg_ty, ret_ty) ->
           if arg_ty = t2 then Ok ret_ty else Error (FunArgTyErr (arg_ty, t2))
       | _ -> Error (FunAppTyErr t1))
  | Let { is_rec = false; name; ty; binding; body } ->
      let open Result in
      typecheck env binding >>= fun t1 ->
      if t1 = ty then
        let env' = TyEnv.add name ty env in
        typecheck env' body
      else Error (LetTyErr (ty, t1))
  | Let { is_rec = true; name; ty; binding = Fun (arg, arg_ty, fun_body); body } ->
      let fun_ty = ty in
      let env' = TyEnv.add name fun_ty env in
      let env'' = TyEnv.add arg arg_ty env' in
      typecheck env'' fun_body >>= fun actual_ret_ty ->
      (match fun_ty with
       | FunTy (_, expected_ret_ty) when expected_ret_ty = actual_ret_ty ->
           typecheck env' body
       | FunTy (_, expected_ret_ty) -> Error (LetTyErr (expected_ret_ty, actual_ret_ty))
       | _ -> assert false)
  | Let { is_rec = true; name; _ } -> Error (LetRecErr name)
  | Assert e ->
      typecheck env e >>= fun ty ->
      if ty = BoolTy then Ok UnitTy else Error (AssertTyErr ty)

let type_of e = typecheck TyEnv.empty e

let rec eval_expr (env : dyn_env) (e : expr) : value =
  match e with
  | Unit -> VUnit
  | Bool b -> VBool b
  | Num n -> VNum n
  | Var x -> Env.find x env
  | Bop (op, e1, e2) ->
      let v1 = eval_expr env e1 in
      let v2 = eval_expr env e2 in
      (match op, v1, v2 with
       | Add, VNum a, VNum b -> VNum (a + b)
       | Sub, VNum a, VNum b -> VNum (a - b)
       | Mul, VNum a, VNum b -> VNum (a * b)
       | Div, VNum _, VNum 0 | Mod, VNum _, VNum 0 -> raise DivByZero
       | Div, VNum a, VNum b -> VNum (a / b)
       | Mod, VNum a, VNum b -> VNum (a mod b)
       | Lt, VNum a, VNum b -> VBool (a < b)
       | Lte, VNum a, VNum b -> VBool (a <= b)
       | Gt, VNum a, VNum b -> VBool (a > b)
       | Gte, VNum a, VNum b -> VBool (a >= b)
       | Eq, VNum a, VNum b -> VBool (a = b)
       | Neq, VNum a, VNum b -> VBool (a <> b)
       | And, VBool a, VBool b -> VBool (a && b)
       | Or, VBool a, VBool b -> VBool (a || b)
       | _ -> failwith "invalid bop")
  | If (e1, e2, e3) ->
      (match eval_expr env e1 with
       | VBool true -> eval_expr env e2
       | VBool false -> eval_expr env e3
       | _ -> failwith "invalid if condition")
  | Fun (x, _ty, body) -> VClos { arg = x; body; env; name = None }
  | App (e1, e2) ->
      let f = eval_expr env e1 in
      let arg_val = eval_expr env e2 in
      (match f with
       | VClos { arg; body; env = clos_env; name = None } ->
           let env' = Env.add arg arg_val clos_env in
           eval_expr env' body
       | VClos { arg; body; env = clos_env; name = Some f_name } ->
           let env' = Env.add arg arg_val (Env.add f_name f clos_env) in
           eval_expr env' body
       | _ -> failwith "apply non-function")
  | Let { is_rec = false; name; binding; body; _ } ->
      let v1 = eval_expr env binding in
      let env' = Env.add name v1 env in
      eval_expr env' body
  | Let { is_rec = true; name; binding = Fun (arg, _arg_ty, body_fun); body; _ } ->
      let rec_clos = VClos { arg; body = body_fun; env; name = Some name } in
      let env' = Env.add name rec_clos env in
      eval_expr env' body
  | Let { is_rec = true; name; _ } ->
      failwith "ill-formed let rec"
  | Assert e ->
      (match eval_expr env e with
       | VBool true -> VUnit
       | VBool false -> raise AssertFail
       | _ -> failwith "invalid assert")

let eval e = eval_expr Env.empty e

let interp (s : string) : (value, error) result =
  match parse s with
  | None -> Error ParseErr
  | Some prog ->
      let expr = desugar prog in
      match type_of expr with
      | Error err -> Error err
      | Ok _ty -> Ok (eval expr)
