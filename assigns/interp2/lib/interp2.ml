open Utils
open Result

module TyEnv = Map.Make(String)

let (let*) = Result.bind

let parse (s : string) : prog option =
  match Parser.prog Lexer.read (Lexing.from_string s) with
  | e -> Some e
  | exception _ -> None

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
    List.fold_left
      (fun acc arg -> App (acc, desugar_expr arg))
      (desugar_expr f)
      args
  | SApp [] -> failwith "Empty application"
  | SFun { args; body } ->
    List.fold_right
      (fun (arg_name, arg_ty) acc -> Fun (arg_name, arg_ty, acc))
      args
      (desugar_expr body)
  | SLet { is_rec; name; args; ty; binding; body } ->
    let binding_expr =
      List.fold_right
        (fun (arg_name, arg_ty) acc -> Fun (arg_name, arg_ty, acc))
        args
        (desugar_expr binding)
    in
    Let { is_rec; name; ty; binding = binding_expr; body = desugar_expr body }

let desugar_let ({ is_rec; name; args; ty; binding } : toplet) (body : expr) : expr =
  let func_expr =
    List.fold_right
      (fun (arg_name, arg_ty) acc -> Fun (arg_name, arg_ty, acc))
      args
      (desugar_expr binding)
  in
  Let { is_rec; name; ty; binding = func_expr; body }

let desugar (prog : prog) : expr =
  match prog with
  | [] -> Unit
  | lets ->
    let rec go lets =
      match lets with
      | [] -> failwith "unreachable"
      | [last] -> desugar_let last (Var last.name)
      | hd :: tl -> desugar_let hd (go tl)
    in go lets

let rec typecheck (env : ty TyEnv.t) (e : expr) : (ty, error) result =
  match e with
  | Unit -> Ok UnitTy
  | Bool _ -> Ok BoolTy
  | Num _ -> Ok IntTy
  | Var x ->
      (match TyEnv.find_opt x env with
       | Some t -> Ok t
       | None -> Error (UnknownVar x))
  | Bop (op, e1, e2) ->
      let* t1 = typecheck env e1 in
      let* t2 = typecheck env e2 in
      begin match op, t1, t2 with
      | (Add | Sub | Mul | Div | Mod), IntTy, IntTy -> Ok IntTy
      | (Lt | Lte | Gt | Gte | Eq | Neq), IntTy, IntTy -> Ok BoolTy
      | (And | Or), BoolTy, BoolTy -> Ok BoolTy
      | (Add | Sub | Mul | Div | Mod), _, _ when t1 <> IntTy -> Error (OpTyErrL (op, IntTy, t1))
      | (Add | Sub | Mul | Div | Mod), _, _ -> Error (OpTyErrR (op, IntTy, t2))
      | (Lt | Lte | Gt | Gte | Eq | Neq), _, _ when t1 <> IntTy -> Error (OpTyErrL (op, IntTy, t1))
      | (Lt | Lte | Gt | Gte | Eq | Neq), _, _ -> Error (OpTyErrR (op, IntTy, t2))
      | (And | Or), _, _ when t1 <> BoolTy -> Error (OpTyErrL (op, BoolTy, t1))
      | (And | Or), _, _ -> Error (OpTyErrR (op, BoolTy, t2))
      end
  | If (e1, e2, e3) ->
      let* t1 = typecheck env e1 in
      if t1 <> BoolTy then Error (IfCondTyErr t1) else
      let* t2 = typecheck env e2 in
      let* t3 = typecheck env e3 in
      if t2 = t3 then Ok t2 else Error (IfTyErr (t2, t3))
  | Fun (x, ty_x, body) ->
      let env' = TyEnv.add x ty_x env in
      let* t_body = typecheck env' body in
      Ok (FunTy (ty_x, t_body))
  | App (e1, e2) ->
      let* t1 = typecheck env e1 in
      let* t2 = typecheck env e2 in
      match t1 with
      | FunTy (arg_ty, ret_ty) ->
          if arg_ty = t2 then Ok ret_ty
          else Error (FunArgTyErr (arg_ty, t2))
      | _ -> Error (FunAppTyErr t1)
  | Let { is_rec = false; name; ty = ty_annot; binding; body } ->
      let* t1 = typecheck env binding in
      if t1 = ty_annot then typecheck (TyEnv.add name ty_annot env) body
      else Error (LetTyErr (ty_annot, t1))
  | Let { is_rec = true; name; ty = ty_annot; binding = Fun (arg, arg_ty, fun_body); body } ->
      let fun_ty = ty_annot in
      let env' = TyEnv.add name fun_ty env in
      let env'' = TyEnv.add arg arg_ty env' in
      let* actual_ret_ty = typecheck env'' fun_body in
      begin match fun_ty with
      | FunTy (_, ret_ty) when actual_ret_ty = ret_ty -> typecheck env' body
      | FunTy (_, ret_ty) -> Error (LetTyErr (ret_ty, actual_ret_ty))
      | _ -> Error (LetRecErr name)
      end
  | Let { is_rec = true; name; _ } ->
      Error (LetRecErr name)
  | Assert e ->
      let* t = typecheck env e in
      if t = BoolTy then Ok UnitTy else Error (AssertTyErr t)

let type_of e = typecheck TyEnv.empty e

exception AssertFail
exception DivByZero

let rec eval_expr (env : dyn_env) (e : expr) : value =
  match e with
  | Unit -> VUnit
  | Bool b -> VBool b
  | Num n -> VNum n
  | Var x -> Env.find x env
  | Bop (op, e1, e2) ->
    let v1 = eval_expr env e1 in
    let v2 = eval_expr env e2 in
    begin match (op, v1, v2) with
    | (Add, VNum a, VNum b) -> VNum (a + b)
    | (Sub, VNum a, VNum b) -> VNum (a - b)
    | (Mul, VNum a, VNum b) -> VNum (a * b)
    | (Div, VNum _, VNum 0) | (Mod, VNum _, VNum 0) -> raise DivByZero
    | (Div, VNum a, VNum b) -> VNum (a / b)
    | (Mod, VNum a, VNum b) -> VNum (a mod b)
    | (Lt, VNum a, VNum b) -> VBool (a < b)
    | (Lte, VNum a, VNum b) -> VBool (a <= b)
    | (Gt, VNum a, VNum b) -> VBool (a > b)
    | (Gte, VNum a, VNum b) -> VBool (a >= b)
    | (Eq, VNum a, VNum b) -> VBool (a = b)
    | (Neq, VNum a, VNum b) -> VBool (a <> b)
    | (And, VBool false, _) -> VBool false
    | (And, VBool true, VBool b) -> VBool b
    | (Or, VBool true, _) -> VBool true
    | (Or, VBool false, VBool b) -> VBool b
    | _ -> failwith "ill-typed bop"
    end
  | If (e1, e2, e3) ->
    (match eval_expr env e1 with
     | VBool true -> eval_expr env e2
     | VBool false -> eval_expr env e3
     | _ -> failwith "ill-typed if")
  | Fun (x, _ty, body) -> VClos { arg = x; body; env; name = None }
  | App (e1, e2) ->
    let v1 = eval_expr env e1 in
    let v2 = eval_expr env e2 in
    begin match v1 with
    | VClos { arg; body; env = clos_env; name = None } ->
      eval_expr (Env.add arg v2 clos_env) body
    | VClos { arg; body; env = clos_env; name = Some f } ->
      eval_expr (Env.add arg v2 (Env.add f v1 clos_env)) body
    | _ -> failwith "application of non-function"
    end
  | Let { is_rec = false; name; ty = _; binding; body } ->
    let v1 = eval_expr env binding in
    eval_expr (Env.add name v1 env) body
  | Let { is_rec = true; name; ty = _; binding = Fun (arg, _arg_ty, body_fun); body } ->
    let rec_clos = VClos { arg; body = body_fun; env; name = Some name } in
    let env' = Env.add name rec_clos env in
    eval_expr env' body
  | Let { is_rec = true; _ } -> failwith "let rec must bind a function"
  | Assert e ->
    (match eval_expr env e with
     | VBool true -> VUnit
     | VBool false -> raise AssertFail
     | _ -> failwith "assert expects a bool")

let eval e = eval_expr Env.empty e

let interp (s : string) : (value, error) result =
  match parse s with
  | None -> Error ParseErr
  | Some p ->
    let expr = desugar p in
    match type_of expr with
    | Error err -> Error err
    | Ok _ -> Ok (eval expr)
