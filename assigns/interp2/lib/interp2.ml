include Utils

(* Part 0: Parsing *)

let parse (s : string) : prog option =
  match Parser.prog Lexer.read (Lexing.from_string s) with
  | e -> Some e
  | exception _ -> None

(* Part 1: Desugaring *)

let rec desugar (p : prog) : expr =
  match p with
  | [] -> Unit
  | _ ->
    let rec nest_lets = function
      | [] -> failwith "unreachable"
      | [last] ->
          let body = Var last.name in
          desugar_toplet last body
      | hd :: tl ->
          let body = nest_lets tl in
          desugar_toplet hd body
    in
    nest_lets p

and desugar_toplet (t : toplet) (body : expr) : expr =
  let f_expr = desugar_fun_args t.args t.binding in
  Let { name = t.name; is_rec = t.is_rec; ty = t.ty; binding = f_expr; body = body }

and desugar_fun_args (args : (string * ty) list) (e : sfexpr) : expr =
  let body = desugar_expr e in
  List.fold_right (fun (x, ty) acc -> Fun (x, ty, acc)) args body

and desugar_expr (e : sfexpr) : expr =
  match e with
  | SUnit -> Unit
  | SBool b -> Bool b
  | SNum n -> Num n
  | SVar x -> Var x
  | SAssert e1 -> Assert (desugar_expr e1)
  | SBop (op, e1, e2) -> Bop (op, desugar_expr e1, desugar_expr e2)
  | SIf (e1, e2, e3) -> If (desugar_expr e1, desugar_expr e2, desugar_expr e3)
  | SApp (f :: args) ->
      List.fold_left (fun acc arg -> App (acc, desugar_expr arg)) (desugar_expr f) args
  | SApp [] -> failwith "invalid empty application"
  | SFun { args; body } ->
      List.fold_right (fun (x, ty) acc -> Fun (x, ty, acc)) args (desugar_expr body)
  | SLet { is_rec; name; args; ty; binding; body } ->
    let binding_expr = desugar_fun_args args binding in
    Let {
      name = name;
      is_rec = is_rec;
      ty = ty;
      binding = binding_expr;
      body = desugar_expr body;
    }

(* Part 2: Type Checking *)

let lookup (env : (string * ty) list) (x : string) : (ty, error) result =
  match List.assoc_opt x env with
  | Some ty -> Ok ty
  | None -> Error (UnknownVar x)

let rec typecheck (env : (string * ty) list) (e : expr) : (ty, error) result =
  match e with
  | Unit -> Ok UnitTy
  | Bool _ -> Ok BoolTy
  | Num _ -> Ok IntTy
  | Var x -> lookup env x
  | Assert e1 ->
      (match typecheck env e1 with
      | Ok BoolTy -> Ok UnitTy
      | Ok t -> Error (AssertTyErr t)
      | Error err -> Error err)
  | If (e1, e2, e3) ->
    (match typecheck env e1 with
     | Ok BoolTy ->
         (match typecheck env e2 with
          | Ok t1 ->
              (match typecheck env e3 with
               | Ok t2 -> if t1 = t2 then Ok t1 else Error (IfTyErr (t1, t2))
               | Error err -> Error err)
          | Error err -> Error err)
     | Ok t -> Error (IfCondTyErr t)
     | Error err -> Error err)
  | Bop (op, e1, e2) -> typecheck_binop env op e1 e2
  | Fun (x, ty_x, body) ->
      (match typecheck ((x, ty_x) :: env) body with
      | Ok ty_body -> Ok (FunTy (ty_x, ty_body))
      | Error err -> Error err)
  | App (e1, e2) ->
      (match typecheck env e1 with
      | Ok (FunTy (param_ty, ret_ty)) ->
          (match typecheck env e2 with
          | Ok arg_ty -> if arg_ty = param_ty then Ok ret_ty else Error (FunArgTyErr (param_ty, arg_ty))
          | Error err -> Error err)
      | Ok t -> Error (FunAppTyErr t)
      | Error err -> Error err)
  | Let { is_rec = false; name = x; ty = ty_x; binding = e1; body = e2 } ->
      (match typecheck env e1 with
      | Ok t1 -> if t1 = ty_x then typecheck ((x, ty_x) :: env) e2 else Error (LetTyErr (ty_x, t1))
      | Error err -> Error err)
  | Let { is_rec = true; name = f; ty = ty_f; binding = e1; body = e2 } ->
      (match e1 with
      | Fun (x, ty_x, body) ->
          let extended = (f, ty_f) :: env in
          (match typecheck extended e1 with
          | Ok t1 -> if t1 = ty_f then typecheck extended e2 else Error (LetTyErr (ty_f, t1))
          | Error err -> Error err)
      | _ -> Error (LetRecErr f))

and typecheck_binop env op e1 e2 =
  let err_l expected actual = Error (OpTyErrL (op, expected, actual)) in
  let err_r expected actual = Error (OpTyErrR (op, expected, actual)) in
  match typecheck env e1 with
  | Error err -> Error err
  | Ok ty1 ->
      match typecheck env e2 with
      | Error err -> Error err
      | Ok ty2 ->
          let int_ops = [Add; Sub; Mul; Div; Mod] in
          let cmp_ops = [Lt; Lte; Gt; Gte; Eq; Neq] in
          let bool_ops = [And; Or] in
          if List.mem op int_ops then
            if ty1 <> IntTy then err_l IntTy ty1
            else if ty2 <> IntTy then err_r IntTy ty2
            else Ok IntTy
          else if List.mem op cmp_ops then
            if ty1 <> IntTy then err_l IntTy ty1
            else if ty2 <> IntTy then err_r IntTy ty2
            else Ok BoolTy
          else if List.mem op bool_ops then
            if ty1 <> BoolTy then err_l BoolTy ty1
            else if ty2 <> BoolTy then err_r BoolTy ty2
            else Ok BoolTy
          else failwith "unreachable: unknown operator"

let type_of (e : expr) : (ty, error) result =
  typecheck [] e

(* Part 3: Evaluation *)

exception AssertFail
exception DivByZero

let rec eval_expr (env : (string * value) list) (e : expr) : value =
  match e with
  | Num n -> VNum n
  | Bool b -> VBool b
  | Unit -> VUnit
  | Var x -> List.assoc x env
  | Assert e1 ->
      (match eval_expr env e1 with
      | VBool true -> VUnit
      | VBool false -> raise AssertFail
      | _ -> failwith "invalid assert")
  | If (e1, e2, e3) ->
      (match eval_expr env e1 with
      | VBool true -> eval_expr env e2
      | VBool false -> eval_expr env e3
      | _ -> failwith "invalid if condition")
  | Bop (op, e1, e2) ->
      let v1 = eval_expr env e1 in
      let v2 = eval_expr env e2 in
      eval_binop op v1 v2
  | Fun (x, _, body) -> VClos { arg = x; body = body; env = env; name = None }
  | App (e1, e2) ->
      let v1 = eval_expr env e1 in
      let v2 = eval_expr env e2 in
      (match v1 with
      | VClos (env', x, body) -> eval_expr ((x, v2) :: env') body
      | VRecClos (env', f, x, body) ->
          let env'' = (x, v2) :: (f, v1) :: env' in
          eval_expr env'' body
      | _ -> failwith "non-function application")
  | Let { is_rec = false; name = x; binding = e1; body = e2; _ } ->
      let v1 = eval_expr env e1 in
      eval_expr ((x, v1) :: env) e2
  | Let { is_rec = true; name = f; binding = e1; body = e2; _ } ->
      (match e1 with
      | Fun (x, _, body) ->
          let rec_clos = VRecClos (env, f, x, body) in
          eval_expr ((f, rec_clos) :: env) e2
      | _ -> failwith "let rec must bind a function")

and eval_binop op v1 v2 =
  let num_bin f = match v1, v2 with VNum a, VNum b -> VNum (f a b) | _ -> failwith "type error" in
  let bool_bin f = match v1, v2 with VBool a, VBool b -> VBool (f a b) | _ -> failwith "type error" in
  let cmp_bin f = match v1, v2 with VNum a, VNum b -> VBool (f a b) | _ -> failwith "type error" in
  match op with
  | Add -> num_bin ( + )
  | Sub -> num_bin ( - )
  | Mul -> num_bin ( * )
  | Div ->
      (match v2 with VNum 0 -> raise DivByZero | VNum b -> (match v1 with VNum a -> VNum (a / b) | _ -> failwith "type error") | _ -> failwith "type error")
  | Mod ->
      (match v2 with VNum 0 -> raise DivByZero | VNum b -> (match v1 with VNum a -> VNum (a mod b) | _ -> failwith "type error") | _ -> failwith "type error")
  | Lt -> cmp_bin ( < )
  | Lte -> cmp_bin ( <= )
  | Gt -> cmp_bin ( > )
  | Gte -> cmp_bin ( >= )
  | Eq -> VBool (v1 = v2)
  | Neq -> VBool (v1 <> v2)
  | And -> (match v1 with VBool false -> VBool false | VBool true -> v2 | _ -> failwith "type error")
  | Or -> (match v1 with VBool true -> VBool true | VBool false -> v2 | _ -> failwith "type error")

let eval (e : expr) : value =
  eval_expr [] e

(* Part 4: Interp *)

let interp (s : string) : (value, error) result =
  match parse s with
  | None -> Error ParseFail
  | Some prog ->
      let core = desugar prog in
      match type_of core with
      | Error err -> Error err
      | Ok _ -> Ok (eval core)
