include Utils

let parse (s : string) : prog option =
  match Parser.prog Lexer.read (Lexing.from_string s) with
  | prog -> Some prog
  | exception _ -> None

let principle_type (_ty : ty) (_cs : constr list) : ty_scheme option = assert false

let type_of (_ctxt: stc_env) (_e : expr) : ty_scheme option = assert false

let is_well_typed (_p : prog) : bool = assert false

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
