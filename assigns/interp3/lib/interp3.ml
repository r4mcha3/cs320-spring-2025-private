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
  (* Literals *)
  | Unit -> VUnit
  | Bool b -> VBool b
  | Int n -> VInt n
  | Float f -> VFloat f
  | Nil -> VList []
  | ENone -> VNone

  (* Variables *)
  | Var x -> (
      try Env.find x env
      with Not_found -> failwith ("Unbound variable: " ^ x)
    )

  (* Assertions *)
  | Assert e1 -> (
      match eval_expr env e1 with
      | VBool true -> VUnit
      | VBool false -> raise AssertFail
      | _ -> failwith "Assert must evaluate to bool"
    )

  (* Some *)
  | ESome e1 ->
      let v1 = eval_expr env e1 in
      VSome v1

  (* Binary Operators *)
  | Bop (bop, e1, e2) ->
      let v1 = eval_expr env e1 in
      let v2 = eval_expr env e2 in
      eval_binop bop v1 v2

  (* If-then-else *)
  | If (cond, e_then, e_else) -> (
      match eval_expr env cond with
      | VBool true -> eval_expr env e_then
      | VBool false -> eval_expr env e_else
      | _ -> failwith "Condition must be boolean"
    )

  (* List Match *)
  | ListMatch { matched; hd_name; tl_name; cons_case; nil_case } -> (
      match eval_expr env matched with
      | VList (h :: t) ->
          let env' = Env.add hd_name h (Env.add tl_name (VList t) env) in
          eval_expr env' cons_case
      | VList [] ->
          eval_expr env nil_case
      | _ -> failwith "ListMatch expects a list"
    )

  (* Option Match *)
  | OptMatch { matched; some_name; some_case; none_case } -> (
      match eval_expr env matched with
      | VSome v ->
          let env' = Env.add some_name v env in
          eval_expr env' some_case
      | VNone ->
          eval_expr env none_case
      | _ -> failwith "OptMatch expects an option"
    )

  (* Pair Match *)
  | PairMatch { matched; fst_name; snd_name; case } -> (
      match eval_expr env matched with
      | VPair (v1, v2) ->
          let env' = Env.add fst_name v1 (Env.add snd_name v2 env) in
          eval_expr env' case
      | _ -> failwith "PairMatch expects a pair"
    )

  (* Functions (with or without annotation) *)
  | Fun (x, _, body) ->
      VClos { name = None; arg = x; body; env }

  (* Function Application *)
  | App (e1, e2) -> (
      match eval_expr env e1 with
      | VClos { name = None; arg; body; env = clos_env } ->
          let v2 = eval_expr env e2 in
          eval_expr (Env.add arg v2 clos_env) body
      | VClos { name = Some f; arg; body; env = clos_env } ->
          let v2 = eval_expr env e2 in
          let clos_env' = Env.add arg v2 (Env.add f (VClos { name = Some f; arg; body; env = clos_env }) clos_env) in
          eval_expr clos_env' body
      | _ -> failwith "Attempt to apply a non-closure"
    )

  (* Type Annotation *)
  | Annot (e1, _) ->
      eval_expr env e1

  (* Let and Let Rec *)
  | Let { is_rec; name; binding; body } ->
      if is_rec then
        let dummy = ref VUnit in
        let rec_clos = VClos { name = Some name; arg = ""; body = binding; env = env } in
        let env' = Env.add name rec_clos env in
        let v1 = eval_expr env' binding in
        let env'' = Env.add name v1 env in
        eval_expr env'' body
      else
        let v1 = eval_expr env binding in
        let env' = Env.add name v1 env in
        eval_expr env' body

(* Helper for evaluating binary operations *)
and eval_binop bop v1 v2 =
  match bop, v1, v2 with
  (* Integer arithmetic *)
  | Add, VInt i1, VInt i2 -> VInt (i1 + i2)
  | Sub, VInt i1, VInt i2 -> VInt (i1 - i2)
  | Mul, VInt i1, VInt i2 -> VInt (i1 * i2)
  | Div, VInt i1, VInt i2 ->
      if i2 = 0 then raise DivByZero else VInt (i1 / i2)
  | Mod, VInt i1, VInt i2 ->
      if i2 = 0 then raise DivByZero else VInt (i1 mod i2)

  (* Float arithmetic *)
  | AddF, VFloat f1, VFloat f2 -> VFloat (f1 +. f2)
  | SubF, VFloat f1, VFloat f2 -> VFloat (f1 -. f2)
  | MulF, VFloat f1, VFloat f2 -> VFloat (f1 *. f2)
  | DivF, VFloat f1, VFloat f2 -> VFloat (f1 /. f2)
  | PowF, VFloat f1, VFloat f2 -> VFloat (f1 ** f2)

  (* Comparisons *)
  | Lt, v1, v2 -> VBool (compare_values v1 v2 (<))
  | Lte, v1, v2 -> VBool (compare_values v1 v2 (<=))
  | Gt, v1, v2 -> VBool (compare_values v1 v2 (>))
  | Gte, v1, v2 -> VBool (compare_values v1 v2 (>=))
  | Eq, v1, v2 -> VBool (compare_values v1 v2 (=))
  | Neq, v1, v2 -> VBool (compare_values v1 v2 (<>))

  (* Boolean operations *)
  | And, VBool b1, VBool b2 -> VBool (b1 && b2)
  | Or, VBool b1, VBool b2 -> VBool (b1 || b2)

  (* List operations *)
  | Cons, v1, VList l -> VList (v1 :: l)

  (* Pair creation *)
  | Comma, v1, v2 -> VPair (v1, v2)

  | _, _, _ -> failwith "Invalid operands for binary operator"

(* Helper for comparisons *)
and compare_values v1 v2 op =
  match v1, v2 with
  | VInt i1, VInt i2 -> op i1 i2
  | VFloat f1, VFloat f2 -> op f1 f2
  | VBool b1, VBool b2 -> op b1 b2
  | VUnit, VUnit -> op 0 0
  | VNone, VNone -> op 0 0
  | VSome v1, VSome v2 -> compare_values v1 v2 op
  | VList l1, VList l2 -> op (List.length l1) (List.length l2)
  | VPair (a1,b1), VPair (a2,b2) -> op (a1 = a2 && b1 = b2) true
  | VClos _, _ | _, VClos _ -> raise CompareFunVals
  | _, _ -> failwith "Cannot compare values of different types"

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
