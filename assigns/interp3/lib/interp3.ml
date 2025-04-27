include Utils

let parse (s : string) : prog option =
  match Parser.prog Lexer.read (Lexing.from_string s) with
  | prog -> Some prog
  | exception _ -> None

type subst = (ident * ty) list

let rec apply_subst (s : subst) (t : ty) : ty =
  match t with
  | TUnit | TInt | TFloat | TBool -> t
  | TVar x ->
      (match List.assoc_opt x s with
       | Some t' -> t'
       | None -> TVar x)
  | TList t1 -> TList (apply_subst s t1)
  | TOption t1 -> TOption (apply_subst s t1)
  | TPair (t1, t2) -> TPair (apply_subst s t1, apply_subst s t2)
  | TFun (t1, t2) -> TFun (apply_subst s t1, apply_subst s t2)

let compose_subst (s1 : subst) (s2 : subst) : subst =
  List.map (fun (x, t) -> (x, apply_subst s1 t)) s2 @ s1

let rec unify (cs : constr list) : subst option =
  match cs with
  | [] -> Some []
  | (t1, t2) :: rest ->
      if t1 = t2 then
        unify rest
      else
        match (t1, t2) with
        | (TVar x, t) | (t, TVar x) ->
            if occurs x t then
              None
            else
              let rest' = List.map (fun (l, r) -> (subst_one x t l, subst_one x t r)) rest in
              (match unify rest' with
               | Some s -> Some ((x, t) :: s)
               | None -> None)
        | (TList t1, TList t2)
        | (TOption t1, TOption t2) ->
            unify ((t1, t2) :: rest)
        | (TPair (l1, r1), TPair (l2, r2))
        | (TFun (l1, r1), TFun (l2, r2)) ->
            unify ((l1, l2) :: (r1, r2) :: rest)
        | _ -> None

and subst_one (x : ident) (t : ty) (t' : ty) : ty =
  apply_subst [(x, t)] t'

and occurs (x : ident) (t : ty) : bool =
  match t with
  | TUnit | TInt | TFloat | TBool -> false
  | TVar y -> x = y
  | TList t1
  | TOption t1 -> occurs x t1
  | TPair (t1, t2)
  | TFun (t1, t2) -> occurs x t1 || occurs x t2

let rec free_vars_ty (t : ty) : VarSet.t =
  match t with
  | TUnit | TInt | TFloat | TBool -> VarSet.empty
  | TVar x -> VarSet.singleton x
  | TList t1 | TOption t1 -> free_vars_ty t1
  | TPair (t1, t2) | TFun (t1, t2) -> VarSet.union (free_vars_ty t1) (free_vars_ty t2)

let generalize (t : ty) : ty_scheme =
  Forall (free_vars_ty t, t)

let principle_type (ty : ty) (cs : constr list) : ty_scheme option =
  match unify cs with
  | None -> None
  | Some subst ->
      let ty' = apply_subst subst ty in
      Some (generalize ty')


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

(* Helper for evaluating binaries *)
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

  (* Float *)
  | AddF, VFloat f1, VFloat f2 -> VFloat (f1 +. f2)
  | SubF, VFloat f1, VFloat f2 -> VFloat (f1 -. f2)
  | MulF, VFloat f1, VFloat f2 -> VFloat (f1 *. f2)
  | DivF, VFloat f1, VFloat f2 -> VFloat (f1 /. f2)
  | PowF, VFloat f1, VFloat f2 -> VFloat (f1 ** f2)

  (* Comparisons *)
  | Lt, VInt i1, VInt i2 -> VBool (i1 < i2)
  | Lte, VInt i1, VInt i2 -> VBool (i1 <= i2)
  | Gt, VInt i1, VInt i2 -> VBool (i1 > i2)
  | Gte, VInt i1, VInt i2 -> VBool (i1 >= i2)
  | Lt, VFloat f1, VFloat f2 -> VBool (f1 < f2)
  | Lte, VFloat f1, VFloat f2 -> VBool (f1 <= f2)
  | Gt, VFloat f1, VFloat f2 -> VBool (f1 > f2)
  | Gte, VFloat f1, VFloat f2 -> VBool (f1 >= f2)

  (* Equality *)
  | Eq, VInt i1, VInt i2 -> VBool (i1 = i2)
  | Eq, VFloat f1, VFloat f2 -> VBool (f1 = f2)
  | Neq, VInt i1, VInt i2 -> VBool (i1 <> i2)
  | Neq, VFloat f1, VFloat f2 -> VBool (f1 <> f2)
  | Eq, VBool b1, VBool b2 -> VBool (b1 = b2)
  | Neq, VBool b1, VBool b2 -> VBool (b1 <> b2)
  | Eq, VUnit, VUnit -> VBool true
  | Neq, VUnit, VUnit -> VBool false
  | Eq, VNone, VNone -> VBool true
  | Neq, VNone, VNone -> VBool false
  | Eq, VSome v1, VSome v2 -> eval_binop Eq v1 v2
  | Neq, VSome v1, VSome v2 -> eval_binop Neq v1 v2


  | And, VBool b1, VBool b2 -> VBool (b1 && b2)
  | Or, VBool b1, VBool b2 -> VBool (b1 || b2)

  | Cons, v1, VList l -> VList (v1 :: l)

  | Comma, v1, v2 -> VPair (v1, v2)

  | _, _, _ -> failwith "Invalid operands for binary operator"

(* Helper for comparisons *)
and compare_values v1 v2 op =
  match v1, v2 with
  | VInt i1, VInt i2 -> op i1 i2
  | VBool b1, VBool b2 ->
      if op 1 1 = true then (b1 = b2) else (b1 <> b2)
  | VUnit, VUnit -> op 0 0
  | VNone, VNone -> op 0 0
  | VSome v1, VSome v2 -> compare_values v1 v2 op
  | VList l1, VList l2 -> op (List.length l1) (List.length l2)
  | VPair (a1, b1), VPair (a2, b2) -> op ((if a1 = a2 && b1 = b2 then 1 else 0)) 1
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
