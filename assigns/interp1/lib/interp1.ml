include Utils

let parse (s : string) : expr option =
  match Parser.prog Lexer.read (Lexing.from_string s) with
  | e -> Some e
  | exception _ -> None

let rec subst (v : value) (x : string) (e : expr) : expr =
  match e with
  | Num _ | True | False | Unit -> e
  | Var y -> if x = y then
               match v with
               | VNum n -> Num n
               | VBool b -> if b then True else False
               | VUnit -> Unit
               | VFun (arg, body) -> Fun (arg, body)
             else e
  | Bop (b, e1, e2) -> Bop (b, subst v x e1, subst v x e2)
  | App (e1, e2) -> App (subst v x e1, subst v x e2)
  | If (e1, e2, e3) -> If (subst v x e1, subst v x e2, subst v x e3)
  | Let (y, e1, e2) ->
      let e1' = subst v x e1 in
      if x = y then Let (y, e1', e2) else Let (y, e1', subst v x e2)
  | Fun (y, body) ->
      if x = y then e else Fun (y, subst v x body)


let rec eval (e : expr) : (value, error) result =
  let int_binop b op e1 e2 =
    match eval e1, eval e2 with
    | Ok (VNum n1), Ok (VNum n2) -> Ok (VNum (op n1 n2))
    | Ok _, Ok _ -> Error (InvalidArgs b)
    | Error err, _ | _, Error err -> Error err  
  in

  let safe_div b e1 e2 div_op =
    match eval e1, eval e2 with
    | Ok (VNum _), Ok (VNum 0) -> Error DivByZero
    | Ok (VNum n1), Ok (VNum n2) -> Ok (VNum (div_op n1 n2))
    | Ok _, Ok _ -> Error (InvalidArgs b)
    | Error err, _ | _, Error err -> Error err  
  in

  let compare_binop b cmp e1 e2 =
    match eval e1, eval e2 with
    | Ok (VNum n1), Ok (VNum n2) -> Ok (VBool (cmp n1 n2))
    | Ok _, Ok _ -> Error (InvalidArgs b)
    | Error err, _ | _, Error err -> Error err  
  in

  let eq_binop e1 e2 =
    match eval e1, eval e2 with
    | Ok (VNum n1), Ok (VNum n2) -> Ok (VBool (n1 = n2))
    | Ok (VBool b1), Ok (VBool b2) -> Ok (VBool (b1 = b2))
    | Ok VUnit, Ok VUnit -> Ok (VBool true)
    | Ok _, Ok _ -> Ok (VBool false)
    | Error err, _ | _, Error err -> Error err
  in

  let neq_binop e1 e2 =
    match eq_binop e1 e2 with
    | Ok (VBool b) -> Ok (VBool (not b))
    | res -> res
  in

  let and_op e1 e2 =
    match eval e1 with
    | Ok (VBool false) -> Ok (VBool false)
    | Ok (VBool true) ->
        (match eval e2 with
         | Ok (VBool b) -> Ok (VBool b)
         | Ok _ -> Error (InvalidArgs And)
         | Error err -> Error err)
    | Ok _ -> Error (InvalidArgs And)
    | Error err -> Error err
  in

  let or_op e1 e2 =
    match eval e1 with
    | Ok (VBool true) -> Ok (VBool true)
    | Ok (VBool false) ->
        (match eval e2 with
         | Ok (VBool b) -> Ok (VBool b)
         | Ok _ -> Error (InvalidArgs Or)
         | Error err -> Error err)
    | Ok _ -> Error (InvalidArgs Or)
    | Error err -> Error err
  in

  match e with
  | Num n -> Ok (VNum n)
  | True -> Ok (VBool true)
  | False -> Ok (VBool false)
  | Unit -> Ok VUnit
  | Var _ -> Error (UnknownVar "unexpected variable during evaluation")
  | Bop (b, e1, e2) ->
    begin match b with
    | Add -> int_binop Add ( + ) e1 e2
    | Sub -> int_binop Sub ( - ) e1 e2
    | Mul -> int_binop Mul ( * ) e1 e2
    | Div -> safe_div Div e1 e2 ( / )
    | Mod -> safe_div Mod e1 e2 ( mod )
    | Lt  -> compare_binop Lt ( < ) e1 e2
    | Lte -> compare_binop Lte ( <= ) e1 e2
    | Gt  -> compare_binop Gt ( > ) e1 e2
    | Gte -> compare_binop Gte ( >= ) e1 e2
    | Eq  -> eq_binop e1 e2
    | Neq -> neq_binop e1 e2
    | And -> and_op e1 e2
    | Or  -> or_op e1 e2
    end

  | If (e1, e2, e3) ->
      begin match eval e1 with
      | Ok (VBool true) -> eval e2
      | Ok (VBool false) -> eval e3
      | Ok _ -> Error InvalidIfCond
      | Error err -> Error err
      end
  | Let (x, e1, e2) ->
      begin match eval e1 with
      | Ok v1 ->
          let e2' = subst v1 x e2 in
          eval e2'
      | Error err -> Error err
      end
  | Fun (x, body) -> Ok (VFun (x, body))
  | App (e1, e2) ->
      begin match eval e1 with
      | Ok (VFun (x, body)) ->
          begin match eval e2 with
          | Ok v2 ->
              let body' = subst v2 x body in
              eval body'
          | Error err -> Error err
          end
      | Ok _ -> Error InvalidApp
      | Error err -> Error err
      end



let interp (s : string) : (value, error) result =
  match parse s with
  | None -> Error ParseFail
  | Some e ->
    let rec check_free e =
      match e with
      | Var x -> Some x
      | Num _ | True | False | Unit -> None
      | Bop (_, e1, e2) | App (e1, e2) ->
          (match check_free e1 with
           | Some x -> Some x
           | None -> check_free e2)
      | If (e1, e2, e3) ->
          (match check_free e1 with
           | Some x -> Some x
           | None ->
             match check_free e2 with
             | Some x -> Some x
             | None -> check_free e3)
      | Let (_x, e1, e2) ->
          (match check_free e1 with
           | Some y -> Some y
           | None -> check_free e2)
      | Fun (_x, body) -> check_free body
    in
    match check_free e with
    | Some x -> Error (UnknownVar x)
    | None -> eval e
