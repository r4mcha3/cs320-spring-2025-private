type ty = 
  | TInt
  | TBool

type tok =
  | LParen
  | RParen
  | TNum of int
  | TAdd
  | TLt
  | TIf

let is_space = function
  | ' ' | '\012' | '\n' | '\r' | '\t' -> true
  | _ -> false

let is_keyword = function
  | '(' | ')' | '+' | '?' | '<' -> true
  | _ -> false

exception UnknownKeyword

let keyword_of_char = function
  | '(' -> LParen
  | ')' -> RParen
  | '+' -> TAdd
  | '<' -> TLt
  | '?' -> TIf
  | _ -> raise UnknownKeyword

let lex s =
  let rec go out i =
    if i >= String.length s
    then Some (List.rev out)
    else if is_space s.[i]
    then go out (i + 1)
    else if is_keyword s.[i]
    then go (keyword_of_char s.[i] :: out) (i + 1)
    else go' out i (i + 1)
  and go' out i j =
    if j >= String.length s
       || is_space s.[j]
       || is_keyword s.[j]
    then
      match int_of_string_opt (String.sub s i (j - i)) with
      | None -> None
      | Some n -> go ((TNum n) :: out) j
    else go' out i (j + 1)
  in go [] 0

type expr =
  | Num of int
  | Add of expr * expr
  | Lt of expr * expr
  | If of expr * expr * expr

let parse str =
  let rec parse_tokens tokens =
    match tokens with
    | TNum n :: rest -> Some (Num n, rest)
    | LParen :: TAdd :: rest ->
      (match parse_tokens rest with
       | Some (e1, rest1) ->
         (match parse_tokens rest1 with
          | Some (e2, RParen :: rest2) -> Some (Add (e1, e2), rest2)
          | _ -> None)
       | _ -> None)
    | LParen :: TLt :: rest ->
      (match parse_tokens rest with
       | Some (e1, rest1) ->
         (match parse_tokens rest1 with
          | Some (e2, RParen :: rest2) -> Some (Lt (e1, e2), rest2)
          | _ -> None)
       | _ -> None)
    | LParen :: TIf :: rest ->
      (match parse_tokens rest with
       | Some (e1, rest1) ->
         (match parse_tokens rest1 with
          | Some (e2, rest2) ->
            (match parse_tokens rest2 with
             | Some (e3, RParen :: rest3) -> Some (If (e1, e2, e3), rest3)
             | _ -> None)
          | _ -> None)
       | _ -> None)
    | _ -> None
  in
  match lex str with
  | Some tokens -> (match parse_tokens tokens with Some (expr, []) -> Some expr | _ -> None)
  | None -> None


let rec type_of e =
  match e with
  | Num _ -> Some TInt
  | Add (e1, e2) ->
    (match type_of e1, type_of e2 with
     | Some TInt, Some TInt -> Some TInt
     | _ -> None)
  | Lt (e1, e2) ->
    (match type_of e1, type_of e2 with
     | Some TInt, Some TInt -> Some TBool
     | _ -> None)
  | If (e1, e2, e3) ->
    (match type_of e1, type_of e2, type_of e3 with
     | Some TBool, Some t2, Some t3 when t2 = t3 -> Some t2
     | _ -> None)

type value =
  | VNum of int
  | VBool of bool

let rec eval e =
  match e with
  | Num n -> VNum n
  | Add (e1, e2) ->
    (match eval e1, eval e2 with
     | VNum n1, VNum n2 -> VNum (n1 + n2)
     | _ -> failwith "Undefined behavior: ill-typed expression")
  | Lt (e1, e2) ->
    (match eval e1, eval e2 with
     | VNum n1, VNum n2 -> VBool (n1 < n2)
     | _ -> failwith "Undefined behavior: ill-typed expression")
  | If (e1, e2, e3) ->
    (match eval e1 with
     | VBool true -> eval e2
     | VBool false -> eval e3
     | _ -> failwith "Undefined behavior: ill-typed expression")
