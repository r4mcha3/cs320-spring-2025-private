type op = Add | Sub | Mul | Div | Pow

type 'a expr =
  {
    expr : 'a _expr;
    meta : 'a
  }
and 'a _expr =
  | Num of int
  | Op of op * 'a expr * 'a expr

type error_kind =
  | DivByZero
  | NegExp

type 'a error =
  {
    error: error_kind;
    meta : 'a;
  }

let guard b error = if b then Error error else Ok ()

let ( let* ) = Result.bind

let eval (e : 'a expr) : (int, 'a error) result =
  let rec eval_expr e =
    match e.expr with
    | Num n -> Ok n
    | Op (op, e1, e2) ->
      let* v1 = eval_expr e1 in
      let* v2 = eval_expr e2 in
      match op with
      | Add -> Ok (v1 + v2)
      | Sub -> Ok (v1 - v2)
      | Mul -> Ok (v1 * v2)
      | Div -> 
        let* _ = guard (v2 = 0) { error = DivByZero; meta = e2.meta } in
        Ok (v1 / v2)
      | Pow -> 
        let* _ = guard (v2 < 0) { error = NegExp; meta = e2.meta } in
        Ok (int_of_float (float_of_int v1 ** float_of_int v2))
  in
  eval_expr e

exception ListTooShort
exception InvalidArg

let prefix (k : int) (l : 'a list) : 'a list =
  if k < 0 then raise InvalidArg
  else if List.length l < k then raise ListTooShort
  else List.fold_left (fun (acc, n) x -> if n < k then (x :: acc, n + 1) else (acc, n)) ([], 0) l |> fst |> List.rev

type prefix_error =
  | ListTooShort
  | InvalidArg

let prefix_res (k : int) (l : 'a list) : ('a list, prefix_error) result =
  try Ok (prefix k l) with
  | ListTooShort -> Error ListTooShort
  | InvalidArg -> Error InvalidArg


module type DEQUEUE = sig
  type 'a t
  val empty: 'a t
  val push_front : 'a -> 'a t -> 'a t
  val pop_front : 'a t -> ('a * 'a t) option
  val push_back : 'a -> 'a t -> 'a t
  val pop_back : 'a t -> ('a * 'a t) option
  val to_list : 'a t -> 'a list
end

module ListDequeue : DEQUEUE with type 'a t = 'a list = struct
  type 'a t = 'a list
  let empty = []
  let push_front x l = x :: l
  let rec pop_front = function
    | [] -> None
    | x :: xs -> Some (x, xs)
  let push_back x l = l @ [x]
  let rec pop_back = function
    | [] -> None
    | l -> Some (List.hd (List.rev l), List.rev (List.tl (List.rev l)))
  let to_list l = l
end

module DoubleListDequeue : DEQUEUE with type 'a t = 'a list * 'a list = struct
  type 'a t = 'a list * 'a list
  let empty = ([], [])
  let push_front x (front, back) = (x :: front, back)
  let push_back x (front, back) = (front, x :: back)
  
  let balance (front, back) =
    let len_f = List.length front in
    let len_b = List.length back in
    if len_f >= len_b then (front, back)
    else (front @ List.rev back, [])

  let rec pop_front = function
  | [], [] -> None
  | x :: xs, back -> Some (x, balance (xs, back))
  | [], back -> 
    let balanced = balance ([], back) in
    pop_front balanced 

  and pop_back = function
  | [], [] -> None
  | front, x :: xs -> Some (x, balance (front, xs))
  | front, [] -> 
    let balanced = balance (front, []) in
    pop_back balanced 

  
  let to_list (front, back) = front @ List.rev back
end


module StringMap = Map.Make(String)
module IntMap = Map.Make(Int)
module StringSet = Set.Make(String)

let flip_keys_and_values (m : int StringMap.t) : StringSet.t IntMap.t =
  StringMap.fold (fun key value acc ->
    let existing_set = match IntMap.find_opt value acc with
      | Some s -> s
      | None -> StringSet.empty
    in
    IntMap.add value (StringSet.add key existing_set) acc
  ) m IntMap.empty
