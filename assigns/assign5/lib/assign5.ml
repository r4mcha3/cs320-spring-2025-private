open Stdlib320

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

let rec eval (e : 'a expr) : (int, 'a error) result =
  match e.expr with
  | Num n -> Ok n
  | Op (op, left, right) ->
    let* l_val = eval left in
    let* r_val = eval right in
    match op with
    | Add -> Ok (l_val + r_val)
    | Sub -> Ok (l_val - r_val)
    | Mul -> Ok (l_val * r_val)
    | Div ->
      let* _ = guard (r_val = 0) { error = DivByZero; meta = e.meta } in
      Ok (l_val / r_val)
    | Pow ->
      let* _ = guard (r_val < 0) { error = NegExp; meta = e.meta } in
      Ok (int_of_float (float_of_int l_val ** float_of_int r_val))

exception ListTooShort
exception InvalidArg

let rec prefix k l =
  if k < 0 then raise InvalidArg
  else match (k, l) with
    | (0, _) -> []
    | (_, []) -> raise ListTooShort
    | (n, x :: xs) -> x :: prefix (n - 1) xs

type prefix_error =
  | ListTooShort
  | InvalidArg

let prefix_res k l =
  if k < 0 then Error InvalidArg
  else
    try Ok (prefix k l)
    with ListTooShort -> Error ListTooShort


module type DEQUEUE = sig
  type 'a t
  val empty: 'a t
  val push_front : 'a -> 'a t -> 'a t
  val pop_front : 'a t -> ('a * 'a t) option
  val push_back : 'a -> 'a t -> 'a t
  val pop_back : 'a t -> ('a * 'a t) option
  val to_list : 'a t -> 'a list
end

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
  let pop_front = function
    | [] -> None
    | x :: xs -> Some (x, xs)
  let push_back x l = l @ [x]
  let rec pop_back = function
    | [] -> None
    | [x] -> Some (x, [])
    | x :: xs ->
      match pop_back xs with
      | Some (y, ys) -> Some (y, x :: ys)
      | None -> None
  let to_list l = l
end

module DoubleListDequeue : DEQUEUE with type 'a t = 'a list * 'a list = struct
  type 'a t = 'a list * 'a list
  let empty = ([], [])
  let push_front x (f, b) = (x :: f, b)
  let push_back x (f, b) = (f, x :: b)
  let balance (f, b) =
    if List.length f >= List.length b then (f, b)
    else (f @ List.rev b, [])
  let pop_front = function
    | [], [] -> None
    | x :: xs, b -> Some (x, balance (xs, b))
    | [], b -> pop_front (balance ([], b))
  let pop_back = function
    | [], [] -> None
    | f, x :: xs -> Some (x, balance (f, xs))
    | f, [] -> pop_back (balance (f, []))
  let to_list (f, b) = f @ List.rev b
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