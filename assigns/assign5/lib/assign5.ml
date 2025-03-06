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

let eval (e : 'a expr) : (int, 'a error) result =
  assert false

exception ListTooShort
exception InvalidArg

let prefix (k : int) (l : 'a list) : 'a list = assert false

type prefix_error =
  | ListTooShort
  | InvalidArg

let prefix_res (k : int) (l : 'a list) : ('a list, prefix_error) result =
  assert false

module type DEQUEUE = sig
  type 'a t
  val empty: 'a t
  val push_front : 'a -> 'a t -> 'a t
  val pop_front : 'a t -> ('a * 'a t) option
  val push_back : 'a -> 'a t -> 'a t
  val pop_back : 'a t -> ('a * 'a t) option
  val to_list : 'a t -> 'a list
end

module ListDequeue = struct
  type 'a t = 'a list
  let empty = assert false
  let push_front x l = assert false
  let pop_front l = assert false
  let push_back x l = assert false
  let pop_back l = assert false
  let to_list l = assert false
end

module DoubleListDequeue = struct
  type 'a t = 'a list * 'a list
  let empty = assert false
  let push_front x l = assert false
  let pop_front l = assert false
  let push_back x l = assert false
  let pop_back l = assert false
  let to_list l = assert false
end

module StringMap = Map.Make(String)
module IntMap = Map.Make(Int)
module StringSet = Set.Make(String)

let flip_keys_and_values (m : int StringMap.t) : StringSet.t IntMap.t =
  assert false
