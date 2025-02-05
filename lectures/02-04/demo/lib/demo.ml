open Stdlib320

let rec step a b =
  if a = b
  then [a]
  else if a < b
  then a :: step (a + 1) b
  else a :: step (a - 1) b

let fill_in_steps (a, b, c) =
  let left = step a b in
  let right = step b c in
  match right with
  | [] -> assert false
  | _ :: right_tail -> left @ right_tail

let reverse l =
  let rec go acc l =
    match l with
    | [] -> acc
    | head :: tail ->
      go (head :: acc) tail
  in go [] l

type intlist =
  | Nil
  | Cons of int * intlist

let rec snoc l x =
  match l with
  | Nil -> Cons(x, Nil)
  | Cons (head, tail) -> Cons (head, snoc tail x)

type expr =
  | Val of int
  | Add of expr * expr
  | Mul of expr * expr

let evaluate e =
  let rec go e =
    match e with
    | Val n -> n
    | Add (e1, e2) -> go e1 + go e2
    | Mul (e1, e2) -> go e1 * go e2
  in go e

(* 3 + (2 * 4 + 14) *)
let _example = Add (Val 3, Add (Mul (Val 2, Val 4), Val 14))

type 'a tree =
  | Leaf
  | Node of 'a * 'a tree * 'a tree

let _example =
  Node (1,
    Node (2, Leaf, Leaf),
    Node (3, Leaf, Leaf))

let rec size t =
  match t with
  | Leaf -> 0
  | Node (_, left, right) ->
  1 + size left + size right
