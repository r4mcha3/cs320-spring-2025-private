open Stdlib320
open Stdlib320.Ntree

type 'a tree =
  | Leaf
  | Node2 of 'a * 'a tree * 'a tree

let rec ntree_of_tree (t : 'a tree) : 'a ntree option =
  match t with
  | Leaf -> None
  | Node2 (x, left, right) ->
      let left_ntree = ntree_of_tree left in
      let right_ntree = ntree_of_tree right in
      let children =
        (match left_ntree with Some nt -> [nt] | None -> []) @
        (match right_ntree with Some nt -> [nt] | None -> [])
      in
      Some (Node (x, children))

let fib3_tail (a, b, c) n =
  let rec aux i x y z =
    if i = n then x
    else aux (i + 1) y z (x + y + z)
  in
  match n with
  | 0 -> a
  | 1 -> b
  | 2 -> c
  | _ -> aux 3 a b c

  let split_on_char sep s =
    let rec aux i j acc =
      if i >= String.length s then List.rev (String.sub s j (i - j) :: acc)
      else if s.[i] = sep then
        aux (i + 1) (i + 1) (String.sub s j (i - j) :: acc)
      else
        aux (i + 1) j acc
    in
    aux 0 0 []  

let file_tree root paths =
  let rec insert_path path_parts children =
    match path_parts with
    | [] -> children
    | part :: rest ->
        let child =
          match List.find_opt (fun (Node (name, _)) -> name = part) children with
          | Some (Node (_, subchildren)) ->
              Node (part, insert_path rest subchildren)
          | None ->
              Node (part, insert_path rest [])
        in
        child :: List.filter (fun (Node (name, _)) -> name <> part) children
  in
  let root_children =
    List.fold_left (fun acc path ->
      let parts = split_on_char '/' path in
      insert_path parts acc
    ) [] paths
  in
  Node (root, root_children)

type expr =
  | Num of int
  | Var of string
  | Add of expr * expr
  | Mul of expr * expr

let rec subst e1 x e2 =
  match e2 with
  | Num _ -> e2
  | Var y -> if y = x then e1 else e2
  | Add (left, right) -> Add (subst e1 x left, subst e1 x right)
  | Mul (left, right) -> Mul (subst e1 x left, subst e1 x right)

let rec string_of_expr e =
  match e with
  | Num n -> string_of_int n
  | Var x -> x
  | Add (e1, e2) ->
      "(" ^ string_of_expr e1 ^ " + " ^ string_of_expr e2 ^ ")"
  | Mul (e1, e2) ->
      "(" ^ string_of_expr e1 ^ " * " ^ string_of_expr e2 ^ ")"
