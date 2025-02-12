
let accum
  (start : 'a)
  (op : int -> 'a -> 'a) : int -> 'a =
  let rec go (n : int) : 'a =
    match n with
    | 0 -> start
    | n -> op n (go (n - 1))
  in go

let sum = accum 0 (+)
let fact = accum 1 ( * )

let rec insert lte x l =
  match l with
  | [] -> [x]
  | y :: ys ->
    if lte x y
    then x :: y :: ys
    else y :: insert lte x ys

let rec sort lte l =
  match l with
  | [] -> []
  | x :: xs -> insert lte x (sort lte xs)

let sort_standard l = sort (<=) l
let sort_reverse l = sort (>=) l
let sort_second l =
  sort
    (fun (_, x) (_, y) -> x <= y)
    l

let check_and_transform check transform l =
  let rec go l =
    match l with
    | [] -> []
    | x :: tail ->
      if check x
      then transform x :: go tail
      else go tail
  in go l

let get key l =
  l
  |> List.filter (fun (k, _) -> k = key)
  |> List.map (fun (_, v) -> v)
(*  List.map (fun (_, v) -> v) (List.filter (fun (k, v) -> k = key) l) *)
(*  check_and_transform
    (fun (k, _) -> k = key)
    (fun v -> v)
    (List.map (fun (_, v) -> v) l)
    *)

let negative l = List.filter (fun x -> x < 0) l
(*  check_and_transform
    (fun n -> n < 0)
    (fun n -> n)
    l
    *)

let sum _l = assert false
let norm (v: float list) =
  v
  |> List.map (fun x -> x *. x)
  |> sum
  |> sqrt

let primes _n =
  let rec go acc l =
    match l with
    | [] -> acc
    | x :: xs -> go (x :: acc) (List.filter (fun i -> i mod x <> 0) xs)
  in go (assert false)
