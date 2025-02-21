open Stdlib320

let curry (f : ('a * 'b) -> 'c) : 'a -> 'b -> 'c = fun x y -> f (x, y)
let uncurry (f : 'a -> 'b -> 'c) : ('a * 'b) -> 'c = fun (x, y) -> f x y

let rec split_list (l : ('a * 'b) list) : 'a list * 'b list =
  match l with
  | [] -> ([], [])
  | (x, y) :: xs ->
      let (lefts, rights) = split_list xs in
      (x :: lefts, y :: rights)

let rec split_tree (t : ('a * 'b) ntree) : 'a ntree * 'b ntree =
  match t with
  | Node ((x, y), children) ->
      let left_children, right_children =
        List.fold_right
          (fun child (l_acc, r_acc) ->
              let l_child, r_child = split_tree child in
              (l_child :: l_acc, r_child :: r_acc))
          children
          ([], [])
      in
      (Node (x, left_children), Node (y, right_children))
      

let rec filter_map (f : 'a -> 'b option) (l : 'a list) : 'b list =
  match l with
  | [] -> []
  | x :: xs -> (
      match f x with
      | Some y -> y :: filter_map f xs
      | None -> filter_map f xs
    )

let rec tree_filter (p : 'a -> bool) (t : 'a ntree) : 'a ntree option =
  match t with
  | Node (x, children) ->
      let rec filter_map f lst =
        match lst with
        | [] -> []
        | h :: t -> (
            match f h with
            | Some v -> v :: filter_map f t
            | None -> filter_map f t
          )
      in
      let filtered_children = filter_map (tree_filter p) children in
      if p x then
        Some (Node (x, filtered_children))
      else
        match filtered_children with
        | [] -> None
        | Node (lx, lchildren) :: rest ->
            Some (Node (lx, lchildren @ rest))

type rat = {
    num : int;
    denom : int;
  }

type distr = (int * rat) list

let rec random_walk (walk : int -> int list) (start : int) (num_steps : int) : distr =
  if num_steps = 0 then
    [(start, { num = 1; denom = 1 })] 
  else
    let prev_distr = random_walk walk start (num_steps - 1) in
    let rec merge_prob v prob acc =
      match acc with
      | [] -> [(v, prob)]
      | (w, p) :: rest ->
          if v = w then
            let common_denom = p.denom * prob.denom in
            let new_num = (p.num * prob.denom) + (prob.num * p.denom) in
            (w, { num = new_num; denom = common_denom }) :: rest
          else
            (w, p) :: merge_prob v prob rest
    in
    let rec process_distribution distr acc =
      match distr with
      | [] -> acc
      | (v, { num; denom }) :: rest ->
          let neighbors = walk v in
          let num_neighbors = List.length neighbors in
          let new_prob = { num; denom = denom * num_neighbors } in
          let updated_acc =
            List.fold_left (fun acc n -> merge_prob n new_prob acc) acc neighbors
          in
          process_distribution rest updated_acc
    in
    let compare_int (a : int) (b : int) : int =
      if a < b then -1 else if a > b then 1 else 0
    in
    let final_distr = process_distribution prev_distr [] in
    List.sort (fun (a, _) (b, _) -> compare_int a b) final_distr
