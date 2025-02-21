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
      let filtered_children = List.filter_map (tree_filter p) children in
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
    [(start, { num = 1; denom = 1 })]  (* Base case: 100% probability at start *)
  else
    let prev_distr = random_walk walk start (num_steps - 1) in
    let combine_prob (distr : distr) : distr =
      let tbl = Hashtbl.create 10 in
      List.iter
        (fun (v, { num; denom }) ->
           let neighbors = walk v in
           let num_neighbors = List.length neighbors in
           let new_prob = { num; denom = denom * num_neighbors } in
           List.iter
             (fun n ->
                Hashtbl.replace tbl n
                  (match Hashtbl.find_opt tbl n with
                   | Some { num = num'; denom = denom' } ->
                       let common_denom = denom' * new_prob.denom in
                       let updated_num =
                         (num' * new_prob.denom) + (new_prob.num * denom')
                       in
                       { num = updated_num; denom = common_denom }
                   | None -> new_prob))
             neighbors)
        distr;
      (* Convert hashtable back to sorted list and reduce fractions *)
      Hashtbl.fold (fun k v acc -> (k, v) :: acc) tbl []
      |> List.sort (fun (a, _) (b, _) -> compare a b)
    in
    combine_prob prev_distr
