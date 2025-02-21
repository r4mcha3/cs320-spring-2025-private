open Assign4

let testing = true (* switch this flag to turn off testing globally *)

let run cases b = if b then cases () else []

let hd l =
  match l with
  | [] -> None
  | h :: _ -> Some h

let tree_ex =
  let open Stdlib320 in
  Node ((1, 2), [
          Node ((3, 4), []);
          Node ((5, 6), []);
    ])
let tree_ex_l =
  let open Stdlib320 in
  Node (1, [
          Node (3, []);
          Node (5, []);
    ])

let tree_ex_r =
  let open Stdlib320 in
  Node (2, [
          Node (4, []);
          Node (6, []);
    ])

let basic_tests () =
  [
    assert (curry (fun (x, y) -> x + y) 2 3 = 5);
    assert (uncurry (fun x y -> x + y) (2, 3) = 5);
    assert (filter_map hd [[1;2];[3;4];[];[5];[];[];[6;7]] = [1;3;5;6]);
    assert (split_list [(1, 2); (3, 4); (5, 6)] = ([1;3;5], [2;4;6]));
    assert (split_tree tree_ex = (tree_ex_l, tree_ex_r));
  ]

let tree_filter_tests () =
  let open Stdlib320 in
  [
    assert (tree_filter (fun _ -> false) tree_ex_l = None);
    assert (tree_filter (fun x -> x = 1) tree_ex_l = Some (Node (1, [])));
    assert (tree_filter (fun x -> x <> 1) tree_ex_l = Some (Node (3, [Node (5, [])])));
    assert (tree_filter (fun x -> x = 5) tree_ex_l = Some (Node (5, [])));
    assert (tree_filter (fun x -> x <> 5) tree_ex_l = Some (Node (1, [Node (3, [])])));
    assert (tree_filter (fun x -> x = 3) tree_ex_l = Some (Node (3, [])));
    assert (tree_filter (fun x -> x <> 3) tree_ex_l = Some (Node (1, [Node (5, [])])));
  ]

let random_walk_tests () =
  let drunkard n = [n + 1; n - 1] in
  let open Stdlib320 in
  [
    assert (random_walk drunkard 0 0 = [(0, {num=1;denom=1})]);
    assert (random_walk drunkard 0 1 = [(-1, {num=1;denom=2}); (1, {num=1;denom=2})]);
    assert (random_walk drunkard 0 2
            = [(-2, {num=1;denom=4}); (0, {num=1;denom=2}); (2, {num=1;denom=4})]);
  ]

let _run_tests : unit list list =
  if not testing then [] else
    [
      run basic_tests true;
      run tree_filter_tests true;
      run random_walk_tests true;
    ]
