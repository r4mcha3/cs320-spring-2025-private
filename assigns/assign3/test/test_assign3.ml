let str_sort = List.sort String.compare

open Stdlib320
open Assign3

let rec files_of_tree (Node (root, children)) =
  let rec expand children =
    match children with
    | [] -> []
    | c :: cs -> files_of_tree c @ expand cs
  in
  let rec add_root fs =
   match fs with
    | [] -> []
    | f :: fs -> (root ^ "/" ^ f) :: add_root fs
  in
  if children = []
  then [root]
  else add_root (expand children)

let _ = files_of_tree

let testing = true (* switch this flag to turn off testing globally *)

let run cases b = if b then cases () else []

let ntree_of_tree_tests () =
  let t1 = Node2 ((), Node2 ((), Leaf, Leaf), Node2 ((), Node2 ((), Leaf, Leaf), Leaf)) in
  let t2 = Node (() , [Node ((), []); Node ((), [Node ((), [])])]) in
  [
    assert (ntree_of_tree Leaf = None);
    assert (ntree_of_tree t1 = Some t2)
  ]

let fib3_tail_tests () =
  [
    assert (fib3_tail (1, 1, 1) 10 = 193);
    assert (fib3_tail (0, 0, 0) 100_000_000 = 0);
  ]

let file_tree_tests () =
  let big_example =
    [
      "assign2/test/test_assign2.ml";
      "assign2/test/dune";
      "assign2/bin/dune";
      "assign2/bin/main.ml";
      "assign2/assign2.opam";
      "assign2/dune-project";
      "assign2/lib/dune";
      "assign0/test/dune";
      "assign0/test/test_assign0.ml";
      "assign0/dune-project";
      "assign0/lib/dune";
      "assign0/assign0.opam";
      "assign1/test/dune";
      "assign1/test/test_assign1.ml";
      "assign1/bin/dune";
      "assign1/bin/main.ml";
      "assign1/assign1.opam";
      "assign1/dune-project";
      "assign1/lib/dune";
    ]
  in
  [
    assert (file_tree "root" [] = Node ("root", []));
    assert (file_tree "root" ["file"] = Node ("root", [Node ("file", [])]));
    assert (file_tree "root" ["file"; "file"] = Node ("root", [Node ("file", [])]));
    assert (file_tree "" ["file"; "dir1/file"; "dir1/dir2/"]
            = Node ("" , [ Node ("file", []) ; Node ("dir1", [Node ("file", []); Node ("dir2", [Node ("", [])])])]));
    assert (str_sort (files_of_tree (file_tree "." big_example))
            = List.map (fun s -> "./" ^ s) (str_sort big_example));
  ]

let subst_tests () =
  [
    assert (subst (Num 2) "x" (Var "x") = Num 2);
    assert (subst (Num 4) "x" (Add (Var "x", Num 2)) = Add (Num 4, Num 2));
    assert (subst (Num 4) "x" (Add (Var "y", Var "z")) = Add (Var "y", Var "z"));
    assert (subst (Add (Var "x", Var "y")) "z" (Add (Var "y", Var "z")) = Add (Var "y", Add (Var "x", Var "y")));
  ]

let string_of_expr_tests () =
  let s = string_of_expr in
  [
    assert (s (Add (Num 2, Num 3)) = "2 + 3");
    assert (s (Add (Num (-2), Num 3)) = "-2 + 3");
    assert (s (Add (Num 2, Num (-3))) = "2 + (-3)");
    assert (s (Add (Num 2, (Mul (Num (-2), Var "x")))) = "2 + (-2) * x");
    assert (s (Mul (Num 2, (Add (Num (-2), Var "x")))) = "2 * (-2 + x)");
    assert (s (Add (Num 2, (Add (Num (-2), Var "x")))) = "2 + (-2) + x");
    assert (s (Mul (Num (-2), (Mul (Num (-2), Var "x")))) = "-2 * (-2) * x");
    assert (s (Mul (Num (-3), Mul (Add (Num (-2), Num (-2)), Var "x"))) = "-3 * (-2 + (-2)) * x");
  ]

let _run_tests : unit list list =
  if not testing then [] else
    [
      run ntree_of_tree_tests true;
      run fib3_tail_tests true;
      run file_tree_tests true;
      run subst_tests true;
      run string_of_expr_tests true;
    ]
