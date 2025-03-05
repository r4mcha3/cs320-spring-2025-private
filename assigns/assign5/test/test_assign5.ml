open Assign5
open OUnit2

module EvalExamples = struct
  let e m ex = {expr=ex;meta=m}
  let add m e1 e2 = e m (Op (Add, e1, e2))
  let div m e1 e2 = e m (Op (Div, e1, e2))
  let pow m e1 e2 = e m (Op (Pow, e1, e2))
  let num m n = e m (Num n)
  let err k m = Error {error=k;meta=m}
  let e1 = add 0 (num 0 1) (pow 2 (num 3 2) (num 4 3))
  let e2 = add 0 (num 0 10) (pow 2 (num 3 2) (num 4 0))
  let e3 = add 0 (pow 1 (num 2 2) (num 3 (-1))) (num 4 1)
  let e3_err = err NegExp 1
  let e4 = add 0 (num 1 1) (div 2 (num 3 2) (num 4 0))
  let e4_err = err DivByZero 2
end

let test_eval =
  let open EvalExamples in
  "basic eval tests" >:::
    [
      "1 + 2 ^ 3" >:: (fun _ -> assert_equal (Ok 9) (eval e1));
      "10 + 2 ^ 0" >:: (fun _ -> assert_equal (Ok 11) (eval e2));
      "2 ^ (-1) + 1" >:: (fun _ -> assert_equal e3_err (eval e3));
      "1 + 2 / 0" >:: (fun _ -> assert_equal e4_err (eval e4));
    ]

let test_prefix =
  "basic prefix tests" >:::
    [
      "success" >:: (fun _ -> assert_equal [1;2;3] (prefix 3 [1;2;3;4;5;6]));
      "list too short" >:: (fun _ -> assert_raises ListTooShort (fun _ -> prefix 5 [1;2;3]));
      "invalid arg" >:: (fun _ -> assert_raises InvalidArg (fun _ -> prefix (-3) [1;2;3]));
      "success res" >:: (fun _ -> assert_equal (Ok [1;2;3]) (prefix_res 3 [1;2;3;4;5;6]));
      "list too short res" >:: (fun _ -> assert_equal (Error ListTooShort) (prefix_res 5 [1;2;3]));
      "invalid arg res" >:: (fun _ -> assert_equal (Error InvalidArg) (prefix_res (-3) [1;2;3]));
    ]

let test_dequeue =
  let module L = ListDequeue in
  let module D = DoubleListDequeue in
  "basic dequeue tests" >:::
    [
      "empty ld" >:: (fun _ -> assert_equal [] L.empty);
      "push_front ld" >:: (fun _ -> assert_equal [1;2;3] (L.push_front 1 [2;3]));
      "pop_front ld" >:: (fun _ -> assert_equal (Some (1, [2;3])) (L.pop_front [1;2;3]));
      "pop_front empty ld" >:: (fun _ -> assert_equal None (L.pop_front []));
      "push_back ld" >:: (fun _ -> assert_equal [1;2;3] (L.push_back 3 [1;2]));
      "pop_back ld" >:: (fun _ -> assert_equal (Some (3, [1;2])) (L.pop_back [1;2;3]));
      "pop_back empty ld" >:: (fun _ -> assert_equal None (L.pop_back []));

      "empty dld" >:: (fun _ -> assert_equal ([], []) D.empty);
      "push_front dld" >:: (fun _ -> assert_equal ([1;2;3], [5;4]) (D.push_front 1 ([2;3], [5;4])));
      "pop_front dld" >:: (fun _ -> assert_equal (Some (1, ([2;3], [5;4]))) (D.pop_front ([1;2;3], [5;4])));
      "push_back dld" >:: (fun _ -> assert_equal ([1;2;3], [6;5;4]) (D.push_back 6 ([1;2;3], [5;4])));
      "pop_back balance" >:: (fun _ -> assert_equal (Some (6, ([1;2;3], [5;4]))) (D.pop_back ([1;2;3;4;5;6], [])));
      "to list dld" >:: (fun _ -> assert_equal [1;2;3;4;5;6] (D.to_list ([1;2;3], [6;5;4])));
    ]

let test_flip =
  "basic flip_keys_and_values" >:::
    [
      "basic case" >:: (fun _ ->
        assert_equal
          (IntMap.of_list
             [
               (1, StringSet.of_list ["a"; "c"]);
               (2, StringSet.of_list ["b"; "e"]);
               (3, StringSet.singleton "d");
             ]
          )
          (flip_keys_and_values
             (StringMap.of_list
                [("a", 1); ("b", 2); ("c", 1); ("d", 3); ("e", 2)])));
    ]

let tests =
  "Assignment 5 test suite" >:::
    [
      test_eval;
      test_prefix;
      test_dequeue;
      test_flip;
    ]

let _ = run_test_tt_main tests
