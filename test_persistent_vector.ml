(* Tests for Persistent Vector *)

#use "persistent_vector.ml";;

let tests_run = ref 0
let tests_passed = ref 0

let test name f =
  incr tests_run;
  try
    f ();
    incr tests_passed;
    Printf.printf "  PASS: %s\n" name
  with e ->
    Printf.printf "  FAIL: %s — %s\n" name (Printexc.to_string e)

let assert_eq a b msg =
  if a <> b then failwith (Printf.sprintf "%s: expected %s, got %s" msg
    (string_of_int b) (string_of_int a))

let assert_true b msg = if not b then failwith msg

let () =
  print_endline "=== Persistent Vector Tests ===";
  print_newline ();

  (* --- Empty vector --- *)
  print_endline "--- Empty vector ---";

  test "empty has length 0" (fun () ->
    assert_eq (length empty) 0 "length"
  );

  test "get on empty raises" (fun () ->
    let raised = ref false in
    (try ignore (get empty 0) with Invalid_argument _ -> raised := true);
    assert_true !raised "should raise"
  );

  test "pop_back on empty raises" (fun () ->
    let raised = ref false in
    (try ignore (pop_back empty) with Invalid_argument _ -> raised := true);
    assert_true !raised "should raise"
  );

  test "to_list of empty is []" (fun () ->
    assert_true (to_list empty = []) "empty to_list"
  );

  test "to_array of empty is [||]" (fun () ->
    assert_true (to_array empty = [||]) "empty to_array"
  );

  (* --- Single element --- *)
  print_endline "";
  print_endline "--- Single element ---";

  test "push one element" (fun () ->
    let v = push_back empty 42 in
    assert_eq (length v) 1 "length";
    assert_eq (get v 0) 42 "get 0"
  );

  test "pop single element" (fun () ->
    let v = push_back empty 42 in
    let (v', x) = pop_back v in
    assert_eq x 42 "popped value";
    assert_eq (length v') 0 "remaining length"
  );

  test "set single element" (fun () ->
    let v = push_back empty 10 in
    let v' = set v 0 99 in
    assert_eq (get v 0) 10 "original unchanged";
    assert_eq (get v' 0) 99 "updated"
  );

  (* --- Small vector --- *)
  print_endline "";
  print_endline "--- Small vector (5 elements) ---";

  let small = of_list [10; 20; 30; 40; 50] in

  test "length is 5" (fun () ->
    assert_eq (length small) 5 "length"
  );

  test "get all elements" (fun () ->
    assert_eq (get small 0) 10 "idx 0";
    assert_eq (get small 1) 20 "idx 1";
    assert_eq (get small 2) 30 "idx 2";
    assert_eq (get small 3) 40 "idx 3";
    assert_eq (get small 4) 50 "idx 4"
  );

  test "set middle element" (fun () ->
    let v = set small 2 999 in
    assert_eq (get v 2) 999 "updated";
    assert_eq (get small 2) 30 "original"
  );

  test "out of bounds get raises" (fun () ->
    let raised = ref false in
    (try ignore (get small 5) with Invalid_argument _ -> raised := true);
    assert_true !raised "should raise"
  );

  test "negative index raises" (fun () ->
    let raised = ref false in
    (try ignore (get small (-1)) with Invalid_argument _ -> raised := true);
    assert_true !raised "should raise"
  );

  test "out of bounds set raises" (fun () ->
    let raised = ref false in
    (try ignore (set small 5 0) with Invalid_argument _ -> raised := true);
    assert_true !raised "should raise"
  );

  (* --- to_list / of_list roundtrip --- *)
  print_endline "";
  print_endline "--- Conversions ---";

  test "of_list / to_list roundtrip" (fun () ->
    let lst = [1; 2; 3; 4; 5] in
    assert_true (to_list (of_list lst) = lst) "roundtrip"
  );

  test "of_array / to_array roundtrip" (fun () ->
    let arr = [|10; 20; 30|] in
    assert_true (to_array (of_array arr) = arr) "roundtrip"
  );

  (* --- Persistence --- *)
  print_endline "";
  print_endline "--- Persistence (structural sharing) ---";

  test "set does not mutate original" (fun () ->
    let orig = of_list [1; 2; 3] in
    let _ = set orig 0 99 in
    assert_eq (get orig 0) 1 "original"
  );

  test "push_back does not mutate original" (fun () ->
    let orig = of_list [1; 2; 3] in
    let _ = push_back orig 4 in
    assert_eq (length orig) 3 "original length"
  );

  test "pop_back does not mutate original" (fun () ->
    let orig = of_list [1; 2; 3] in
    let _ = pop_back orig in
    assert_eq (length orig) 3 "original length";
    assert_eq (get orig 2) 3 "original last"
  );

  test "multiple versions coexist" (fun () ->
    let v0 = of_list [10; 20; 30] in
    let v1 = set v0 0 99 in
    let v2 = push_back v0 40 in
    let (v3, _) = pop_back v0 in
    assert_true (to_list v0 = [10; 20; 30]) "v0";
    assert_true (to_list v1 = [99; 20; 30]) "v1";
    assert_true (to_list v2 = [10; 20; 30; 40]) "v2";
    assert_true (to_list v3 = [10; 20]) "v3"
  );

  (* --- Higher-order operations --- *)
  print_endline "";
  print_endline "--- Higher-order operations ---";

  test "map doubles elements" (fun () ->
    let v = map (fun x -> x * 2) (of_list [1; 2; 3]) in
    assert_true (to_list v = [2; 4; 6]) "doubled"
  );

  test "fold_left sums" (fun () ->
    assert_eq (fold_left ( + ) 0 (of_list [1; 2; 3; 4; 5])) 15 "sum"
  );

  test "fold_right builds list" (fun () ->
    let lst = fold_right (fun x acc -> x :: acc) (of_list [1; 2; 3]) [] in
    assert_true (lst = [1; 2; 3]) "fold_right"
  );

  test "filter evens" (fun () ->
    let v = filter (fun x -> x mod 2 = 0) (of_list [1; 2; 3; 4; 5; 6]) in
    assert_true (to_list v = [2; 4; 6]) "filtered"
  );

  test "exists finds element" (fun () ->
    assert_true (exists (fun x -> x > 3) (of_list [1; 2; 3; 4; 5])) "exists > 3";
    assert_true (not (exists (fun x -> x > 10) (of_list [1; 2; 3]))) "not exists > 10"
  );

  test "for_all checks all" (fun () ->
    assert_true (for_all (fun x -> x > 0) (of_list [1; 2; 3])) "all > 0";
    assert_true (not (for_all (fun x -> x > 2) (of_list [1; 2; 3]))) "not all > 2"
  );

  test "find_opt" (fun () ->
    assert_true (find_opt (fun x -> x mod 2 = 0) (of_list [1; 3; 4; 5]) = Some 4) "found 4";
    assert_true (find_opt (fun x -> x > 10) (of_list [1; 2; 3]) = None) "not found"
  );

  test "iter visits all elements" (fun () ->
    let acc = ref 0 in
    iter (fun x -> acc := !acc + x) (of_list [1; 2; 3; 4]);
    assert_eq !acc 10 "sum via iter"
  );

  test "iteri provides correct indices" (fun () ->
    let pairs = ref [] in
    iteri (fun i x -> pairs := (i, x) :: !pairs) (of_list [10; 20; 30]);
    let sorted = List.rev !pairs in
    assert_true (sorted = [(0, 10); (1, 20); (2, 30)]) "pairs"
  );

  (* --- Slicing --- *)
  print_endline "";
  print_endline "--- Slicing ---";

  test "sub extracts range" (fun () ->
    let v = of_list [10; 20; 30; 40; 50] in
    assert_true (to_list (sub v 1 4) = [20; 30; 40]) "sub [1,4)"
  );

  test "sub empty range" (fun () ->
    let v = of_list [1; 2; 3] in
    assert_eq (length (sub v 1 1)) 0 "empty sub"
  );

  test "sub invalid range raises" (fun () ->
    let raised = ref false in
    (try ignore (sub (of_list [1; 2]) 2 1) with Invalid_argument _ -> raised := true);
    assert_true !raised "should raise"
  );

  test "append two vectors" (fun () ->
    let v = append (of_list [1; 2]) (of_list [3; 4; 5]) in
    assert_true (to_list v = [1; 2; 3; 4; 5]) "appended"
  );

  test "append with empty" (fun () ->
    let v = of_list [1; 2; 3] in
    assert_true (to_list (append v empty) = [1; 2; 3]) "append empty right";
    assert_true (to_list (append empty v) = [1; 2; 3]) "append empty left"
  );

  test "rev" (fun () ->
    assert_true (to_list (rev (of_list [1; 2; 3; 4])) = [4; 3; 2; 1]) "reversed"
  );

  (* --- Equality --- *)
  print_endline "";
  print_endline "--- Equality ---";

  test "equal vectors" (fun () ->
    assert_true (equal ( = ) (of_list [1; 2; 3]) (of_list [1; 2; 3])) "equal"
  );

  test "unequal vectors (different values)" (fun () ->
    assert_true (not (equal ( = ) (of_list [1; 2; 3]) (of_list [1; 2; 4]))) "diff values"
  );

  test "unequal vectors (different lengths)" (fun () ->
    assert_true (not (equal ( = ) (of_list [1; 2]) (of_list [1; 2; 3]))) "diff lengths"
  );

  test "empty vectors are equal" (fun () ->
    assert_true (equal ( = ) empty empty) "both empty"
  );

  (* --- Transient --- *)
  print_endline "";
  print_endline "--- Transient (batch) ---";

  test "transient build and freeze" (fun () ->
    let t = transient_of empty in
    for i = 0 to 9 do transient_push t i done;
    let v = persistent_of t in
    assert_eq (length v) 10 "length";
    for i = 0 to 9 do assert_eq (get v i) i ("get " ^ string_of_int i) done
  );

  test "frozen transient rejects push" (fun () ->
    let t = transient_of empty in
    transient_push t 1;
    ignore (persistent_of t);
    let raised = ref false in
    (try transient_push t 2 with Failure _ -> raised := true);
    assert_true !raised "should raise"
  );

  test "of_list_fast matches of_list" (fun () ->
    let lst = List.init 100 (fun i -> i) in
    let v1 = of_list lst in
    let v2 = of_list_fast lst in
    assert_true (equal ( = ) v1 v2) "fast = normal"
  );

  (* --- Large vector --- *)
  print_endline "";
  print_endline "--- Large vector (10,000 elements) ---";

  test "build and access 10k elements" (fun () ->
    let v = of_list_fast (List.init 10000 (fun i -> i)) in
    assert_eq (length v) 10000 "length";
    assert_eq (get v 0) 0 "first";
    assert_eq (get v 9999) 9999 "last";
    assert_eq (get v 5000) 5000 "middle"
  );

  test "set on large vector" (fun () ->
    let v = of_list_fast (List.init 10000 (fun i -> i)) in
    let v' = set v 7777 (-1) in
    assert_eq (get v 7777) 7777 "original";
    assert_eq (get v' 7777) (-1) "updated"
  );

  test "pop_back on large vector" (fun () ->
    let v = of_list_fast (List.init 100 (fun i -> i)) in
    let (v', x) = pop_back v in
    assert_eq x 99 "popped";
    assert_eq (length v') 99 "remaining"
  );

  test "pop all elements from vector" (fun () ->
    let v = ref (of_list [1; 2; 3; 4; 5]) in
    let collected = ref [] in
    while length !v > 0 do
      let (v', x) = pop_back !v in
      collected := x :: !collected;
      v := v'
    done;
    assert_true (!collected = [1; 2; 3; 4; 5]) "all popped in order"
  );

  (* --- Polymorphic --- *)
  print_endline "";
  print_endline "--- Polymorphic ---";

  test "string vector" (fun () ->
    let v = of_list ["a"; "b"; "c"] in
    assert_true (get v 1 = "b") "string get";
    let v' = map String.uppercase_ascii v in
    assert_true (to_list v' = ["A"; "B"; "C"]) "string map"
  );

  test "float vector" (fun () ->
    let v = of_list [1.0; 2.5; 3.7] in
    assert_true (abs_float (get v 1 -. 2.5) < 0.001) "float get"
  );

  test "tuple vector" (fun () ->
    let v = of_list [(1, "a"); (2, "b")] in
    assert_true (get v 0 = (1, "a")) "tuple get"
  );

  (* --- Edge cases: boundary at branching factor --- *)
  print_endline "";
  print_endline "--- Branching boundary (32 elements) ---";

  test "exactly 32 elements" (fun () ->
    let v = of_list_fast (List.init 32 (fun i -> i)) in
    assert_eq (length v) 32 "length";
    assert_eq (get v 0) 0 "first";
    assert_eq (get v 31) 31 "last"
  );

  test "33 elements (first overflow)" (fun () ->
    let v = of_list_fast (List.init 33 (fun i -> i)) in
    assert_eq (length v) 33 "length";
    assert_eq (get v 32) 32 "element 32"
  );

  test "64 elements (second chunk)" (fun () ->
    let v = of_list_fast (List.init 64 (fun i -> i)) in
    assert_eq (length v) 64 "length";
    assert_eq (get v 63) 63 "last"
  );

  test "1024 elements (32^2)" (fun () ->
    let v = of_list_fast (List.init 1024 (fun i -> i)) in
    assert_eq (length v) 1024 "length";
    assert_eq (get v 1023) 1023 "last"
  );

  test "1025 elements (second level overflow)" (fun () ->
    let v = of_list_fast (List.init 1025 (fun i -> i)) in
    assert_eq (length v) 1025 "length";
    assert_eq (get v 1024) 1024 "element 1024"
  );

  (* --- Summary --- *)
  print_newline ();
  Printf.printf "=== Results: %d/%d tests passed ===\n" !tests_passed !tests_run
