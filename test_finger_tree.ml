(* test_ml — Tests for ml
 *
 * Covers: construction, push left/right, head/tail/last/init,
 * concatenation, split, of_list/to_list, fold, filter, reverse,
 * priority queue specialisation, sorted sequence specialisation.
 *
 * Usage:
 *   ocaml test_ml
 *   -- or compiled --
 *   ocamlopt ml test_ml -o test_finger_tree && ./test_finger_tree
 *)

#use "test_framework.ml";;
#use "ml";;

(* ── Minimal test harness ─────────────────────────────────────────── *)

let current_suite = ref ""

let assert_equal_list ~msg expected actual =
  incr tests_run;
  if expected = actual then incr tests_passed
  else begin
    incr tests_failed;
    let show xs = "[" ^ String.concat "; " (List.map string_of_int xs) ^ "]" in
    Printf.printf "  FAIL [%s] %s: expected %s, got %s\n"
      !current_suite msg (show expected) (show actual)
  end

let assert_int ~msg expected actual =
  incr tests_run;
  if expected = actual then incr tests_passed
  else begin
    incr tests_failed;
    Printf.printf "  FAIL [%s] %s: expected %d, got %d\n"
      !current_suite msg expected actual
  end

let suite name f =
  current_suite := name;
  Printf.printf "Testing %s...\n" name;
  f ()

(* ── IntSeq tests ─────────────────────────────────────────────────── *)

let () = suite "IntSeq — construction" (fun () ->
  let open IntSeq in
  assert_true ~msg:"empty is_empty" (is_empty empty);
  assert_true ~msg:"singleton not empty" (not (is_empty (singleton 42)));
  assert_equal_list ~msg:"of_list []" [] (to_list empty);
  assert_equal_list ~msg:"of_list [1]" [1] (to_list (of_list [1]));
  assert_equal_list ~msg:"of_list [1;2;3]" [1;2;3] (to_list (of_list [1;2;3]));
  assert_equal_list ~msg:"of_list 1..10"
    [1;2;3;4;5;6;7;8;9;10] (to_list (of_list [1;2;3;4;5;6;7;8;9;10]));
)

let () = suite "IntSeq — push_left" (fun () ->
  let open IntSeq in
  assert_equal_list ~msg:"push_left to empty" [1] (to_list (push_left 1 empty));
  assert_equal_list ~msg:"push_left to singleton" [0;1]
    (to_list (push_left 0 (singleton 1)));
  let t = of_list [2;3;4] in
  assert_equal_list ~msg:"push_left 1" [1;2;3;4] (to_list (push_left 1 t));
  (* Build up through digit overflow *)
  let t5 = List.fold_right push_left [1;2;3;4;5;6;7;8] empty in
  assert_equal_list ~msg:"push_left 8 elts" [1;2;3;4;5;6;7;8] (to_list t5);
)

let () = suite "IntSeq — push_right" (fun () ->
  let open IntSeq in
  assert_equal_list ~msg:"push_right to empty" [1]
    (to_list (push_right empty 1));
  assert_equal_list ~msg:"push_right to singleton" [1;2]
    (to_list (push_right (singleton 1) 2));
  let t = of_list [1;2;3] in
  assert_equal_list ~msg:"push_right 4" [1;2;3;4] (to_list (push_right t 4));
  (* Build up through digit overflow *)
  let t8 = List.fold_left push_right empty [1;2;3;4;5;6;7;8] in
  assert_equal_list ~msg:"push_right 8 elts" [1;2;3;4;5;6;7;8] (to_list t8);
)

let () = suite "IntSeq — head/last" (fun () ->
  let open IntSeq in
  assert_int ~msg:"head singleton" 42 (head (singleton 42));
  assert_int ~msg:"last singleton" 42 (last (singleton 42));
  let t = of_list [10;20;30] in
  assert_int ~msg:"head [10;20;30]" 10 (head t);
  assert_int ~msg:"last [10;20;30]" 30 (last t);
  assert_raises ~msg:"head empty" (fun () -> head empty);
  assert_raises ~msg:"last empty" (fun () -> last empty);
)

let () = suite "IntSeq — tail/init" (fun () ->
  let open IntSeq in
  assert_equal_list ~msg:"tail [1;2;3]" [2;3]
    (to_list (tail (of_list [1;2;3])));
  assert_equal_list ~msg:"init [1;2;3]" [1;2]
    (to_list (init (of_list [1;2;3])));
  assert_equal_list ~msg:"tail singleton" []
    (to_list (tail (singleton 1)));
  assert_equal_list ~msg:"init singleton" []
    (to_list (init (singleton 1)));
  assert_raises ~msg:"tail empty" (fun () -> tail empty);
  assert_raises ~msg:"init empty" (fun () -> init empty);
  (* Cascading tail through Deep with empty prefix *)
  let big = of_list [1;2;3;4;5;6;7;8;9;10] in
  let rec drain_left t =
    if is_empty t then []
    else head t :: drain_left (tail t) in
  assert_equal_list ~msg:"drain via tail" [1;2;3;4;5;6;7;8;9;10]
    (drain_left big);
)

let () = suite "IntSeq — concat" (fun () ->
  let open IntSeq in
  assert_equal_list ~msg:"concat empty+empty" []
    (to_list (concat empty empty));
  assert_equal_list ~msg:"concat empty+[1;2]" [1;2]
    (to_list (concat empty (of_list [1;2])));
  assert_equal_list ~msg:"concat [1;2]+empty" [1;2]
    (to_list (concat (of_list [1;2]) empty));
  assert_equal_list ~msg:"concat [1;2;3]+[4;5;6]" [1;2;3;4;5;6]
    (to_list (concat (of_list [1;2;3]) (of_list [4;5;6])));
  (* Large concat *)
  let a = of_list (List.init 50 Fun.id) in
  let b = of_list (List.init 50 (fun i -> i + 50)) in
  assert_equal_list ~msg:"concat 50+50"
    (List.init 100 Fun.id) (to_list (concat a b));
  (* Multiple concats *)
  let c = concat (concat (of_list [1;2]) (of_list [3;4]))
                 (concat (of_list [5;6]) (of_list [7;8])) in
  assert_equal_list ~msg:"nested concat" [1;2;3;4;5;6;7;8] (to_list c);
)

let () = suite "IntSeq — split" (fun () ->
  let open IntSeq in
  (* Split by index: predicate is "accumulated size > i" *)
  let nth t i = (split (fun s -> s > i) t).pivot in
  let t = of_list [10;20;30;40;50] in
  assert_int ~msg:"nth 0" 10 (nth t 0);
  assert_int ~msg:"nth 2" 30 (nth t 2);
  assert_int ~msg:"nth 4" 50 (nth t 4);
  (* Split preserves all elements *)
  let { left; pivot; right } = split (fun s -> s > 2) t in
  assert_equal_list ~msg:"split left" [10;20] (to_list left);
  assert_int ~msg:"split pivot" 30 pivot;
  assert_equal_list ~msg:"split right" [40;50] (to_list right);
  (* Split singleton *)
  let { left = l1; pivot = p1; right = r1 } =
    split (fun s -> s > 0) (singleton 99) in
  assert_equal_list ~msg:"split singleton left" [] (to_list l1);
  assert_int ~msg:"split singleton pivot" 99 p1;
  assert_equal_list ~msg:"split singleton right" [] (to_list r1);
)

let () = suite "IntSeq — fold/iter" (fun () ->
  let open IntSeq in
  let t = of_list [1;2;3;4;5] in
  assert_int ~msg:"fold_left sum" 15 (fold_left ( + ) 0 t);
  assert_int ~msg:"fold_left product" 120 (fold_left ( * ) 1 t);
  assert_int ~msg:"fold_right sum" 15 (fold_right ( + ) t 0);
  assert_int ~msg:"fold_left empty" 0 (fold_left ( + ) 0 empty);
  (* iter *)
  let acc = ref 0 in
  iter (fun x -> acc := !acc + x) t;
  assert_int ~msg:"iter sum" 15 !acc;
)

let () = suite "IntSeq — rev/filter/take_while/drop_while" (fun () ->
  let open IntSeq in
  let t = of_list [1;2;3;4;5] in
  assert_equal_list ~msg:"rev" [5;4;3;2;1] (to_list (rev t));
  assert_equal_list ~msg:"rev empty" [] (to_list (rev empty));
  assert_equal_list ~msg:"filter even" [2;4]
    (to_list (filter (fun x -> x mod 2 = 0) t));
  assert_equal_list ~msg:"filter all" [1;2;3;4;5]
    (to_list (filter (fun _ -> true) t));
  assert_equal_list ~msg:"filter none" []
    (to_list (filter (fun _ -> false) t));
  assert_equal_list ~msg:"take_while < 4" [1;2;3]
    (to_list (take_while (fun x -> x < 4) t));
  assert_equal_list ~msg:"drop_while < 4" [4;5]
    (to_list (drop_while (fun x -> x < 4) t));
)

let () = suite "IntSeq — length/measure" (fun () ->
  let open IntSeq in
  assert_int ~msg:"length empty" 0 (length empty);
  assert_int ~msg:"length singleton" 1 (length (singleton 1));
  assert_int ~msg:"length 5" 5 (length (of_list [1;2;3;4;5]));
  assert_int ~msg:"measure 3" 3 (measure (of_list [1;2;3]));
  assert_int ~msg:"measure empty" 0 (measure empty);
)

(* ── PrioQueue tests ──────────────────────────────────────────────── *)

let () = suite "PrioQueue — extract min" (fun () ->
  let open PrioQueue in
  let pq = of_list [5; 3; 8; 1; 4; 9; 2; 7; 6] in
  assert_int ~msg:"measure = min" 1 (measure pq);
  let m = measure pq in
  let { pivot; left; right } = split (fun x -> x <= m) pq in
  assert_int ~msg:"extract min" 1 pivot;
  let rest = concat left right in
  assert_int ~msg:"next min" 2 (measure rest);
  (* Drain all in order *)
  let rec drain acc t =
    if is_empty t then List.rev acc
    else
      let m = measure t in
      let { pivot; left; right } = split (fun x -> x <= m) t in
      drain (pivot :: acc) (concat left right) in
  assert_equal_list ~msg:"drain sorted" [1;2;3;4;5;6;7;8;9] (drain [] pq);
)

let () = suite "PrioQueue — single element" (fun () ->
  let open PrioQueue in
  let pq = singleton 42 in
  assert_int ~msg:"measure singleton" 42 (measure pq);
  assert_int ~msg:"head singleton" 42 (head pq);
)

(* ── SortedSeq tests ──────────────────────────────────────────────── *)

let () = suite "SortedSeq — sorted insert" (fun () ->
  let open SortedSeq in
  let sorted_insert x t =
    if is_empty t then singleton x
    else if x <= head t then push_left x t
    else if x >= last t then push_right t x
    else
      let { left; right; _ } = split (fun m -> m >= x) t in
      concat (push_right left x) right in
  let sorted = List.fold_left (fun t x -> sorted_insert x t)
                 empty [5; 3; 8; 1; 4; 9; 2; 7; 6; 10] in
  assert_equal_list ~msg:"sorted order" [1;2;3;4;5;6;7;8;9;10]
    (to_list sorted);
  assert_int ~msg:"max measure" 10 (measure sorted);
)

(* ── Edge cases ───────────────────────────────────────────────────── *)

let () = suite "Edge cases" (fun () ->
  let open IntSeq in
  (* Lots of pushes to stress digit overflow *)
  let n = 100 in
  let big = List.init n Fun.id |> of_list in
  assert_int ~msg:"length 100" n (length big);
  assert_int ~msg:"head 100" 0 (head big);
  assert_int ~msg:"last 100" 99 (last big);
  assert_equal_list ~msg:"to_list 100" (List.init n Fun.id) (to_list big);
  (* Interleaved push_left and push_right *)
  let t = push_right (push_left 1 (push_right (push_left 2 empty) 3)) 4 in
  assert_equal_list ~msg:"interleaved pushes" [1;2;3;4] (to_list t);
  (* Repeated concat *)
  let base = of_list [1;2] in
  let t4 = concat base base in
  assert_equal_list ~msg:"concat [1;2]+[1;2]" [1;2;1;2] (to_list t4);
)

(* ── Summary ──────────────────────────────────────────────────────── *)

let () =
  Printf.printf "\n--- Results ---\n";
  Printf.printf "Total: %d | Passed: %d | Failed: %d\n"
    !tests_run !tests_passed !tests_failed;
  if !tests_failed = 0 then
  test_summary ()
