(* test_queue.ml — Tests for the Purely Functional Queue *)

#use "test_framework.ml";;

let current_suite = ref ""

let assert_equal_generic ~msg ~to_string expected actual =
  incr tests_run;
  if expected = actual then
    incr tests_passed
  else begin
    incr tests_failed;
    Printf.printf "  FAIL [%s] %s: expected %s, got %s\n"
      !current_suite msg (to_string expected) (to_string actual)
  end

let assert_equal_int ~msg expected actual =
  assert_equal_generic ~msg ~to_string:string_of_int expected actual

let assert_equal_bool ~msg expected actual =
  assert_equal_generic ~msg ~to_string:string_of_bool expected actual

let assert_equal_string ~msg expected actual =
  assert_equal_generic ~msg ~to_string:(fun s -> "\"" ^ s ^ "\"") expected actual

let assert_equal_int_list ~msg expected actual =
  let s lst = "[" ^ String.concat "; " (List.map string_of_int lst) ^ "]" in
  assert_equal_generic ~msg ~to_string:s expected actual

let assert_equal_int_opt ~msg expected actual =
  let s = function None -> "None" | Some x -> "Some(" ^ string_of_int x ^ ")" in
  assert_equal_generic ~msg ~to_string:s expected actual

let suite name f =
  current_suite := name;
  Printf.printf "Running: %s\n" name;
  f ()


(* ── Import queue functions ─────────────────────────────────── *)
(* We duplicate the core type and functions here for standalone testing,
   matching the pattern used by test_all.ml *)

type 'a queue = {
  front : 'a list;
  rear  : 'a list;
  len   : int;
}

let check q =
  match q.front with
  | [] -> { front = List.rev q.rear; rear = []; len = q.len }
  | _  -> q

let empty = { front = []; rear = []; len = 0 }

let singleton x = { front = [x]; rear = []; len = 1 }

let of_list lst = { front = lst; rear = []; len = List.length lst }

let is_empty q = q.len = 0

let length q = q.len

let peek q =
  match q.front with
  | x :: _ -> Some x
  | [] ->
    match q.rear with
    | [] -> None
    | _ ->
      let q' = check q in
      (match q'.front with x :: _ -> Some x | [] -> None)

let peek_exn q =
  match peek q with
  | Some x -> x
  | None -> failwith "Queue.peek_exn: empty queue"

let enqueue x q =
  check { q with rear = x :: q.rear; len = q.len + 1 }

let dequeue q =
  match q.front with
  | x :: rest ->
    let q' = check { front = rest; rear = q.rear; len = q.len - 1 } in
    (Some x, q')
  | [] -> (None, q)

let dequeue_exn q =
  match dequeue q with
  | (Some x, q') -> (x, q')
  | (None, _) -> failwith "Queue.dequeue_exn: empty queue"

let to_list q = q.front @ List.rev q.rear

let append q1 q2 =
  let elems = to_list q2 in
  List.fold_left (fun acc x -> enqueue x acc) q1 elems

let enqueue_all xs q =
  List.fold_left (fun acc x -> enqueue x acc) q xs

let map f q = of_list (List.map f (to_list q))

let filter pred q = of_list (List.filter pred (to_list q))

let fold_left f init q = List.fold_left f init (to_list q)

let fold_right f q init = List.fold_right f (to_list q) init

let exists pred q = List.exists pred (to_list q)

let for_all pred q = List.for_all pred (to_list q)

let find_opt pred q = List.find_opt pred (to_list q)

let iter f q = List.iter f (to_list q)

let dequeue_n n q =
  if n <= 0 then ([], q)
  else
    let rec go acc remaining count =
      if count <= 0 then (List.rev acc, remaining)
      else
        match dequeue remaining with
        | (Some x, q') -> go (x :: acc) q' (count - 1)
        | (None, q')   -> (List.rev acc, q')
    in
    go [] q n

let drop n q = let (_, q') = dequeue_n n q in q'

let take n q = let (elems, _) = dequeue_n n q in elems

let rev q = of_list (List.rev (to_list q))

let rotate q =
  match dequeue q with
  | (Some x, q') -> enqueue x q'
  | (None, q')   -> q'

let rotate_n n q =
  let n = n mod (max 1 q.len) in
  let rec go q count =
    if count <= 0 then q
    else go (rotate q) (count - 1)
  in
  go q n

let equal eq q1 q2 =
  q1.len = q2.len && List.for_all2 eq (to_list q1) (to_list q2)

let mem x q = List.mem x (to_list q)

let nth q i =
  if i < 0 || i >= q.len then None
  else Some (List.nth (to_list q) i)

let to_string f q =
  let elems = to_list q in
  "<" ^ String.concat ", " (List.map f elems) ^ ">"

let to_string_int q = to_string string_of_int q


(* ═══════════════════════════════════════════════════════════ *)
(*                        TEST SUITES                        *)
(* ═══════════════════════════════════════════════════════════ *)

let () =
  Printf.printf "╔═══════════════════════════════════════════╗\n";
  Printf.printf "║    Functional Queue Test Suite            ║\n";
  Printf.printf "╚═══════════════════════════════════════════╝\n\n";

  (* ── Empty queue ─────────────────────────────────────── *)
  suite "Empty Queue" (fun () ->
    assert_true ~msg:"empty is empty" (is_empty empty);
    assert_equal_int ~msg:"empty length" 0 (length empty);
    assert_equal_int_opt ~msg:"peek empty" None (peek empty);
    let (v, q) = dequeue empty in
    assert_equal_int_opt ~msg:"dequeue empty" None v;
    assert_true ~msg:"dequeue empty still empty" (is_empty q);
    assert_equal_string ~msg:"empty to_string" "<>" (to_string_int empty);
    assert_equal_int_list ~msg:"empty to_list" [] (to_list empty);
  );

  (* ── Singleton ───────────────────────────────────────── *)
  suite "Singleton" (fun () ->
    let q = singleton 42 in
    assert_true ~msg:"singleton not empty" (not (is_empty q));
    assert_equal_int ~msg:"singleton length" 1 (length q);
    assert_equal_int_opt ~msg:"singleton peek" (Some 42) (peek q);
    let (v, q') = dequeue_exn q in
    assert_equal_int ~msg:"singleton dequeue value" 42 v;
    assert_true ~msg:"singleton dequeue empty" (is_empty q');
  );

  (* ── Enqueue / Dequeue ───────────────────────────────── *)
  suite "Enqueue / Dequeue" (fun () ->
    let q = empty in
    let q = enqueue 1 q in
    let q = enqueue 2 q in
    let q = enqueue 3 q in
    assert_equal_int ~msg:"length after 3 enqueues" 3 (length q);
    assert_equal_int_opt ~msg:"peek first" (Some 1) (peek q);

    let (v1, q) = dequeue_exn q in
    assert_equal_int ~msg:"dequeue 1st" 1 v1;
    let (v2, q) = dequeue_exn q in
    assert_equal_int ~msg:"dequeue 2nd" 2 v2;
    let (v3, q) = dequeue_exn q in
    assert_equal_int ~msg:"dequeue 3rd" 3 v3;
    assert_true ~msg:"all dequeued" (is_empty q);
  );

  (* ── FIFO ordering ──────────────────────────────────── *)
  suite "FIFO Ordering" (fun () ->
    let q = enqueue_all [10; 20; 30; 40; 50] empty in
    assert_equal_int_list ~msg:"FIFO order" [10; 20; 30; 40; 50] (to_list q);
    assert_equal_int_opt ~msg:"first out" (Some 10) (peek q);
  );

  (* ── of_list / to_list roundtrip ─────────────────────── *)
  suite "of_list / to_list" (fun () ->
    let lst = [1; 2; 3; 4; 5] in
    let q = of_list lst in
    assert_equal_int_list ~msg:"roundtrip" lst (to_list q);
    assert_equal_int ~msg:"of_list length" 5 (length q);

    let q2 = of_list [] in
    assert_true ~msg:"of_list empty" (is_empty q2);
    assert_equal_int_list ~msg:"of_list empty roundtrip" [] (to_list q2);
  );

  (* ── Persistence ─────────────────────────────────────── *)
  suite "Persistence" (fun () ->
    let q1 = of_list [1; 2; 3] in
    let q2 = enqueue 4 q1 in
    let q3 = enqueue 5 q1 in

    (* q1 unchanged *)
    assert_equal_int_list ~msg:"original unchanged" [1; 2; 3] (to_list q1);
    assert_equal_int ~msg:"original length" 3 (length q1);

    (* q2 has 4 appended *)
    assert_equal_int_list ~msg:"branch 1" [1; 2; 3; 4] (to_list q2);

    (* q3 has 5 appended (from q1, not q2) *)
    assert_equal_int_list ~msg:"branch 2" [1; 2; 3; 5] (to_list q3);

    (* Dequeue from q1 doesn't affect q2 *)
    let (_, q1') = dequeue_exn q1 in
    assert_equal_int_list ~msg:"q1 after dequeue" [2; 3] (to_list q1');
    assert_equal_int_list ~msg:"q2 still intact" [1; 2; 3; 4] (to_list q2);
  );

  (* ── Interleaved enqueue/dequeue ─────────────────────── *)
  suite "Interleaved Operations" (fun () ->
    (* This exercises the front/rear rotation *)
    let q = enqueue 1 empty in
    let q = enqueue 2 q in
    let (v, q) = dequeue_exn q in
    assert_equal_int ~msg:"interleave dequeue 1" 1 v;
    let q = enqueue 3 q in
    let q = enqueue 4 q in
    let (v, q) = dequeue_exn q in
    assert_equal_int ~msg:"interleave dequeue 2" 2 v;
    let (v, q) = dequeue_exn q in
    assert_equal_int ~msg:"interleave dequeue 3" 3 v;
    let (v, q) = dequeue_exn q in
    assert_equal_int ~msg:"interleave dequeue 4" 4 v;
    assert_true ~msg:"interleave empty" (is_empty q);
  );

  (* ── Large queue stress test ─────────────────────────── *)
  suite "Stress Test" (fun () ->
    let n = 1000 in
    let q = ref empty in
    for i = 1 to n do
      q := enqueue i !q
    done;
    assert_equal_int ~msg:"stress length" n (length !q);
    assert_equal_int_opt ~msg:"stress peek" (Some 1) (peek !q);

    for i = 1 to n do
      let (v, q') = dequeue_exn !q in
      assert_equal_int ~msg:(Printf.sprintf "stress dequeue %d" i) i v;
      q := q'
    done;
    assert_true ~msg:"stress empty after all dequeues" (is_empty !q);
  );

  (* ── Map ─────────────────────────────────────────────── *)
  suite "Map" (fun () ->
    let q = of_list [1; 2; 3; 4; 5] in
    let doubled = map (fun x -> x * 2) q in
    assert_equal_int_list ~msg:"map double" [2; 4; 6; 8; 10] (to_list doubled);
    assert_equal_int ~msg:"map preserves length" 5 (length doubled);

    let mapped_empty = map (fun x -> x + 1) empty in
    assert_true ~msg:"map empty" (is_empty mapped_empty);
  );

  (* ── Filter ──────────────────────────────────────────── *)
  suite "Filter" (fun () ->
    let q = of_list [1; 2; 3; 4; 5; 6; 7; 8; 9; 10] in
    let evens = filter (fun x -> x mod 2 = 0) q in
    assert_equal_int_list ~msg:"filter evens" [2; 4; 6; 8; 10] (to_list evens);
    assert_equal_int ~msg:"filter length" 5 (length evens);

    let none = filter (fun x -> x > 100) q in
    assert_true ~msg:"filter all out" (is_empty none);

    let all = filter (fun _ -> true) q in
    assert_equal_int ~msg:"filter keep all" 10 (length all);
  );

  (* ── Fold ────────────────────────────────────────────── *)
  suite "Fold" (fun () ->
    let q = of_list [1; 2; 3; 4; 5] in
    let sum = fold_left (+) 0 q in
    assert_equal_int ~msg:"fold_left sum" 15 sum;

    let product = fold_left ( * ) 1 q in
    assert_equal_int ~msg:"fold_left product" 120 product;

    (* fold_right builds list in order *)
    let lst = fold_right (fun x acc -> x :: acc) q [] in
    assert_equal_int_list ~msg:"fold_right list" [1; 2; 3; 4; 5] lst;

    let sum_empty = fold_left (+) 0 empty in
    assert_equal_int ~msg:"fold_left empty" 0 sum_empty;
  );

  (* ── Exists / For_all / Find ─────────────────────────── *)
  suite "Exists / For_all / Find" (fun () ->
    let q = of_list [10; 20; 30; 40; 50] in

    assert_true ~msg:"exists 30" (exists (fun x -> x = 30) q);
    assert_true ~msg:"not exists 99" (not (exists (fun x -> x = 99) q));

    assert_true ~msg:"for_all > 0" (for_all (fun x -> x > 0) q);
    assert_true ~msg:"not for_all > 25" (not (for_all (fun x -> x > 25) q));

    assert_equal_int_opt ~msg:"find even" (Some 10) (find_opt (fun x -> x mod 2 = 0) q);
    assert_equal_int_opt ~msg:"find > 35" (Some 40) (find_opt (fun x -> x > 35) q);
    assert_equal_int_opt ~msg:"find > 100" None (find_opt (fun x -> x > 100) q);

    assert_true ~msg:"exists on empty" (not (exists (fun _ -> true) empty));
    assert_true ~msg:"for_all on empty" (for_all (fun _ -> false) empty);
  );

  (* ── Dequeue_n / Take / Drop ─────────────────────────── *)
  suite "Dequeue_n / Take / Drop" (fun () ->
    let q = of_list [1; 2; 3; 4; 5] in

    let (batch, rest) = dequeue_n 3 q in
    assert_equal_int_list ~msg:"dequeue_n 3 batch" [1; 2; 3] batch;
    assert_equal_int_list ~msg:"dequeue_n 3 rest" [4; 5] (to_list rest);

    let (all, rest2) = dequeue_n 10 q in
    assert_equal_int_list ~msg:"dequeue_n overflow" [1; 2; 3; 4; 5] all;
    assert_true ~msg:"dequeue_n overflow empty" (is_empty rest2);

    let (none, rest3) = dequeue_n 0 q in
    assert_equal_int_list ~msg:"dequeue_n 0" [] none;
    assert_equal_int ~msg:"dequeue_n 0 length" 5 (length rest3);

    assert_equal_int_list ~msg:"take 2" [1; 2] (take 2 q);
    assert_equal_int_list ~msg:"drop 2" [3; 4; 5] (to_list (drop 2 q));
  );

  (* ── Append ──────────────────────────────────────────── *)
  suite "Append" (fun () ->
    let q1 = of_list [1; 2; 3] in
    let q2 = of_list [4; 5; 6] in
    let combined = append q1 q2 in
    assert_equal_int_list ~msg:"append" [1; 2; 3; 4; 5; 6] (to_list combined);
    assert_equal_int ~msg:"append length" 6 (length combined);

    (* Append empty *)
    let a1 = append q1 empty in
    assert_equal_int_list ~msg:"append empty right" [1; 2; 3] (to_list a1);
    let a2 = append empty q2 in
    assert_equal_int_list ~msg:"append empty left" [4; 5; 6] (to_list a2);
  );

  (* ── Enqueue_all ─────────────────────────────────────── *)
  suite "Enqueue_all" (fun () ->
    let q = of_list [1; 2] in
    let q = enqueue_all [3; 4; 5] q in
    assert_equal_int_list ~msg:"enqueue_all" [1; 2; 3; 4; 5] (to_list q);

    let q2 = enqueue_all [] empty in
    assert_true ~msg:"enqueue_all empty" (is_empty q2);
  );

  (* ── Reverse ─────────────────────────────────────────── *)
  suite "Reverse" (fun () ->
    let q = of_list [1; 2; 3; 4; 5] in
    let r = rev q in
    assert_equal_int_list ~msg:"reverse" [5; 4; 3; 2; 1] (to_list r);
    assert_equal_int ~msg:"reverse length" 5 (length r);

    let r_empty = rev empty in
    assert_true ~msg:"reverse empty" (is_empty r_empty);

    let r_single = rev (singleton 42) in
    assert_equal_int_list ~msg:"reverse singleton" [42] (to_list r_single);
  );

  (* ── Rotate ──────────────────────────────────────────── *)
  suite "Rotate" (fun () ->
    let q = of_list [1; 2; 3; 4; 5] in
    let r1 = rotate q in
    assert_equal_int_list ~msg:"rotate 1" [2; 3; 4; 5; 1] (to_list r1);

    let r3 = rotate_n 3 q in
    assert_equal_int_list ~msg:"rotate 3" [4; 5; 1; 2; 3] (to_list r3);

    let r5 = rotate_n 5 q in
    assert_equal_int_list ~msg:"rotate full circle" [1; 2; 3; 4; 5] (to_list r5);

    let r0 = rotate_n 0 q in
    assert_equal_int_list ~msg:"rotate 0" [1; 2; 3; 4; 5] (to_list r0);

    let re = rotate empty in
    assert_true ~msg:"rotate empty" (is_empty re);
  );

  (* ── Equal ───────────────────────────────────────────── *)
  suite "Equal" (fun () ->
    let q1 = of_list [1; 2; 3] in
    let q2 = of_list [1; 2; 3] in
    let q3 = of_list [1; 2; 4] in
    let q4 = of_list [1; 2] in

    assert_true ~msg:"equal same" (equal (=) q1 q2);
    assert_true ~msg:"not equal diff value" (not (equal (=) q1 q3));
    assert_true ~msg:"not equal diff length" (not (equal (=) q1 q4));
    assert_true ~msg:"empty equal empty" (equal (=) empty empty);

    (* Equal after different construction paths *)
    let qa = enqueue 3 (enqueue 2 (enqueue 1 empty)) in
    assert_true ~msg:"equal diff construction" (equal (=) q1 qa);
  );

  (* ── Mem / Nth ───────────────────────────────────────── *)
  suite "Mem / Nth" (fun () ->
    let q = of_list [10; 20; 30; 40; 50] in

    assert_true ~msg:"mem 30" (mem 30 q);
    assert_true ~msg:"not mem 99" (not (mem 99 q));
    assert_true ~msg:"not mem in empty" (not (mem 1 empty));

    assert_equal_int_opt ~msg:"nth 0" (Some 10) (nth q 0);
    assert_equal_int_opt ~msg:"nth 2" (Some 30) (nth q 2);
    assert_equal_int_opt ~msg:"nth 4" (Some 50) (nth q 4);
    assert_equal_int_opt ~msg:"nth out of bounds" None (nth q 5);
    assert_equal_int_opt ~msg:"nth negative" None (nth q (-1));
    assert_equal_int_opt ~msg:"nth empty" None (nth empty 0);
  );

  (* ── To_string ───────────────────────────────────────── *)
  suite "To_string" (fun () ->
    let q = of_list [1; 2; 3] in
    assert_equal_string ~msg:"to_string" "<1, 2, 3>" (to_string_int q);
    assert_equal_string ~msg:"to_string empty" "<>" (to_string_int empty);
    assert_equal_string ~msg:"to_string singleton" "<42>" (to_string_int (singleton 42));
  );

  (* ── Iter ────────────────────────────────────────────── *)
  suite "Iter" (fun () ->
    let q = of_list [1; 2; 3; 4; 5] in
    let sum = ref 0 in
    iter (fun x -> sum := !sum + x) q;
    assert_equal_int ~msg:"iter sum" 15 !sum;

    let items = ref [] in
    iter (fun x -> items := x :: !items) q;
    assert_equal_int_list ~msg:"iter order" [5; 4; 3; 2; 1] !items;
  );

  (* ── Exception paths ─────────────────────────────────── *)
  suite "Exceptions" (fun () ->
    assert_raises ~msg:"peek_exn on empty" (fun () -> peek_exn empty);
    assert_raises ~msg:"dequeue_exn on empty" (fun () -> dequeue_exn empty);
  );

  (* ── Invariant check (front/rear rotation) ──────────── *)
  suite "Invariant" (fun () ->
    (* Build a queue by only enqueuing (rear grows, front stays empty
       until check kicks in) *)
    let q = enqueue 1 empty in
    assert_equal_int_opt ~msg:"single enqueue peek" (Some 1) (peek q);

    let q = enqueue 2 q in
    let q = enqueue 3 q in
    assert_equal_int_opt ~msg:"multi enqueue peek" (Some 1) (peek q);

    (* Drain and re-fill to exercise multiple rotations *)
    let q = of_list [1; 2; 3] in
    let (_, q) = dequeue_exn q in
    let (_, q) = dequeue_exn q in
    let (_, q) = dequeue_exn q in
    let q = enqueue 4 q in
    let q = enqueue 5 q in
    assert_equal_int_opt ~msg:"refill peek" (Some 4) (peek q);
    assert_equal_int_list ~msg:"refill list" [4; 5] (to_list q);
  );

  (* ── Mixed type (string queue) ──────────────────────── *)
  suite "String Queue" (fun () ->
    let q = of_list ["hello"; "world"; "ocaml"] in
    assert_equal_int ~msg:"string queue length" 3 (length q);
    let (v, q') = dequeue_exn q in
    assert_equal_string ~msg:"string dequeue" "hello" v;
    let mapped = map String.uppercase_ascii q in
    let result = to_list mapped in
    assert_true ~msg:"string map"
      (result = ["HELLO"; "WORLD"; "OCAML"]);
  );

  (* ── Summary ─────────────────────────────────────────── *)
  Printf.printf "\n════════════════════════════════════════════\n";
  test_summary ()