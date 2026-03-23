(* Tests for Ring Buffer *)

(* Minimal test harness *)
let tests_run = ref 0
let tests_passed = ref 0

let assert_equal name expected actual =
  incr tests_run;
  if expected = actual then incr tests_passed
  else Printf.printf "FAIL: %s — expected %s, got %s\n" name
    (string_of_int expected) (string_of_int actual)

let assert_true name cond =
  incr tests_run;
  if cond then incr tests_passed
  else Printf.printf "FAIL: %s\n" name

let assert_raises name f =
  incr tests_run;
  try f (); Printf.printf "FAIL: %s — no exception\n" name
  with _ -> incr tests_passed

(* Pull in the module by compiling together with ring_buffer.ml *)

let () =
  Printf.printf "Ring Buffer Tests\n";
  Printf.printf "=================\n\n";

  (* Test create *)
  let rb = RingBuffer.create 4 0 in
  assert_equal "create capacity" 4 (RingBuffer.capacity rb);
  assert_equal "create length" 0 (RingBuffer.length rb);
  assert_true "create is_empty" (RingBuffer.is_empty rb);

  (* Test push_back *)
  RingBuffer.push_back rb 1;
  RingBuffer.push_back rb 2;
  RingBuffer.push_back rb 3;
  assert_equal "push_back length" 3 (RingBuffer.length rb);
  assert_equal "peek_front" 1 (RingBuffer.peek_front rb);
  assert_equal "peek_back" 3 (RingBuffer.peek_back rb);

  (* Test overflow *)
  RingBuffer.push_back rb 4;
  RingBuffer.push_back rb 5; (* overwrites 1 *)
  assert_equal "overflow length" 4 (RingBuffer.length rb);
  assert_equal "overflow front" 2 (RingBuffer.peek_front rb);
  assert_equal "overflow back" 5 (RingBuffer.peek_back rb);
  assert_true "overflow is_full" (RingBuffer.is_full rb);

  (* Test pop_front *)
  let v = RingBuffer.pop_front rb in
  assert_equal "pop_front value" 2 v;
  assert_equal "pop_front length" 3 (RingBuffer.length rb);

  (* Test pop_back *)
  let v2 = RingBuffer.pop_back rb in
  assert_equal "pop_back value" 5 v2;
  assert_equal "pop_back length" 2 (RingBuffer.length rb);

  (* Test get/set *)
  assert_equal "get 0" 3 (RingBuffer.get rb 0);
  assert_equal "get 1" 4 (RingBuffer.get rb 1);
  RingBuffer.set rb 0 33;
  assert_equal "set then get" 33 (RingBuffer.get rb 0);

  (* Test push_front *)
  RingBuffer.push_front rb 10;
  assert_equal "push_front front" 10 (RingBuffer.peek_front rb);
  assert_equal "push_front length" 3 (RingBuffer.length rb);

  (* Test to_list *)
  let lst = RingBuffer.to_list rb in
  assert_true "to_list" (lst = [10; 33; 4]);

  (* Test to_array *)
  let arr = RingBuffer.to_array rb in
  assert_equal "to_array len" 3 (Array.length arr);
  assert_equal "to_array[0]" 10 arr.(0);

  (* Test fold_left *)
  let sum = RingBuffer.fold_left ( + ) 0 rb in
  assert_equal "fold_left sum" 47 sum;

  (* Test exists / for_all *)
  assert_true "exists >30" (RingBuffer.exists (fun x -> x > 30) rb);
  assert_true "not exists >100" (not (RingBuffer.exists (fun x -> x > 100) rb));
  assert_true "for_all >0" (RingBuffer.for_all (fun x -> x > 0) rb);

  (* Test clear *)
  RingBuffer.clear rb;
  assert_true "clear is_empty" (RingBuffer.is_empty rb);
  assert_equal "clear length" 0 (RingBuffer.length rb);

  (* Test empty exceptions *)
  assert_raises "pop_front empty" (fun () -> ignore (RingBuffer.pop_front rb));
  assert_raises "pop_back empty" (fun () -> ignore (RingBuffer.pop_back rb));
  assert_raises "peek_front empty" (fun () -> ignore (RingBuffer.peek_front rb));

  (* Test of_list with overflow *)
  let rb3 = RingBuffer.of_list 3 0 [1; 2; 3; 4; 5] in
  assert_equal "of_list overflow len" 3 (RingBuffer.length rb3);
  assert_equal "of_list overflow front" 3 (RingBuffer.peek_front rb3);
  assert_equal "of_list overflow back" 5 (RingBuffer.peek_back rb3);

  (* Test invalid create *)
  assert_raises "create cap 0" (fun () -> ignore (RingBuffer.create 0 0));

  (* Results *)
  Printf.printf "\n%d/%d tests passed\n" !tests_passed !tests_run;
  if !tests_passed = !tests_run then
    Printf.printf "All tests passed!\n"
  else
    Printf.printf "Some tests FAILED.\n"
