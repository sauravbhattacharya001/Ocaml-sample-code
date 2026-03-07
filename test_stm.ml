(* test_stm.ml — Tests for Software Transactional Memory *)

#use "stm.ml";;

(* ---- Minimal test framework ---- *)

let tests_run = ref 0
let tests_passed = ref 0
let tests_failed = ref 0

let assert_test name condition =
  incr tests_run;
  if condition then begin
    incr tests_passed;
    Printf.printf "  ✓ %s\n" name
  end else begin
    incr tests_failed;
    Printf.printf "  ✗ %s\n" name
  end

let print_results () =
  Printf.printf "\n══════════════════════════════════\n";
  Printf.printf "  Tests: %d passed, %d failed, %d total\n"
    !tests_passed !tests_failed !tests_run;
  Printf.printf "══════════════════════════════════\n"


(* ════════════════════════════════════════════════════════════════
   TVar basics
   ════════════════════════════════════════════════════════════════ *)

let () = Printf.printf "\n── TVar Basics ──\n"

let () =
  let tv = new_tvar 42 in
  assert_test "new_tvar initial value"
    (read_tvar_raw tv = 42)

let () =
  let tv = new_tvar 0 in
  write_tvar_raw tv 99;
  assert_test "write_tvar_raw updates value"
    (read_tvar_raw tv = 99)

let () =
  let tv = new_tvar 10 in
  let v0 = tv.version in
  write_tvar_raw tv 20;
  assert_test "write_tvar_raw bumps version"
    (tv.version = v0 + 1)

let () =
  let a = new_tvar 1 in
  let b = new_tvar 2 in
  assert_test "tvars get unique ids"
    (a.id <> b.id)


(* ════════════════════════════════════════════════════════════════
   Atomic read/write
   ════════════════════════════════════════════════════════════════ *)

let () = Printf.printf "\n── Atomic Read/Write ──\n"

let () =
  let tv = new_tvar 42 in
  let v = atomically_exn (read_tvar tv) in
  assert_test "atomically read_tvar"
    (v = 42)

let () =
  let tv = new_tvar 0 in
  atomically_exn (write_tvar tv 100);
  assert_test "atomically write_tvar"
    (read_tvar_raw tv = 100)

let () =
  let tv = new_tvar 5 in
  atomically_exn (modify_tvar tv (fun n -> n * 3));
  assert_test "modify_tvar"
    (read_tvar_raw tv = 15)


(* ════════════════════════════════════════════════════════════════
   Monadic composition
   ════════════════════════════════════════════════════════════════ *)

let () = Printf.printf "\n── Monadic Composition ──\n"

let () =
  let tv = new_tvar 10 in
  let action = stm_bind (read_tvar tv) (fun v ->
    write_tvar tv (v + 5)) in
  atomically_exn action;
  assert_test "stm_bind sequences read then write"
    (read_tvar_raw tv = 15)

let () =
  let tv = new_tvar 7 in
  let v = atomically_exn (stm_map (fun x -> x * 10) (read_tvar tv)) in
  assert_test "stm_map applies function"
    (v = 70)

let () =
  let a = new_tvar 1 in
  let b = new_tvar 2 in
  let action = stm_seq (write_tvar a 10) (read_tvar b) in
  let v = atomically_exn action in
  assert_test "stm_seq returns second result"
    (v = 2 && read_tvar_raw a = 10)


(* ════════════════════════════════════════════════════════════════
   Read-your-writes consistency
   ════════════════════════════════════════════════════════════════ *)

let () = Printf.printf "\n── Read-Your-Writes ──\n"

let () =
  let tv = new_tvar 0 in
  let action = stm_bind (write_tvar tv 42) (fun () ->
    read_tvar tv) in
  let v = atomically_exn action in
  assert_test "read after write in same tx sees buffered value"
    (v = 42)

let () =
  let tv = new_tvar 0 in
  let action =
    stm_bind (write_tvar tv 10) (fun () ->
    stm_bind (write_tvar tv 20) (fun () ->
    read_tvar tv)) in
  let v = atomically_exn action in
  assert_test "multiple writes, read sees last"
    (v = 20)


(* ════════════════════════════════════════════════════════════════
   Bank account / transfer
   ════════════════════════════════════════════════════════════════ *)

let () = Printf.printf "\n── Bank Transfer ──\n"

let () =
  let acc = new_account "Test" 1000 in
  atomically_exn (deposit acc 500);
  let bal = atomically_exn (get_balance acc) in
  assert_test "deposit increases balance"
    (bal = 1500)

let () =
  let acc = new_account "Test" 1000 in
  atomically_exn (withdraw acc 300);
  let bal = atomically_exn (get_balance acc) in
  assert_test "withdraw decreases balance"
    (bal = 700)

let () =
  let acc = new_account "Test" 100 in
  let result = atomically (withdraw acc 200) in
  assert_test "withdraw insufficient funds retries"
    (match result with Retried -> true | _ -> false)

let () =
  let a = new_account "A" 1000 in
  let b = new_account "B" 500 in
  atomically_exn (transfer a b 300);
  let ba = atomically_exn (get_balance a) in
  let bb = atomically_exn (get_balance b) in
  assert_test "transfer is atomic (total preserved)"
    (ba = 700 && bb = 800 && ba + bb = 1500)

let () =
  let a = new_account "A" 100 in
  let b = new_account "B" 500 in
  let result = atomically (transfer a b 200) in
  assert_test "transfer with insufficient funds retries"
    (match result with Retried -> true | _ -> false)


(* ════════════════════════════════════════════════════════════════
   Retry and OrElse
   ════════════════════════════════════════════════════════════════ *)

let () = Printf.printf "\n── Retry & OrElse ──\n"

let () =
  let result = atomically stm_retry in
  assert_test "bare retry returns Retried"
    (match result with Retried -> true | _ -> false)

let () =
  let result = atomically (stm_or_else stm_retry (stm_return 42)) in
  assert_test "orElse falls back on retry"
    (match result with Value 42 -> true | _ -> false)

let () =
  let result = atomically (stm_or_else (stm_return 1) (stm_return 2)) in
  assert_test "orElse takes first if it succeeds"
    (match result with Value 1 -> true | _ -> false)

let () =
  let result = atomically (stm_or_else stm_retry stm_retry) in
  assert_test "both retry → combined retries"
    (match result with Retried -> true | _ -> false)

let () =
  let poor = new_account "Poor" 10 in
  let rich = new_account "Rich" 5000 in
  let name = atomically_exn (withdraw_from_either poor rich 100) in
  assert_test "withdraw_from_either uses fallback"
    (name = "Rich")

let () =
  assert_test "stm_guard true succeeds"
    (match atomically (stm_guard true) with Value () -> true | _ -> false)

let () =
  assert_test "stm_guard false retries"
    (match atomically (stm_guard false) with Retried -> true | _ -> false)

let () =
  let tv = new_tvar 10 in
  assert_test "stm_check with true pred succeeds"
    (match atomically (stm_check tv (fun v -> v > 5)) with Value () -> true | _ -> false)

let () =
  let tv = new_tvar 3 in
  assert_test "stm_check with false pred retries"
    (match atomically (stm_check tv (fun v -> v > 5)) with Retried -> true | _ -> false)


(* ════════════════════════════════════════════════════════════════
   Channel
   ════════════════════════════════════════════════════════════════ *)

let () = Printf.printf "\n── Bounded Channel ──\n"

let () =
  let ch = new_channel 2 in
  atomically_exn (send ch "a");
  atomically_exn (send ch "b");
  let m1 = atomically_exn (receive ch) in
  let m2 = atomically_exn (receive ch) in
  assert_test "channel FIFO order"
    (m1 = "a" && m2 = "b")

let () =
  let ch = new_channel 1 in
  atomically_exn (send ch "x");
  let result = atomically (send ch "y") in
  assert_test "send to full channel retries"
    (match result with Retried -> true | _ -> false)

let () =
  let ch : string channel = new_channel 5 in
  let result = atomically (receive ch) in
  assert_test "receive from empty channel retries"
    (match result with Retried -> true | _ -> false)

let () =
  let ch : int channel = new_channel 5 in
  let v = atomically_exn (try_receive ch) in
  assert_test "try_receive from empty returns None"
    (v = None)

let () =
  let ch = new_channel 5 in
  atomically_exn (send ch 42);
  let v = atomically_exn (try_receive ch) in
  assert_test "try_receive returns Some when available"
    (v = Some 42)


(* ════════════════════════════════════════════════════════════════
   TMap
   ════════════════════════════════════════════════════════════════ *)

let () = Printf.printf "\n── Transactional Map ──\n"

let () =
  let m = new_tmap () in
  atomically_exn (tmap_put m "k" 99);
  let v = atomically_exn (tmap_get m "k") in
  assert_test "tmap put then get"
    (v = Some 99)

let () =
  let m = new_tmap () in
  let v = atomically_exn (tmap_get m "missing") in
  assert_test "tmap get missing key"
    (v = None)

let () =
  let m = new_tmap () in
  atomically_exn (tmap_put m "a" 1);
  atomically_exn (tmap_put m "b" 2);
  let sz = atomically_exn (tmap_size m) in
  assert_test "tmap size"
    (sz = 2)

let () =
  let m = new_tmap () in
  atomically_exn (tmap_put m "x" 10);
  atomically_exn (tmap_put m "x" 20);
  let v = atomically_exn (tmap_get m "x") in
  assert_test "tmap put overwrites"
    (v = Some 20)

let () =
  let m = new_tmap () in
  atomically_exn (tmap_put m "x" 10);
  atomically_exn (tmap_delete m "x");
  let v = atomically_exn (tmap_get m "x") in
  assert_test "tmap delete"
    (v = None)


(* ════════════════════════════════════════════════════════════════
   Conflict detection
   ════════════════════════════════════════════════════════════════ *)

let () = Printf.printf "\n── Conflict Detection ──\n"

let () =
  let tv = new_tvar 0 in
  let result = simulate_conflict tv 999 777 in
  assert_test "external modify causes conflict"
    (match result with Conflict -> true | _ -> false)

let () =
  let tv = new_tvar 100 in
  let _ = simulate_two_transactions tv (fun v -> v + 50) (fun v -> v * 2) in
  assert_test "second tx wins in interleave"
    (read_tvar_raw tv = 200)

let () =
  let log = empty_log () in
  let tv = new_tvar 42 in
  let _ = (read_tvar tv) log in
  let _ = (write_tvar tv 99) log in
  let result = commit log in
  assert_test "commit succeeds without external changes"
    (match result with Committed -> true | _ -> false);
  assert_test "value updated after commit"
    (read_tvar_raw tv = 99)

let () =
  let log = empty_log () in
  let result = commit log in
  assert_test "empty log commits successfully"
    (match result with Committed -> true | _ -> false)


(* ════════════════════════════════════════════════════════════════
   Statistics
   ════════════════════════════════════════════════════════════════ *)

let () = Printf.printf "\n── Statistics ──\n"

let () =
  reset_stats ();
  let c = new_counter 0 in
  for _ = 1 to 50 do
    ignore (atomically_tracked (increment c))
  done;
  let (commits, _, _) = get_stats () in
  assert_test "50 increments = 50 commits"
    (commits = 50);
  assert_test "counter value is 50"
    (atomically_exn (get_counter c) = 50)

let () =
  reset_stats ();
  ignore (atomically_tracked stm_retry);
  let (_, _, retries) = get_stats () in
  assert_test "retry tracked in stats"
    (retries = 1)

let () =
  let c = new_counter 0 in
  atomically_exn (increment c);
  atomically_exn (increment c);
  atomically_exn (decrement c);
  assert_test "increment + increment + decrement = 1"
    (atomically_exn (get_counter c) = 1)


(* ════════════════════════════════════════════════════════════════
   Edge cases
   ════════════════════════════════════════════════════════════════ *)

let () = Printf.printf "\n── Edge Cases ──\n"

let () =
  let tv = new_tvar "hello" in
  let v = atomically_exn (read_tvar tv) in
  assert_test "TVar with string type"
    (v = "hello")

let () =
  let tv = new_tvar [] in
  atomically_exn (modify_tvar tv (fun lst -> 1 :: 2 :: 3 :: lst));
  let v = atomically_exn (read_tvar tv) in
  assert_test "TVar with list type"
    (v = [1; 2; 3])

let () =
  let tv = new_tvar 0 in
  for i = 1 to 100 do
    atomically_exn (write_tvar tv i)
  done;
  assert_test "100 sequential atomic writes"
    (read_tvar_raw tv = 100)

let () =
  let ch = new_channel 100 in
  for i = 1 to 50 do
    atomically_exn (send ch i)
  done;
  let sum = ref 0 in
  for _ = 1 to 50 do
    sum := !sum + atomically_exn (receive ch)
  done;
  assert_test "channel preserves all 50 messages"
    (!sum = 50 * 51 / 2)  (* sum 1..50 = 1275 *)

let () =
  let a = new_account "A" 0 in
  atomically_exn (deposit a 0);
  assert_test "zero deposit is fine"
    (atomically_exn (get_balance a) = 0)

let () =
  let result = atomically (stm_return 42) in
  assert_test "pure return always commits"
    (match result with Value 42 -> true | _ -> false)

let () =
  try
    ignore (atomically_exn stm_retry);
    assert_test "atomically_exn raises on retry" false
  with Stm_retry ->
    assert_test "atomically_exn raises on retry" true


(* ════════════════════════════════════════════════════════════════
   Composite transactions
   ════════════════════════════════════════════════════════════════ *)

let () = Printf.printf "\n── Composite Transactions ──\n"

let () =
  let a = new_account "A" 1000 in
  let b = new_account "B" 1000 in
  let c = new_account "C" 0 in
  (* Multi-hop: A→B→C in one atomic block *)
  let multi_transfer = stm_bind (transfer a b 300) (fun () ->
    transfer b c 200) in
  atomically_exn multi_transfer;
  let ba = atomically_exn (get_balance a) in
  let bb = atomically_exn (get_balance b) in
  let bc = atomically_exn (get_balance c) in
  assert_test "multi-hop transfer preserves total"
    (ba + bb + bc = 2000 && ba = 700 && bb = 1100 && bc = 200)

let () =
  (* Atomic swap of two TVars *)
  let x = new_tvar 10 in
  let y = new_tvar 20 in
  let swap =
    stm_bind (read_tvar x) (fun vx ->
    stm_bind (read_tvar y) (fun vy ->
    stm_seq (write_tvar x vy) (write_tvar y vx))) in
  atomically_exn swap;
  assert_test "atomic swap"
    (read_tvar_raw x = 20 && read_tvar_raw y = 10)


(* ════════════════════════════════════════════════════════════════ *)

let () =
  print_results ();
  if !tests_failed > 0 then exit 1
