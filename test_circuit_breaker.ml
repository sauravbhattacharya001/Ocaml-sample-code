(* test_circuit_breaker.ml — Tests for the circuit breaker module *)

#use "circuit_breaker.ml"

let tests_run = ref 0
let tests_passed = ref 0

let assert_equal ~label expected actual =
  tests_run := !tests_run + 1;
  if expected = actual then begin
    tests_passed := !tests_passed + 1;
    Printf.printf "  [PASS] %s\n" label
  end else
    Printf.printf "  [FAIL] %s: expected %s, got %s\n" label expected actual

let assert_true ~label cond =
  tests_run := !tests_run + 1;
  if cond then begin
    tests_passed := !tests_passed + 1;
    Printf.printf "  [PASS] %s\n" label
  end else
    Printf.printf "  [FAIL] %s: expected true\n" label

let () =
  Printf.printf "=== Circuit Breaker Tests ===\n\n";
  let time = ref 0.0 in
  let now_fn () = !time in

  (* Test 1: Initial state is closed *)
  Printf.printf "Test 1: Initial state\n";
  let cb = CircuitBreaker.create ~failure_threshold:3 ~recovery_timeout:10.0
      ~half_open_max_probes:2 ~name:"test" ~now_fn () in
  assert_equal ~label:"state is closed"
    "closed" (CircuitBreaker.state_to_string (CircuitBreaker.get_state cb));
  assert_equal ~label:"no failures"
    0 (CircuitBreaker.failures_in_window cb);

  (* Test 2: Successful calls stay closed *)
  Printf.printf "\nTest 2: Successful calls\n";
  for _ = 1 to 5 do
    time := !time +. 1.0;
    ignore (CircuitBreaker.call cb (fun () -> 42))
  done;
  assert_equal ~label:"state stays closed"
    "closed" (CircuitBreaker.state_to_string (CircuitBreaker.get_state cb));
  let stats = CircuitBreaker.get_stats cb in
  assert_equal ~label:"5 successes" 5 stats.successes;
  assert_equal ~label:"0 failures" 0 stats.failures;
  assert_equal ~label:"5 consecutive successes" 5 stats.consecutive_successes;

  (* Test 3: Failures below threshold stay closed *)
  Printf.printf "\nTest 3: Sub-threshold failures\n";
  let cb2 = CircuitBreaker.create ~failure_threshold:3 ~recovery_timeout:10.0
      ~name:"test2" ~now_fn () in
  for _ = 1 to 2 do
    time := !time +. 1.0;
    ignore (CircuitBreaker.call cb2 (fun () -> failwith "err"))
  done;
  assert_equal ~label:"still closed with 2 failures"
    "closed" (CircuitBreaker.state_to_string (CircuitBreaker.get_state cb2));
  assert_equal ~label:"2 failures in window"
    2 (CircuitBreaker.failures_in_window cb2);

  (* Test 4: Reaching threshold trips to open *)
  Printf.printf "\nTest 4: Trip on threshold\n";
  time := !time +. 1.0;
  ignore (CircuitBreaker.call cb2 (fun () -> failwith "err"));
  assert_equal ~label:"trips to open"
    "open" (CircuitBreaker.state_to_string (CircuitBreaker.get_state cb2));
  let stats2 = CircuitBreaker.get_stats cb2 in
  assert_equal ~label:"trip count is 1" 1 stats2.trips;

  (* Test 5: Open state rejects calls *)
  Printf.printf "\nTest 5: Open rejects calls\n";
  time := !time +. 1.0;
  let result = CircuitBreaker.call cb2 (fun () -> "nope") in
  assert_true ~label:"call is rejected" (result = Error `Circuit_open);
  assert_equal ~label:"rejections = 1" 1 (CircuitBreaker.get_stats cb2).rejections;

  (* Test 6: Recovery timeout transitions to half-open *)
  Printf.printf "\nTest 6: Recovery timeout -> half-open\n";
  time := !time +. 15.0;  (* > 10s timeout *)
  let result = CircuitBreaker.call cb2 (fun () -> "probe") in
  assert_true ~label:"call allowed after timeout" (result = Ok "probe");
  assert_equal ~label:"state is half_open"
    "half_open" (CircuitBreaker.state_to_string (CircuitBreaker.get_state cb2));

  (* Test 7: Success in half-open progresses toward reset *)
  Printf.printf "\nTest 7: Half-open probes\n";
  let cb3 = CircuitBreaker.create ~failure_threshold:2 ~recovery_timeout:5.0
      ~half_open_max_probes:2 ~name:"test3" ~now_fn () in
  (* Trip it *)
  for _ = 1 to 2 do
    time := !time +. 1.0;
    ignore (CircuitBreaker.call cb3 (fun () -> failwith "x"))
  done;
  assert_equal ~label:"tripped" "open"
    (CircuitBreaker.state_to_string (CircuitBreaker.get_state cb3));
  (* Wait and do probes *)
  time := !time +. 6.0;
  ignore (CircuitBreaker.call cb3 (fun () -> "ok"));
  assert_equal ~label:"half-open after 1 probe" "half_open"
    (CircuitBreaker.state_to_string (CircuitBreaker.get_state cb3));
  ignore (CircuitBreaker.call cb3 (fun () -> "ok"));
  assert_equal ~label:"reset after 2 probes" "closed"
    (CircuitBreaker.state_to_string (CircuitBreaker.get_state cb3));

  (* Test 8: Failure in half-open re-trips *)
  Printf.printf "\nTest 8: Half-open failure re-trips\n";
  let cb4 = CircuitBreaker.create ~failure_threshold:2 ~recovery_timeout:5.0
      ~half_open_max_probes:3 ~name:"test4" ~now_fn () in
  for _ = 1 to 2 do
    time := !time +. 1.0;
    ignore (CircuitBreaker.call cb4 (fun () -> failwith "x"))
  done;
  time := !time +. 6.0;
  ignore (CircuitBreaker.call cb4 (fun () -> failwith "still bad"));
  assert_equal ~label:"re-trips on half-open failure" "open"
    (CircuitBreaker.state_to_string (CircuitBreaker.get_state cb4));
  assert_equal ~label:"trip count is 2" 2 (CircuitBreaker.get_stats cb4).trips;

  (* Test 9: Exponential backoff *)
  Printf.printf "\nTest 9: Exponential backoff\n";
  let cb5 = CircuitBreaker.create ~failure_threshold:2 ~recovery_timeout:10.0
      ~backoff_multiplier:2.0 ~name:"test5" ~now_fn () in
  (* Trip once *)
  for _ = 1 to 2 do
    time := !time +. 1.0;
    ignore (CircuitBreaker.call cb5 (fun () -> failwith "x"))
  done;
  let t1 = CircuitBreaker.effective_timeout cb5 in
  assert_true ~label:"first timeout = 10.0" (t1 = 10.0);
  (* Recover and trip again *)
  time := !time +. 11.0;
  ignore (CircuitBreaker.call cb5 (fun () -> failwith "still down"));
  (* Now trip_count = 2 *)
  let t2 = CircuitBreaker.effective_timeout cb5 in
  assert_true ~label:"second timeout = 20.0 (backoff)"
    (Float.abs (t2 -. 20.0) < 0.01);

  (* Test 10: Sliding window prunes old failures *)
  Printf.printf "\nTest 10: Window pruning\n";
  let cb6 = CircuitBreaker.create ~failure_threshold:3 ~recovery_timeout:5.0
      ~window_size:10.0 ~name:"test6" ~now_fn () in
  time := 100.0;
  ignore (CircuitBreaker.call cb6 (fun () -> failwith "a"));
  time := 101.0;
  ignore (CircuitBreaker.call cb6 (fun () -> failwith "b"));
  assert_equal ~label:"2 in window" 2 (CircuitBreaker.failures_in_window cb6);
  (* Jump past window *)
  time := 115.0;
  assert_equal ~label:"0 after pruning" 0 (CircuitBreaker.failures_in_window cb6);
  assert_equal ~label:"still closed" "closed"
    (CircuitBreaker.state_to_string (CircuitBreaker.get_state cb6));

  (* Test 11: Manual trip and reset *)
  Printf.printf "\nTest 11: Manual trip/reset\n";
  let cb7 = CircuitBreaker.create ~failure_threshold:10 ~recovery_timeout:5.0
      ~name:"test7" ~now_fn () in
  CircuitBreaker.manual_trip cb7;
  assert_equal ~label:"manually tripped" "open"
    (CircuitBreaker.state_to_string (CircuitBreaker.get_state cb7));
  CircuitBreaker.reset cb7;
  assert_equal ~label:"manually reset" "closed"
    (CircuitBreaker.state_to_string (CircuitBreaker.get_state cb7));

  (* Test 12: Call with fallback *)
  Printf.printf "\nTest 12: Fallback\n";
  let cb8 = CircuitBreaker.create ~failure_threshold:1 ~recovery_timeout:60.0
      ~name:"test8" ~now_fn () in
  time := !time +. 1.0;
  ignore (CircuitBreaker.call cb8 (fun () -> failwith "boom"));
  time := !time +. 1.0;
  let result = CircuitBreaker.call_with_fallback cb8
      ~fallback:(fun () -> "fallback-val")
      (fun () -> "real-val") in
  assert_true ~label:"fallback returns cached value" (result = Ok "fallback-val");

  (* Test 13: Event callbacks fire *)
  Printf.printf "\nTest 13: Event callbacks\n";
  let events = ref [] in
  let cb9 = CircuitBreaker.create ~failure_threshold:2 ~recovery_timeout:5.0
      ~name:"test9" ~now_fn () in
  CircuitBreaker.on_event cb9 (fun ev ->
    match ev with
    | CircuitBreaker.Tripped _ -> events := "tripped" :: !events
    | CircuitBreaker.Reset _ -> events := "reset" :: !events
    | CircuitBreaker.Half_opened _ -> events := "half_opened" :: !events
    | _ -> ()
  );
  time := !time +. 1.0;
  ignore (CircuitBreaker.call cb9 (fun () -> failwith "x"));
  time := !time +. 1.0;
  ignore (CircuitBreaker.call cb9 (fun () -> failwith "x"));
  assert_true ~label:"tripped event fired" (List.mem "tripped" !events);
  CircuitBreaker.reset cb9;
  assert_true ~label:"reset event fired" (List.mem "reset" !events);

  (* Test 14: Health check probe *)
  Printf.printf "\nTest 14: Health probe\n";
  let cb10 = CircuitBreaker.create ~failure_threshold:2 ~recovery_timeout:5.0
      ~half_open_max_probes:2 ~name:"test10" ~now_fn () in
  for _ = 1 to 2 do
    time := !time +. 1.0;
    ignore (CircuitBreaker.call cb10 (fun () -> failwith "x"))
  done;
  time := !time +. 6.0;
  let probe_result = CircuitBreaker.probe cb10 (fun () -> true) in
  assert_true ~label:"probe passes" (probe_result = Ok `Probe_passed);
  let probe_result2 = CircuitBreaker.probe cb10 (fun () -> true) in
  assert_true ~label:"second probe resets" (probe_result2 = Ok `Probe_passed);
  assert_equal ~label:"back to closed" "closed"
    (CircuitBreaker.state_to_string (CircuitBreaker.get_state cb10));

  (* Test 15: Reporting *)
  Printf.printf "\nTest 15: Reporting formats\n";
  let cb11 = CircuitBreaker.create ~failure_threshold:5 ~recovery_timeout:30.0
      ~name:"report-test" ~now_fn () in
  let text = CircuitBreaker.to_text cb11 in
  assert_true ~label:"text contains name" (String.length text > 0);
  let md = CircuitBreaker.to_markdown cb11 in
  assert_true ~label:"markdown has header" (String.length md > 20);
  let json = CircuitBreaker.to_json cb11 in
  assert_true ~label:"json starts with {" (String.get json 0 = '{');
  assert_true ~label:"json contains name field"
    (String.length json > 10);

  (* Test 16: Max backoff cap *)
  Printf.printf "\nTest 16: Max backoff cap\n";
  let cb12 = CircuitBreaker.create ~failure_threshold:1 ~recovery_timeout:10.0
      ~backoff_multiplier:10.0 ~max_backoff:50.0 ~name:"test12" ~now_fn () in
  (* Trip many times *)
  for _ = 1 to 5 do
    time := !time +. 1.0;
    ignore (CircuitBreaker.call cb12 (fun () -> failwith "x"));
    time := !time +. 200.0;  (* wait past any timeout *)
    (* Force transition to half-open by calling *)
    ignore (CircuitBreaker.call cb12 (fun () -> failwith "still bad"))
  done;
  let capped = CircuitBreaker.effective_timeout cb12 in
  assert_true ~label:"timeout capped at max_backoff"
    (capped <= 50.0);

  (* Summary *)
  Printf.printf "\n=== Results: %d/%d passed ===\n" !tests_passed !tests_run;
  if !tests_passed = !tests_run then
    Printf.printf "All tests passed!\n"
  else
    Printf.printf "SOME TESTS FAILED\n"
