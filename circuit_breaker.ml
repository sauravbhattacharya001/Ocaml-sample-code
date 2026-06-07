(* circuit_breaker.ml — Circuit Breaker pattern for fault-tolerant service calls.
 *
 * Implements the standard three-state circuit breaker (Closed → Open → Half-Open)
 * with configurable failure thresholds, recovery timeouts, and half-open probe limits.
 *
 * Features:
 *   - Token-bucket style failure counting with sliding window
 *   - Configurable failure_threshold, recovery_timeout, half_open_max_probes
 *   - Call wrapping with automatic state transitions
 *   - Manual reset/trip controls
 *   - Statistics tracking (total_calls, successes, failures, rejections, trips)
 *   - Multiple independent breakers via create/name registry
 *   - Event callbacks (on_trip, on_reset, on_half_open)
 *   - Exponential backoff on repeated trips (optional)
 *   - Health check probe support in half-open state
 *
 * Usage:
 *   let cb = CircuitBreaker.create ~failure_threshold:5 ~recovery_timeout:30.0 () in
 *   match CircuitBreaker.call cb (fun () -> do_risky_operation ()) with
 *   | Ok result -> handle_success result
 *   | Error `Circuit_open -> handle_rejection ()
 *   | Error (`Call_failed exn) -> handle_failure exn
 *)

module CircuitBreaker = struct
  type state =
    | Closed
    | Open
    | Half_open

  type stats = {
    mutable total_calls: int;
    mutable successes: int;
    mutable failures: int;
    mutable rejections: int;
    mutable trips: int;
    mutable last_trip_time: float option;
    mutable last_success_time: float option;
    mutable last_failure_time: float option;
    mutable consecutive_successes: int;
    mutable consecutive_failures: int;
  }

  type config = {
    failure_threshold: int;
    recovery_timeout: float;
    half_open_max_probes: int;
    window_size: float;
    backoff_multiplier: float;
    max_backoff: float;
    name: string;
  }

  type event =
    | Tripped of { name: string; failures: int; time: float }
    | Reset of { name: string; time: float }
    | Half_opened of { name: string; time: float }
    | Call_succeeded of { name: string; time: float }
    | Call_failed of { name: string; time: float; exn: exn option }
    | Call_rejected of { name: string; time: float }

  type callback = event -> unit

  type failure_record = {
    timestamp: float;
  }

  type t = {
    config: config;
    mutable state: state;
    mutable failures_in_window: failure_record list;
    mutable half_open_probes: int;
    mutable opened_at: float option;
    mutable trip_count: int;
    stats: stats;
    mutable callbacks: callback list;
    mutable now_fn: unit -> float;
  }

  let default_config = {
    failure_threshold = 5;
    recovery_timeout = 30.0;
    half_open_max_probes = 3;
    window_size = 60.0;
    backoff_multiplier = 1.5;
    max_backoff = 300.0;
    name = "default";
  }

  let make_stats () = {
    total_calls = 0;
    successes = 0;
    failures = 0;
    rejections = 0;
    trips = 0;
    last_trip_time = None;
    last_success_time = None;
    last_failure_time = None;
    consecutive_successes = 0;
    consecutive_failures = 0;
  }

  let create
      ?(failure_threshold = 5)
      ?(recovery_timeout = 30.0)
      ?(half_open_max_probes = 3)
      ?(window_size = 60.0)
      ?(backoff_multiplier = 1.5)
      ?(max_backoff = 300.0)
      ?(name = "default")
      ?(now_fn = Sys.time)
      () =
    {
      config = {
        failure_threshold;
        recovery_timeout;
        half_open_max_probes;
        window_size;
        backoff_multiplier;
        max_backoff;
        name;
      };
      state = Closed;
      failures_in_window = [];
      half_open_probes = 0;
      opened_at = None;
      trip_count = 0;
      stats = make_stats ();
      callbacks = [];
      now_fn;
    }

  let state_to_string = function
    | Closed -> "closed"
    | Open -> "open"
    | Half_open -> "half_open"

  let get_state cb = cb.state
  let get_stats cb = cb.stats
  let get_config cb = cb.config
  let get_name cb = cb.config.name

  let on_event cb f =
    cb.callbacks <- f :: cb.callbacks

  let emit cb event =
    List.iter (fun f -> f event) cb.callbacks

  (* Prune failures outside the sliding window *)
  let prune_window cb now =
    let cutoff = now -. cb.config.window_size in
    cb.failures_in_window <-
      List.filter (fun r -> r.timestamp > cutoff) cb.failures_in_window

  let failures_in_window cb =
    let now = cb.now_fn () in
    prune_window cb now;
    List.length cb.failures_in_window

  (* Calculate effective recovery timeout with exponential backoff *)
  let effective_timeout cb =
    if cb.trip_count <= 1 then cb.config.recovery_timeout
    else
      let mult = cb.config.backoff_multiplier ** (float_of_int (cb.trip_count - 1)) in
      Float.min cb.config.max_backoff (cb.config.recovery_timeout *. mult)

  (* Transition to open state *)
  let trip cb now =
    cb.state <- Open;
    cb.opened_at <- Some now;
    cb.trip_count <- cb.trip_count + 1;
    cb.half_open_probes <- 0;
    cb.stats.trips <- cb.stats.trips + 1;
    cb.stats.last_trip_time <- Some now;
    emit cb (Tripped { name = cb.config.name; failures = failures_in_window cb; time = now })

  (* Transition to half-open state *)
  let enter_half_open cb now =
    cb.state <- Half_open;
    cb.half_open_probes <- 0;
    emit cb (Half_opened { name = cb.config.name; time = now })

  (* Reset to closed state *)
  let reset cb =
    let now = cb.now_fn () in
    cb.state <- Closed;
    cb.failures_in_window <- [];
    cb.half_open_probes <- 0;
    cb.opened_at <- None;
    cb.trip_count <- 0;
    cb.stats.consecutive_failures <- 0;
    emit cb (Reset { name = cb.config.name; time = now })

  (* Manually trip the breaker *)
  let manual_trip cb =
    let now = cb.now_fn () in
    trip cb now

  let record_success cb =
    let now = cb.now_fn () in
    cb.stats.successes <- cb.stats.successes + 1;
    cb.stats.last_success_time <- Some now;
    cb.stats.consecutive_successes <- cb.stats.consecutive_successes + 1;
    cb.stats.consecutive_failures <- 0;
    emit cb (Call_succeeded { name = cb.config.name; time = now });
    match cb.state with
    | Half_open ->
      cb.half_open_probes <- cb.half_open_probes + 1;
      if cb.half_open_probes >= cb.config.half_open_max_probes then
        reset cb
    | _ -> ()

  let record_failure cb exn_opt =
    let now = cb.now_fn () in
    cb.stats.failures <- cb.stats.failures + 1;
    cb.stats.last_failure_time <- Some now;
    cb.stats.consecutive_failures <- cb.stats.consecutive_failures + 1;
    cb.stats.consecutive_successes <- 0;
    cb.failures_in_window <- { timestamp = now } :: cb.failures_in_window;
    prune_window cb now;
    emit cb (Call_failed { name = cb.config.name; time = now; exn = exn_opt });
    match cb.state with
    | Half_open ->
      (* Any failure in half-open immediately re-trips *)
      trip cb now
    | Closed ->
      if List.length cb.failures_in_window >= cb.config.failure_threshold then
        trip cb now
    | Open -> ()

  (* Check if the breaker should allow a call *)
  let should_allow cb =
    let now = cb.now_fn () in
    match cb.state with
    | Closed -> true
    | Open ->
      (match cb.opened_at with
       | None -> true  (* shouldn't happen, but be safe *)
       | Some opened ->
         let timeout = effective_timeout cb in
         if now -. opened >= timeout then begin
           enter_half_open cb now;
           true
         end else
           false)
    | Half_open ->
      cb.half_open_probes < cb.config.half_open_max_probes

  (* Main call wrapper *)
  let call cb f =
    cb.stats.total_calls <- cb.stats.total_calls + 1;
    if should_allow cb then begin
      match f () with
      | result ->
        record_success cb;
        Ok result
      | exception exn ->
        record_failure cb (Some exn);
        Error (`Call_failed exn)
    end else begin
      let now = cb.now_fn () in
      cb.stats.rejections <- cb.stats.rejections + 1;
      emit cb (Call_rejected { name = cb.config.name; time = now });
      Error `Circuit_open
    end

  (* Call with a fallback when circuit is open *)
  let call_with_fallback cb ~fallback f =
    match call cb f with
    | Error `Circuit_open -> Ok (fallback ())
    | other -> other

  (* Health check probe — used in half-open to test service recovery *)
  let probe cb health_check_fn =
    if cb.state <> Half_open && cb.state <> Open then
      Ok `Already_closed
    else begin
      let now = cb.now_fn () in
      if cb.state = Open then begin
        match cb.opened_at with
        | Some opened when now -. opened >= effective_timeout cb ->
          enter_half_open cb now
        | _ -> ()
      end;
      if cb.state = Half_open then begin
        match health_check_fn () with
        | true ->
          record_success cb;
          Ok `Probe_passed
        | false ->
          record_failure cb None;
          Ok `Probe_failed
        | exception exn ->
          record_failure cb (Some exn);
          Ok `Probe_failed
      end else
        Error `Circuit_open
    end

  (* --- Reporting --- *)

  let to_record cb =
    let fw = failures_in_window cb in
    [
      ("name", cb.config.name);
      ("state", state_to_string cb.state);
      ("failures_in_window", string_of_int fw);
      ("failure_threshold", string_of_int cb.config.failure_threshold);
      ("recovery_timeout", Printf.sprintf "%.1f" cb.config.recovery_timeout);
      ("effective_timeout", Printf.sprintf "%.1f" (effective_timeout cb));
      ("trip_count", string_of_int cb.trip_count);
      ("total_calls", string_of_int cb.stats.total_calls);
      ("successes", string_of_int cb.stats.successes);
      ("failures", string_of_int cb.stats.failures);
      ("rejections", string_of_int cb.stats.rejections);
      ("consecutive_successes", string_of_int cb.stats.consecutive_successes);
      ("consecutive_failures", string_of_int cb.stats.consecutive_failures);
    ]

  let to_text cb =
    let pairs = to_record cb in
    String.concat "\n"
      (List.map (fun (k, v) -> Printf.sprintf "  %s: %s" k v) pairs)

  let to_markdown cb =
    let pairs = to_record cb in
    let header = Printf.sprintf "## Circuit Breaker: %s\n" cb.config.name in
    let state_line = Printf.sprintf "**State:** `%s`\n" (state_to_string cb.state) in
    let table_header = "| Metric | Value |\n|--------|-------|\n" in
    let rows = List.map (fun (k, v) -> Printf.sprintf "| %s | %s |" k v) pairs in
    header ^ state_line ^ "\n" ^ table_header ^ String.concat "\n" rows ^ "\n"

  let to_json cb =
    let pairs = to_record cb in
    let entries = List.map (fun (k, v) ->
      Printf.sprintf "  \"%s\": \"%s\"" k v
    ) pairs in
    "{\n" ^ String.concat ",\n" entries ^ "\n}"
end

(* --- Registry: manage multiple named breakers --- *)

module Registry = struct
  let breakers : (string, CircuitBreaker.t) Hashtbl.t = Hashtbl.create 16

  let get_or_create ?(failure_threshold = 5) ?(recovery_timeout = 30.0)
      ?(half_open_max_probes = 3) ?(window_size = 60.0)
      ?(backoff_multiplier = 1.5) ?(max_backoff = 300.0) ?now_fn name =
    match Hashtbl.find_opt breakers name with
    | Some cb -> cb
    | None ->
      let now_fn = match now_fn with Some f -> f | None -> Sys.time in
      let cb = CircuitBreaker.create
          ~failure_threshold ~recovery_timeout ~half_open_max_probes
          ~window_size ~backoff_multiplier ~max_backoff ~name ~now_fn () in
      Hashtbl.replace breakers name cb;
      cb

  let find name = Hashtbl.find_opt breakers name

  let remove name = Hashtbl.remove breakers name

  let reset_all () = Hashtbl.iter (fun _ cb -> CircuitBreaker.reset cb) breakers

  let clear () = Hashtbl.clear breakers

  let list_all () =
    Hashtbl.fold (fun name cb acc -> (name, cb) :: acc) breakers []

  let summary () =
    let all = list_all () in
    let sorted = List.sort (fun (a, _) (b, _) -> String.compare a b) all in
    List.map (fun (name, cb) ->
      Printf.sprintf "[%s] state=%s failures=%d trips=%d"
        name
        (CircuitBreaker.state_to_string (CircuitBreaker.get_state cb))
        (CircuitBreaker.failures_in_window cb)
        (CircuitBreaker.get_stats cb).trips
    ) sorted
end

(* --- Demo --- *)

let () =
  Printf.printf "=== Circuit Breaker Demo ===\n\n";

  (* Create a breaker with low thresholds for demo *)
  let time = ref 0.0 in
  let now_fn () = !time in

  let cb = CircuitBreaker.create
      ~failure_threshold:3
      ~recovery_timeout:10.0
      ~half_open_max_probes:2
      ~window_size:60.0
      ~backoff_multiplier:2.0
      ~name:"payment-service"
      ~now_fn
      () in

  (* Register event callback *)
  CircuitBreaker.on_event cb (fun event ->
    match event with
    | CircuitBreaker.Tripped { name; failures; _ } ->
      Printf.printf "  [EVENT] %s TRIPPED (failures=%d)\n" name failures
    | CircuitBreaker.Reset { name; _ } ->
      Printf.printf "  [EVENT] %s RESET\n" name
    | CircuitBreaker.Half_opened { name; _ } ->
      Printf.printf "  [EVENT] %s HALF-OPEN\n" name
    | _ -> ()
  );

  (* Simulate successful calls *)
  Printf.printf "--- Phase 1: Successful calls ---\n";
  for _ = 1 to 3 do
    time := !time +. 1.0;
    let result = CircuitBreaker.call cb (fun () -> "ok") in
    (match result with
     | Ok v -> Printf.printf "  Call succeeded: %s\n" v
     | Error _ -> Printf.printf "  Call failed\n")
  done;

  (* Simulate failures to trip the breaker *)
  Printf.printf "\n--- Phase 2: Failures trigger trip ---\n";
  for i = 1 to 4 do
    time := !time +. 1.0;
    let result = CircuitBreaker.call cb (fun () -> failwith "service down") in
    (match result with
     | Ok _ -> Printf.printf "  Call %d succeeded\n" i
     | Error `Circuit_open -> Printf.printf "  Call %d rejected (circuit open)\n" i
     | Error (`Call_failed exn) ->
       Printf.printf "  Call %d failed: %s\n" i (Printexc.to_string exn))
  done;

  (* Verify calls are rejected while open *)
  Printf.printf "\n--- Phase 3: Calls rejected while open ---\n";
  time := !time +. 2.0;
  for _ = 1 to 2 do
    let result = CircuitBreaker.call cb (fun () -> "won't reach") in
    (match result with
     | Error `Circuit_open -> Printf.printf "  Rejected (circuit open)\n"
     | _ -> Printf.printf "  Unexpected result\n")
  done;

  (* Call with fallback *)
  Printf.printf "\n--- Phase 4: Fallback while open ---\n";
  let result = CircuitBreaker.call_with_fallback cb
      ~fallback:(fun () -> "cached-value")
      (fun () -> "fresh-value") in
  (match result with
   | Ok v -> Printf.printf "  Got fallback: %s\n" v
   | Error _ -> Printf.printf "  Unexpected error\n");

  (* Wait for recovery timeout and try half-open probes *)
  Printf.printf "\n--- Phase 5: Recovery after timeout ---\n";
  time := !time +. 15.0;  (* past recovery_timeout of 10s *)

  (* First probe in half-open succeeds *)
  let result = CircuitBreaker.call cb (fun () -> "recovered!") in
  (match result with
   | Ok v -> Printf.printf "  Half-open probe 1 succeeded: %s\n" v
   | Error _ -> Printf.printf "  Probe failed\n");

  (* Second probe completes reset *)
  let result = CircuitBreaker.call cb (fun () -> "fully back") in
  (match result with
   | Ok v -> Printf.printf "  Half-open probe 2 succeeded: %s\n" v
   | Error _ -> Printf.printf "  Probe failed\n");

  Printf.printf "  State after recovery: %s\n"
    (CircuitBreaker.state_to_string (CircuitBreaker.get_state cb));

  (* Trip again to show exponential backoff *)
  Printf.printf "\n--- Phase 6: Re-trip with exponential backoff ---\n";
  for _ = 1 to 3 do
    time := !time +. 1.0;
    ignore (CircuitBreaker.call cb (fun () -> failwith "down again"))
  done;
  Printf.printf "  Effective timeout (trip #2): %.1fs\n"
    (CircuitBreaker.effective_timeout cb);

  (* Show reporting *)
  Printf.printf "\n--- Stats (text) ---\n%s\n" (CircuitBreaker.to_text cb);
  Printf.printf "\n--- Stats (JSON) ---\n%s\n" (CircuitBreaker.to_json cb);

  (* Registry demo *)
  Printf.printf "\n--- Phase 7: Registry ---\n";
  let _auth = Registry.get_or_create ~failure_threshold:10 ~now_fn "auth-service" in
  let _db = Registry.get_or_create ~failure_threshold:3 ~now_fn "db-service" in
  ignore (CircuitBreaker.call _auth (fun () -> "auth ok"));
  ignore (CircuitBreaker.call _db (fun () -> failwith "timeout"));
  List.iter (fun s -> Printf.printf "  %s\n" s) (Registry.summary ());

  Printf.printf "\nDone.\n"
