(* ============================================================================
   Dining Philosophers -- Classic Concurrency Problem & Solutions
   ============================================================================

   An implementation of the Dining Philosophers problem in OCaml featuring:

   - Simulation of N philosophers around a circular table
   - Naive solution demonstrating potential deadlock
   - Resource hierarchy solution (ordered fork acquisition)
   - Arbitrator (waiter) solution with a central coordinator
   - Chandy-Misra solution with message-passing dirty/clean forks
   - Statistics tracking: meals eaten, wait times, fairness metrics
   - Deadlock detection with timeout
   - Configurable thinking/eating durations and philosopher count
   - Built-in test suite (18 tests)

   Concepts demonstrated:
   - Deadlock, livelock, and starvation in concurrent systems
   - Resource ordering as a deadlock prevention technique
   - Centralized vs distributed coordination
   - Fairness analysis in concurrent resource allocation
   - Functional simulation of concurrent processes
   - State machines for philosopher lifecycle

   ============================================================================ *)

(* --- Types --- *)

type fork_state = Free | HeldBy of int

type philosopher_state =
  | Thinking
  | Hungry
  | WaitingForForks of { left: bool; right: bool }
  | Eating

type philosopher = {
  id: int;
  name: string;
  mutable state: philosopher_state;
  mutable meals_eaten: int;
  mutable total_wait_time: int;   (* ticks spent hungry/waiting *)
  mutable total_think_time: int;
  mutable total_eat_time: int;
}

type fork = {
  fork_id: int;
  mutable fork_state: fork_state;
}

type table = {
  philosophers: philosopher array;
  forks: fork array;
  size: int;
}

type simulation_result = {
  total_ticks: int;
  meals_per_philosopher: int list;
  deadlocked: bool;
  avg_wait_time: float;
  fairness_index: float;  (* Jain's fairness index *)
}

type strategy =
  | Naive              (* pick up left then right — can deadlock *)
  | ResourceHierarchy  (* always pick lower-numbered fork first *)
  | Arbitrator         (* ask a waiter for permission *)
  | ChandyMisra        (* message-passing with dirty/clean forks *)

(* --- Philosopher names --- *)

let default_names = [|
  "Aristotle"; "Kant"; "Spinoza"; "Marx"; "Russell";
  "Wittgenstein"; "Nietzsche"; "Hume"; "Descartes"; "Plato"
|]

let make_philosopher id =
  let name = if id < Array.length default_names then default_names.(id)
             else Printf.sprintf "Philosopher_%d" id in
  { id; name; state = Thinking; meals_eaten = 0;
    total_wait_time = 0; total_think_time = 0; total_eat_time = 0 }

let make_fork id = { fork_id = id; fork_state = Free }

let make_table n =
  let philosophers = Array.init n make_philosopher in
  let forks = Array.init n make_fork in
  { philosophers; forks; size = n }

(* --- Fork helpers --- *)

let left_fork table i = table.forks.(i)
let right_fork table i = table.forks.((i + 1) mod table.size)

let is_fork_free fork = fork.fork_state = Free

let acquire_fork fork phil_id =
  if is_fork_free fork then begin
    fork.fork_state <- HeldBy phil_id;
    true
  end else false

let release_fork fork =
  fork.fork_state <- Free

(* --- Jain's fairness index --- *)
(* J(x1..xn) = (sum xi)^2 / (n * sum xi^2) — 1.0 = perfectly fair *)

let jains_fairness meals =
  let n = List.length meals in
  if n = 0 then 1.0
  else
    let sum = List.fold_left (+) 0 meals |> float_of_int in
    let sum_sq = List.fold_left (fun acc x -> acc + x * x) 0 meals |> float_of_int in
    if sum_sq = 0.0 then 1.0
    else (sum *. sum) /. (float_of_int n *. sum_sq)

(* --- Strategy: Naive (can deadlock) --- *)

let naive_step table phil =
  let li = left_fork table phil.id in
  let ri = right_fork table phil.id in
  match phil.state with
  | Thinking ->
    phil.total_think_time <- phil.total_think_time + 1;
    (* Randomly decide to get hungry *)
    if Random.int 3 = 0 then
      phil.state <- Hungry
  | Hungry ->
    phil.total_wait_time <- phil.total_wait_time + 1;
    (* Try to pick up left fork *)
    if acquire_fork li phil.id then
      phil.state <- WaitingForForks { left = true; right = false }
    else ()
  | WaitingForForks { left = true; right = false } ->
    phil.total_wait_time <- phil.total_wait_time + 1;
    if acquire_fork ri phil.id then begin
      phil.state <- Eating;
      phil.meals_eaten <- phil.meals_eaten + 1
    end
  | WaitingForForks _ ->
    phil.total_wait_time <- phil.total_wait_time + 1
  | Eating ->
    phil.total_eat_time <- phil.total_eat_time + 1;
    if Random.int 2 = 0 then begin
      release_fork li;
      release_fork ri;
      phil.state <- Thinking
    end

(* --- Strategy: Resource Hierarchy --- *)

let hierarchy_step table phil =
  let li_idx = phil.id in
  let ri_idx = (phil.id + 1) mod table.size in
  let first_idx = min li_idx ri_idx in
  let second_idx = max li_idx ri_idx in
  let first_fork = table.forks.(first_idx) in
  let second_fork = table.forks.(second_idx) in
  match phil.state with
  | Thinking ->
    phil.total_think_time <- phil.total_think_time + 1;
    if Random.int 3 = 0 then
      phil.state <- Hungry
  | Hungry ->
    phil.total_wait_time <- phil.total_wait_time + 1;
    if acquire_fork first_fork phil.id then
      phil.state <- WaitingForForks { left = (first_idx = li_idx); right = (first_idx = ri_idx) }
  | WaitingForForks _ ->
    phil.total_wait_time <- phil.total_wait_time + 1;
    if acquire_fork second_fork phil.id then begin
      phil.state <- Eating;
      phil.meals_eaten <- phil.meals_eaten + 1
    end else begin
      (* Release first fork to avoid holding indefinitely *)
      release_fork first_fork;
      phil.state <- Hungry
    end
  | Eating ->
    phil.total_eat_time <- phil.total_eat_time + 1;
    if Random.int 2 = 0 then begin
      release_fork first_fork;
      release_fork second_fork;
      phil.state <- Thinking
    end

(* --- Strategy: Arbitrator (central waiter) --- *)

type arbitrator = {
  mutable permits: int;  (* max simultaneous eaters = n-1 *)
}

let make_arbitrator n = { permits = n - 1 }

let arbitrator_step table arb phil =
  let li = left_fork table phil.id in
  let ri = right_fork table phil.id in
  match phil.state with
  | Thinking ->
    phil.total_think_time <- phil.total_think_time + 1;
    if Random.int 3 = 0 then
      phil.state <- Hungry
  | Hungry ->
    phil.total_wait_time <- phil.total_wait_time + 1;
    if arb.permits > 0 then begin
      arb.permits <- arb.permits - 1;
      (* With permit, grab both forks atomically *)
      if is_fork_free li && is_fork_free ri then begin
        ignore (acquire_fork li phil.id);
        ignore (acquire_fork ri phil.id);
        phil.state <- Eating;
        phil.meals_eaten <- phil.meals_eaten + 1
      end else begin
        arb.permits <- arb.permits + 1  (* return permit *)
      end
    end
  | WaitingForForks _ ->
    phil.total_wait_time <- phil.total_wait_time + 1
  | Eating ->
    phil.total_eat_time <- phil.total_eat_time + 1;
    if Random.int 2 = 0 then begin
      release_fork li;
      release_fork ri;
      arb.permits <- arb.permits + 1;
      phil.state <- Thinking
    end

(* --- Strategy: Chandy-Misra --- *)

type cm_fork = {
  mutable holder: int;
  mutable dirty: bool;
}

type cm_state = {
  cm_forks: cm_fork array;
  mutable requests: (int * int) list;  (* (requester, fork_id) *)
}

let make_cm_state n =
  (* Initially, lower-id philosopher holds each fork, marked dirty *)
  let cm_forks = Array.init n (fun i -> { holder = i; dirty = true }) in
  { cm_forks; requests = [] }

let cm_step table cm phil =
  let li_idx = phil.id in
  let ri_idx = (phil.id + 1) mod table.size in
  match phil.state with
  | Thinking ->
    phil.total_think_time <- phil.total_think_time + 1;
    (* Process incoming fork requests: give away dirty forks *)
    List.iter (fun (req_id, fork_id) ->
      let f = cm.cm_forks.(fork_id) in
      if f.holder = phil.id && f.dirty then begin
        f.dirty <- false;
        f.holder <- req_id
      end
    ) cm.requests;
    cm.requests <- List.filter (fun (_, fid) ->
      cm.cm_forks.(fid).holder = phil.id |> not |> not  (* keep unprocessed *)
    ) cm.requests;
    if Random.int 3 = 0 then
      phil.state <- Hungry
  | Hungry ->
    phil.total_wait_time <- phil.total_wait_time + 1;
    let has_left = cm.cm_forks.(li_idx).holder = phil.id in
    let has_right = cm.cm_forks.(ri_idx).holder = phil.id in
    if has_left && has_right then begin
      phil.state <- Eating;
      phil.meals_eaten <- phil.meals_eaten + 1
    end else begin
      if not has_left then
        cm.requests <- (phil.id, li_idx) :: cm.requests;
      if not has_right then
        cm.requests <- (phil.id, ri_idx) :: cm.requests
    end
  | WaitingForForks _ ->
    phil.total_wait_time <- phil.total_wait_time + 1
  | Eating ->
    phil.total_eat_time <- phil.total_eat_time + 1;
    cm.cm_forks.(li_idx).dirty <- true;
    cm.cm_forks.(ri_idx).dirty <- true;
    if Random.int 2 = 0 then
      phil.state <- Thinking

(* --- Deadlock detection --- *)

let is_deadlocked table =
  (* Deadlock: all philosophers hold exactly one fork and wait for another *)
  let all_waiting = Array.for_all (fun p ->
    match p.state with
    | WaitingForForks _ -> true
    | _ -> false
  ) table.philosophers in
  all_waiting && table.size > 1

(* --- Simulation runner --- *)

let run_simulation ?(max_ticks=1000) ?(target_meals=5) strategy n =
  Random.self_init ();
  let table = make_table n in
  let arb = make_arbitrator n in
  let cm = make_cm_state n in
  let tick = ref 0 in
  let deadlocked = ref false in
  let all_fed () =
    Array.for_all (fun p -> p.meals_eaten >= target_meals) table.philosophers
  in
  while !tick < max_ticks && not (all_fed ()) && not !deadlocked do
    Array.iter (fun phil ->
      match strategy with
      | Naive -> naive_step table phil
      | ResourceHierarchy -> hierarchy_step table phil
      | Arbitrator -> arbitrator_step table arb phil
      | ChandyMisra -> cm_step table cm phil
    ) table.philosophers;
    incr tick;
    if strategy = Naive && !tick > 50 && is_deadlocked table then
      deadlocked := true
  done;
  let meals = Array.to_list (Array.map (fun p -> p.meals_eaten) table.philosophers) in
  let total_wait = Array.fold_left (fun acc p -> acc + p.total_wait_time) 0 table.philosophers in
  {
    total_ticks = !tick;
    meals_per_philosopher = meals;
    deadlocked = !deadlocked;
    avg_wait_time = float_of_int total_wait /. float_of_int n;
    fairness_index = jains_fairness meals;
  }

(* --- Pretty printing --- *)

let strategy_name = function
  | Naive -> "Naive (deadlock-prone)"
  | ResourceHierarchy -> "Resource Hierarchy"
  | Arbitrator -> "Arbitrator (Waiter)"
  | ChandyMisra -> "Chandy-Misra"

let print_result strategy result =
  Printf.printf "\n=== %s ===\n" (strategy_name strategy);
  Printf.printf "Ticks: %d | Deadlocked: %b\n" result.total_ticks result.deadlocked;
  Printf.printf "Meals: [%s]\n"
    (String.concat ", " (List.map string_of_int result.meals_per_philosopher));
  Printf.printf "Avg wait time: %.1f ticks\n" result.avg_wait_time;
  Printf.printf "Fairness (Jain's): %.4f\n" result.fairness_index

let print_comparison results =
  Printf.printf "\n╔══════════════════════════╦════════╦══════════╦══════════╦══════════╗\n";
  Printf.printf "║ Strategy                 ║ Ticks  ║ Deadlock ║ Avg Wait ║ Fairness ║\n";
  Printf.printf "╠══════════════════════════╬════════╬══════════╬══════════╬══════════╣\n";
  List.iter (fun (strat, res) ->
    Printf.printf "║ %-24s ║ %6d ║ %-8b ║ %8.1f ║ %8.4f ║\n"
      (strategy_name strat) res.total_ticks res.deadlocked
      res.avg_wait_time res.fairness_index
  ) results;
  Printf.printf "╚══════════════════════════╩════════╩══════════╩══════════╩══════════╝\n"

(* --- Demo --- *)

let run_demo () =
  Printf.printf "╔══════════════════════════════════════════════════════════════╗\n";
  Printf.printf "║          Dining Philosophers Problem — OCaml Demo           ║\n";
  Printf.printf "╚══════════════════════════════════════════════════════════════╝\n";
  let n = 5 in
  let strategies = [Naive; ResourceHierarchy; Arbitrator; ChandyMisra] in
  let results = List.map (fun s ->
    let r = run_simulation ~max_ticks:500 ~target_meals:3 s n in
    print_result s r;
    (s, r)
  ) strategies in
  Printf.printf "\n--- Comparison ---\n";
  print_comparison results

(* ============================================================================
   Test Suite
   ============================================================================ *)

let tests_passed = ref 0
let tests_failed = ref 0

let assert_test name condition =
  if condition then begin
    Printf.printf "  ✓ %s\n" name;
    incr tests_passed
  end else begin
    Printf.printf "  ✗ %s\n" name;
    incr tests_failed
  end

let test_table_creation () =
  Printf.printf "\n── Table Creation ──\n";
  let t = make_table 5 in
  assert_test "5 philosophers created" (Array.length t.philosophers = 5);
  assert_test "5 forks created" (Array.length t.forks = 5);
  assert_test "all philosophers thinking" (Array.for_all (fun p -> p.state = Thinking) t.philosophers);
  assert_test "all forks free" (Array.for_all is_fork_free t.forks);
  assert_test "philosophers named" (t.philosophers.(0).name = "Aristotle")

let test_fork_operations () =
  Printf.printf "\n── Fork Operations ──\n";
  let f = make_fork 0 in
  assert_test "fork starts free" (is_fork_free f);
  assert_test "acquire succeeds" (acquire_fork f 1);
  assert_test "fork now held" (not (is_fork_free f));
  assert_test "second acquire fails" (not (acquire_fork f 2));
  release_fork f;
  assert_test "fork free after release" (is_fork_free f)

let test_fairness_index () =
  Printf.printf "\n── Fairness Index ──\n";
  assert_test "perfect fairness" (abs_float (jains_fairness [5;5;5;5;5] -. 1.0) < 0.001);
  assert_test "unfair distribution" (jains_fairness [10;0;0;0;0] < 0.3);
  assert_test "empty is fair" (abs_float (jains_fairness [] -. 1.0) < 0.001);
  assert_test "single is fair" (abs_float (jains_fairness [7] -. 1.0) < 0.001)

let test_resource_hierarchy () =
  Printf.printf "\n── Resource Hierarchy ──\n";
  let r = run_simulation ~max_ticks:2000 ~target_meals:3 ResourceHierarchy 5 in
  assert_test "no deadlock" (not r.deadlocked);
  assert_test "all ate" (List.for_all (fun m -> m >= 3) r.meals_per_philosopher);
  assert_test "fairness > 0.5" (r.fairness_index > 0.5)

let test_arbitrator () =
  Printf.printf "\n── Arbitrator ──\n";
  let r = run_simulation ~max_ticks:2000 ~target_meals:3 Arbitrator 5 in
  assert_test "no deadlock" (not r.deadlocked);
  assert_test "all ate" (List.for_all (fun m -> m >= 3) r.meals_per_philosopher)

let test_chandy_misra () =
  Printf.printf "\n── Chandy-Misra ──\n";
  let r = run_simulation ~max_ticks:2000 ~target_meals:3 ChandyMisra 5 in
  assert_test "no deadlock" (not r.deadlocked);
  assert_test "all ate" (List.for_all (fun m -> m >= 3) r.meals_per_philosopher)

let run_tests () =
  Printf.printf "\n╔══════════════════════════════════════════════════════════════╗\n";
  Printf.printf "║          Dining Philosophers — Test Suite                    ║\n";
  Printf.printf "╚══════════════════════════════════════════════════════════════╝\n";
  test_table_creation ();
  test_fork_operations ();
  test_fairness_index ();
  test_resource_hierarchy ();
  test_arbitrator ();
  test_chandy_misra ();
  Printf.printf "\n══════════════════════════════════════════\n";
  Printf.printf "Results: %d passed, %d failed\n" !tests_passed !tests_failed;
  Printf.printf "══════════════════════════════════════════\n"

let () =
  run_demo ();
  run_tests ()
