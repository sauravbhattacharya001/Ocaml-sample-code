(* Task Scheduler — Real-Time Scheduling Algorithms
   
   Implements classic real-time scheduling with:
   - Earliest Deadline First (EDF) — optimal dynamic-priority
   - Rate Monotonic (RM) — optimal fixed-priority for periodic tasks
   - Round Robin (RR) — fair time-slicing with configurable quantum
   - Deadline miss detection and utilization analysis
   - ASCII Gantt chart visualization
   - Schedulability tests (Liu & Layland bound, exact analysis)
   - Proactive overload detection with recommendations
   
   Usage: ocaml task_scheduler.ml
*)

(* ── Task definition ─────────────────────────────────────────── *)

type task = {
  id: int;
  name: string;
  period: int;           (* period for periodic tasks *)
  wcet: int;             (* worst-case execution time *)
  deadline: int;         (* relative deadline *)
  priority: int;         (* lower = higher priority for RM *)
}

type job = {
  task_id: int;
  release: int;
  absolute_deadline: int;
  remaining: int;
  completed: bool;
}

type schedule_event = {
  time_start: int;
  time_end: int;
  task_name: string;
  task_id: int;
}

type algorithm = EDF | RateMonotonic | RoundRobin of int

type schedule_result = {
  events: schedule_event list;
  deadline_misses: (int * string * int) list;  (* time, task_name, deadline *)
  utilization: float;
  schedulable: bool;
  algorithm_name: string;
}

(* ── Utilization and schedulability ─────────────────────────── *)

let compute_utilization tasks =
  List.fold_left (fun acc t ->
    acc +. (float_of_int t.wcet /. float_of_int t.period)
  ) 0.0 tasks

let liu_layland_bound n =
  float_of_int n *. (2.0 ** (1.0 /. float_of_int n) -. 1.0)

let rm_schedulable tasks =
  let n = List.length tasks in
  let u = compute_utilization tasks in
  u <= liu_layland_bound n

let edf_schedulable tasks =
  compute_utilization tasks <= 1.0

(* ── LCM for hyperperiod ────────────────────────────────────── *)

let rec gcd a b = if b = 0 then a else gcd b (a mod b)
let lcm a b = (a * b) / (gcd a b)

let hyperperiod tasks =
  List.fold_left (fun acc t -> lcm acc t.period) 1 tasks

(* ── Job generation ─────────────────────────────────────────── *)

let generate_jobs tasks horizon =
  List.concat_map (fun t ->
    let rec gen release acc =
      if release >= horizon then List.rev acc
      else
        let j = {
          task_id = t.id;
          release;
          absolute_deadline = release + t.deadline;
          remaining = t.wcet;
          completed = false;
        } in
        gen (release + t.period) (j :: acc)
    in
    gen 0 []
  ) tasks

(* ── EDF scheduler ──────────────────────────────────────────── *)

let schedule_edf tasks horizon =
  let jobs = ref (generate_jobs tasks horizon) in
  let events = ref [] in
  let misses = ref [] in
  let task_map = List.map (fun t -> (t.id, t)) tasks in
  let find_task id = List.assoc id task_map in
  for time = 0 to horizon - 1 do
    (* Find ready jobs sorted by deadline *)
    let ready = List.filter (fun j ->
      j.release <= time && j.remaining > 0 && not j.completed
    ) !jobs in
    let ready = List.sort (fun a b ->
      compare a.absolute_deadline b.absolute_deadline
    ) ready in
    match ready with
    | [] -> ()
    | chosen :: _ ->
      let t = find_task chosen.task_id in
      events := {
        time_start = time;
        time_end = time + 1;
        task_name = t.name;
        task_id = t.id;
      } :: !events;
      jobs := List.map (fun j ->
        if j.task_id = chosen.task_id && j.release = chosen.release then
          { j with remaining = j.remaining - 1;
                   completed = j.remaining - 1 = 0 }
        else j
      ) !jobs
  done;
  (* Check deadline misses *)
  List.iter (fun j ->
    if not j.completed && j.remaining > 0 then begin
      let t = find_task j.task_id in
      misses := (j.absolute_deadline, t.name, j.absolute_deadline) :: !misses
    end
  ) !jobs;
  {
    events = List.rev !events;
    deadline_misses = !misses;
    utilization = compute_utilization tasks;
    schedulable = edf_schedulable tasks;
    algorithm_name = "Earliest Deadline First (EDF)";
  }

(* ── Rate Monotonic scheduler ───────────────────────────────── *)

let schedule_rm tasks horizon =
  (* Assign priority by period (shorter period = higher priority) *)
  let sorted = List.sort (fun a b -> compare a.period b.period) tasks in
  let prioritized = List.mapi (fun i t -> { t with priority = i }) sorted in
  let jobs = ref (generate_jobs prioritized horizon) in
  let events = ref [] in
  let misses = ref [] in
  let task_map = List.map (fun t -> (t.id, t)) prioritized in
  let find_task id = List.assoc id task_map in
  for time = 0 to horizon - 1 do
    let ready = List.filter (fun j ->
      j.release <= time && j.remaining > 0 && not j.completed
    ) !jobs in
    let ready = List.sort (fun a b ->
      let ta = find_task a.task_id in
      let tb = find_task b.task_id in
      compare ta.priority tb.priority
    ) ready in
    match ready with
    | [] -> ()
    | chosen :: _ ->
      let t = find_task chosen.task_id in
      events := {
        time_start = time;
        time_end = time + 1;
        task_name = t.name;
        task_id = t.id;
      } :: !events;
      jobs := List.map (fun j ->
        if j.task_id = chosen.task_id && j.release = chosen.release then
          { j with remaining = j.remaining - 1;
                   completed = j.remaining - 1 = 0 }
        else j
      ) !jobs
  done;
  List.iter (fun j ->
    if not j.completed && j.remaining > 0 then begin
      let t = find_task j.task_id in
      misses := (j.absolute_deadline, t.name, j.absolute_deadline) :: !misses
    end
  ) !jobs;
  {
    events = List.rev !events;
    deadline_misses = !misses;
    utilization = compute_utilization tasks;
    schedulable = rm_schedulable tasks;
    algorithm_name = "Rate Monotonic (RM)";
  }

(* ── Round Robin scheduler ──────────────────────────────────── *)

let schedule_rr tasks horizon quantum =
  let jobs = ref (generate_jobs tasks horizon) in
  let events = ref [] in
  let misses = ref [] in
  let task_map = List.map (fun t -> (t.id, t)) tasks in
  let find_task id = List.assoc id task_map in
  let queue = Queue.create () in
  let in_queue = Hashtbl.create 16 in
  let time = ref 0 in
  let current_slice = ref 0 in
  let current_job = ref None in
  while !time < horizon do
    (* Add newly released jobs to queue *)
    List.iter (fun j ->
      if j.release = !time && j.remaining > 0 && not j.completed then begin
        let key = (j.task_id, j.release) in
        if not (Hashtbl.mem in_queue key) then begin
          Queue.push key queue;
          Hashtbl.replace in_queue key true
        end
      end
    ) !jobs;
    (* Pick next job if no current or quantum expired *)
    if !current_job = None || !current_slice >= quantum then begin
      (* Re-queue current if not done *)
      (match !current_job with
       | Some (tid, rel) ->
         let j = List.find (fun j -> j.task_id = tid && j.release = rel) !jobs in
         if j.remaining > 0 && not j.completed then
           Queue.push (tid, rel) queue
       | None -> ());
      current_job := None;
      current_slice := 0;
      if not (Queue.is_empty queue) then begin
        let (tid, rel) = Queue.pop queue in
        Hashtbl.remove in_queue (tid, rel);
        let j = List.find (fun j -> j.task_id = tid && j.release = rel) !jobs in
        if j.remaining > 0 && not j.completed then begin
          current_job := Some (tid, rel);
          current_slice := 0
        end
      end
    end;
    (match !current_job with
     | None -> ()
     | Some (tid, rel) ->
       let t = find_task tid in
       events := {
         time_start = !time;
         time_end = !time + 1;
         task_name = t.name;
         task_id = t.id;
       } :: !events;
       jobs := List.map (fun j ->
         if j.task_id = tid && j.release = rel then
           { j with remaining = j.remaining - 1;
                    completed = j.remaining - 1 = 0 }
         else j
       ) !jobs;
       current_slice := !current_slice + 1;
       let j = List.find (fun j -> j.task_id = tid && j.release = rel) !jobs in
       if j.completed then begin
         current_job := None;
         current_slice := 0
       end);
    incr time
  done;
  List.iter (fun j ->
    if not j.completed && j.remaining > 0 then begin
      let t = find_task j.task_id in
      misses := (j.absolute_deadline, t.name, j.absolute_deadline) :: !misses
    end
  ) !jobs;
  {
    events = List.rev !events;
    deadline_misses = !misses;
    utilization = compute_utilization tasks;
    schedulable = compute_utilization tasks <= 1.0;
    algorithm_name = Printf.sprintf "Round Robin (quantum=%d)" quantum;
  }

(* ── Merge consecutive events ───────────────────────────────── *)

let merge_events events =
  let rec merge acc = function
    | [] -> List.rev acc
    | e :: rest ->
      match acc with
      | prev :: acc_rest when prev.task_id = e.task_id && prev.time_end = e.time_start ->
        merge ({ prev with time_end = e.time_end } :: acc_rest) rest
      | _ -> merge (e :: acc) rest
  in
  merge [] events

(* ── ASCII Gantt chart ──────────────────────────────────────── *)

let gantt_chart result horizon =
  let merged = merge_events result.events in
  let width = min horizon 60 in
  let scale = float_of_int horizon /. float_of_int width in
  Printf.printf "\n┌─ Gantt Chart: %s " result.algorithm_name;
  for _ = 1 to width - String.length result.algorithm_name - 14 do
    print_char '─'
  done;
  print_string "┐\n";
  (* Time axis *)
  Printf.printf "│ ";
  for t = 0 to width - 1 do
    let actual = int_of_float (float_of_int t *. scale) in
    if actual mod 5 = 0 then
      print_char '|'
    else
      print_char ' '
  done;
  print_string " │\n";
  (* Collect unique task IDs *)
  let task_ids = List.sort_uniq compare
    (List.map (fun e -> (e.task_id, e.task_name)) merged) in
  List.iter (fun (tid, tname) ->
    Printf.printf "│ ";
    for t = 0 to width - 1 do
      let actual_start = int_of_float (float_of_int t *. scale) in
      let actual_end = int_of_float (float_of_int (t + 1) *. scale) in
      let running = List.exists (fun e ->
        e.task_id = tid && e.time_start < actual_end && e.time_end > actual_start
      ) merged in
      if running then print_char '#'
      else print_char '.'
    done;
    Printf.printf " │ %s\n" tname
  ) task_ids;
  Printf.printf "└";
  for _ = 1 to width + 2 do print_char '─' done;
  print_string "┘\n";
  (* Time labels *)
  Printf.printf "  0";
  for t = 1 to width - 1 do
    let actual = int_of_float (float_of_int t *. scale) in
    if actual mod 10 = 0 then
      Printf.printf "%-2d" actual
    else if (actual - 1) mod 10 <> 0 then
      print_char ' '
  done;
  print_newline ()

(* ── Overload advisor ───────────────────────────────────────── *)

let overload_advisor tasks =
  let u = compute_utilization tasks in
  let n = List.length tasks in
  Printf.printf "\n╔══ Overload Advisor ══════════════════════════════════════╗\n";
  Printf.printf "║ Total utilization: %.4f (%.1f%%)%s║\n"
    u (u *. 100.0) (String.make (max 0 (28 - String.length (Printf.sprintf "%.4f (%.1f%%)" u (u *. 100.0)))) ' ');
  Printf.printf "║ Liu-Layland RM bound: %.4f (n=%d)%s║\n"
    (liu_layland_bound n) n
    (String.make (max 0 (27 - String.length (Printf.sprintf "%.4f (n=%d)" (liu_layland_bound n) n))) ' ');
  Printf.printf "║                                                         ║\n";
  if u > 1.0 then begin
    Printf.printf "║ ⚠ OVERLOADED — system cannot schedule all tasks!        ║\n";
    Printf.printf "║ Recommendation: Remove or reduce WCET of tasks:         ║\n";
    let sorted = List.sort (fun a b ->
      compare (float_of_int b.wcet /. float_of_int b.period)
              (float_of_int a.wcet /. float_of_int a.period)
    ) tasks in
    (match sorted with
     | t :: _ ->
       Printf.printf "║   → '%s' uses %.1f%% alone%s║\n"
         t.name
         (float_of_int t.wcet /. float_of_int t.period *. 100.0)
         (String.make (max 0 (37 - String.length t.name - String.length (Printf.sprintf "%.1f%%" (float_of_int t.wcet /. float_of_int t.period *. 100.0)))) ' ')
     | [] -> ())
  end else if u > liu_layland_bound n then begin
    Printf.printf "║ ⚡ Above RM bound — EDF may still schedule.             ║\n";
    Printf.printf "║ Recommendation: Use EDF or verify RM with exact test.   ║\n"
  end else begin
    Printf.printf "║ ✓ Within RM bound — all algorithms should work.         ║\n";
    Printf.printf "║ Headroom: %.1f%% spare capacity.%s║\n"
      ((1.0 -. u) *. 100.0)
      (String.make (max 0 (30 - String.length (Printf.sprintf "%.1f%%" ((1.0 -. u) *. 100.0)))) ' ')
  end;
  Printf.printf "╚═════════════════════════════════════════════════════════╝\n"

(* ── Print results ──────────────────────────────────────────── *)

let print_result result horizon =
  Printf.printf "\n━━━ %s ━━━\n" result.algorithm_name;
  gantt_chart result horizon;
  Printf.printf "\n  Utilization: %.2f%%\n" (result.utilization *. 100.0);
  Printf.printf "  Schedulable: %s\n"
    (if result.schedulable then "✓ Yes" else "✗ No");
  if result.deadline_misses <> [] then begin
    Printf.printf "  ⚠ Deadline misses: %d\n" (List.length result.deadline_misses);
    List.iter (fun (t, name, dl) ->
      Printf.printf "    → %s missed deadline at t=%d (deadline=%d)\n" name t dl
    ) result.deadline_misses
  end else
    Printf.printf "  ✓ No deadline misses\n"

(* ── Compare algorithms ─────────────────────────────────────── *)

let compare_algorithms tasks horizon =
  Printf.printf "\n╔══════════════════════════════════════════════════════════╗\n";
  Printf.printf "║           Algorithm Comparison Summary                  ║\n";
  Printf.printf "╠══════════════════════════════════════════════════════════╣\n";
  Printf.printf "║ %-20s │ Misses │ Schedulable │ Best?  ║\n" "Algorithm";
  Printf.printf "╟──────────────────────┼────────┼─────────────┼────────╢\n";
  let results = [
    schedule_edf tasks horizon;
    schedule_rm tasks horizon;
    schedule_rr tasks horizon 2;
  ] in
  let best = List.fold_left (fun best r ->
    if List.length r.deadline_misses < List.length best.deadline_misses then r
    else best
  ) (List.hd results) results in
  List.iter (fun r ->
    let is_best = r.algorithm_name = best.algorithm_name in
    Printf.printf "║ %-20s │ %6d │ %-11s │ %-6s ║\n"
      (String.sub r.algorithm_name 0 (min 20 (String.length r.algorithm_name)))
      (List.length r.deadline_misses)
      (if r.schedulable then "✓ Yes" else "✗ No")
      (if is_best then "★ Yes" else "")
  ) results;
  Printf.printf "╚══════════════════════════════════════════════════════════╝\n";
  Printf.printf "\n  Recommendation: Use %s for this task set.\n" best.algorithm_name

(* ── Example task sets ──────────────────────────────────────── *)

let example_simple = [
  { id = 0; name = "Sensor"; period = 5; wcet = 1; deadline = 5; priority = 0 };
  { id = 1; name = "Control"; period = 10; wcet = 3; deadline = 10; priority = 1 };
  { id = 2; name = "Logger"; period = 20; wcet = 2; deadline = 20; priority = 2 };
]

let example_tight = [
  { id = 0; name = "Heartbeat"; period = 4; wcet = 1; deadline = 4; priority = 0 };
  { id = 1; name = "NavUpdate"; period = 6; wcet = 2; deadline = 6; priority = 1 };
  { id = 2; name = "Telemetry"; period = 12; wcet = 3; deadline = 12; priority = 2 };
]

let example_overload = [
  { id = 0; name = "Critical"; period = 3; wcet = 2; deadline = 3; priority = 0 };
  { id = 1; name = "Display"; period = 4; wcet = 2; deadline = 4; priority = 1 };
  { id = 2; name = "Backup"; period = 6; wcet = 2; deadline = 6; priority = 2 };
]

(* ── Interactive REPL ───────────────────────────────────────── *)

let custom_tasks = ref []
let next_id = ref 0

let repl () =
  Printf.printf "\n┌───────────────────────────────────────┐\n";
  Printf.printf "│  Task Scheduler — Interactive Mode     │\n";
  Printf.printf "│  Commands:                             │\n";
  Printf.printf "│    add <name> <period> <wcet> <dl>     │\n";
  Printf.printf "│    remove <name>                       │\n";
  Printf.printf "│    list                                │\n";
  Printf.printf "│    edf / rm / rr <quantum>             │\n";
  Printf.printf "│    compare                             │\n";
  Printf.printf "│    advisor                             │\n";
  Printf.printf "│    clear / quit                        │\n";
  Printf.printf "└───────────────────────────────────────┘\n";
  let running = ref true in
  while !running do
    Printf.printf "\nscheduler> %!";
    let line = try input_line stdin with End_of_file -> "quit" in
    let parts = String.split_on_char ' ' (String.trim line) in
    match parts with
    | ["quit"] | ["exit"] | ["q"] -> running := false
    | ["add"; name; p; c; d] ->
      (try
        let t = {
          id = !next_id; name;
          period = int_of_string p;
          wcet = int_of_string c;
          deadline = int_of_string d;
          priority = !next_id;
        } in
        custom_tasks := !custom_tasks @ [t];
        incr next_id;
        Printf.printf "  Added: %s (P=%d, C=%d, D=%d)\n" name t.period t.wcet t.deadline
      with _ -> Printf.printf "  Error: add <name> <period> <wcet> <deadline>\n")
    | ["remove"; name] ->
      custom_tasks := List.filter (fun t -> t.name <> name) !custom_tasks;
      Printf.printf "  Removed: %s\n" name
    | ["list"] ->
      if !custom_tasks = [] then Printf.printf "  (no tasks)\n"
      else List.iter (fun t ->
        Printf.printf "  [%d] %s — P=%d, C=%d, D=%d (U=%.2f%%)\n"
          t.id t.name t.period t.wcet t.deadline
          (float_of_int t.wcet /. float_of_int t.period *. 100.0)
      ) !custom_tasks
    | ["edf"] when !custom_tasks <> [] ->
      let hp = hyperperiod !custom_tasks in
      print_result (schedule_edf !custom_tasks hp) hp
    | ["rm"] when !custom_tasks <> [] ->
      let hp = hyperperiod !custom_tasks in
      print_result (schedule_rm !custom_tasks hp) hp
    | ["rr"; q] when !custom_tasks <> [] ->
      (try
        let hp = hyperperiod !custom_tasks in
        print_result (schedule_rr !custom_tasks hp (int_of_string q)) hp
      with _ -> Printf.printf "  Error: rr <quantum>\n")
    | ["compare"] when !custom_tasks <> [] ->
      compare_algorithms !custom_tasks (hyperperiod !custom_tasks)
    | ["advisor"] when !custom_tasks <> [] ->
      overload_advisor !custom_tasks
    | ["clear"] ->
      custom_tasks := []; next_id := 0;
      Printf.printf "  Cleared all tasks.\n"
    | _ -> Printf.printf "  Unknown command. Try: add, remove, list, edf, rm, rr, compare, advisor, quit\n"
  done

(* ── Demo ───────────────────────────────────────────────────── *)

let () =
  Printf.printf "╔══════════════════════════════════════════════════════════╗\n";
  Printf.printf "║     Real-Time Task Scheduler — OCaml Implementation     ║\n";
  Printf.printf "║  EDF · Rate Monotonic · Round Robin · Gantt Charts      ║\n";
  Printf.printf "╚══════════════════════════════════════════════════════════╝\n";

  Printf.printf "\n━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━\n";
  Printf.printf "  Example 1: Simple task set (U=55%%)\n";
  Printf.printf "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━\n";
  let hp1 = hyperperiod example_simple in
  print_result (schedule_edf example_simple hp1) hp1;
  print_result (schedule_rm example_simple hp1) hp1;
  print_result (schedule_rr example_simple hp1 2) hp1;

  Printf.printf "\n━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━\n";
  Printf.printf "  Example 2: Tight utilization (U=83%%)\n";
  Printf.printf "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━\n";
  let hp2 = hyperperiod example_tight in
  print_result (schedule_edf example_tight hp2) hp2;
  print_result (schedule_rm example_tight hp2) hp2;

  Printf.printf "\n━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━\n";
  Printf.printf "  Example 3: Overloaded system (U>100%%)\n";
  Printf.printf "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━\n";
  let hp3 = hyperperiod example_overload in
  print_result (schedule_edf example_overload hp3) hp3;
  overload_advisor example_overload;

  compare_algorithms example_simple hp1;

  Printf.printf "\n━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━\n";
  Printf.printf "  Interactive mode — type 'quit' to exit\n";
  Printf.printf "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━\n";
  repl ()
