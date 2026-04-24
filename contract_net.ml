(* Contract Net Protocol Simulator
   =================================
   Implementation of the FIPA Contract Net Interaction Protocol — a classic
   multi-agent task allocation mechanism where a manager broadcasts a Call
   for Proposals (CFP), contractors bid, and the manager awards to the best.

   Features:
   - Manager and Contractor agents with configurable strategies
   - 6 bidding strategies: lowest-cost, fastest, balanced, specialist, random, adaptive
   - 3 manager award strategies: cheapest, fastest, best-value (weighted)
   - Task decomposition: complex tasks split into subtasks with dependencies
   - Reputation tracking: past performance affects future awards
   - Failure handling: automatic re-allocation on contractor failure
   - 3 built-in domains: logistics, software development, construction
   - Interactive REPL with step-by-step or auto-run execution

   Usage: ocaml contract_net.ml
          ocaml contract_net.ml --domain logistics
          ocaml contract_net.ml --domain software
          ocaml contract_net.ml --domain construction
          ocaml contract_net.ml --auto
*)

(* ── Core Types ────────────────────────────────────────────────────── *)

type skill = string

type task = {
  t_id          : int;
  t_name        : string;
  t_skills      : skill list;
  t_complexity  : float;   (* 0.0–1.0 *)
  t_deadline    : int;     (* max steps allowed *)
  t_parent      : int option;
  t_deps        : int list;
}

type bid = {
  b_contractor  : string;
  b_task_id     : int;
  b_cost        : float;
  b_time        : int;
  b_confidence  : float;   (* 0.0–1.0 *)
}

type award_strategy = Cheapest | Fastest | BestValue of float (* cost_weight *)

type bid_strategy =
  | LowCost | FastTime | Balanced | Specialist | RandomBid | Adaptive

type task_state =
  | Pending | Announced | Bidding | Awarded of string | InProgress of string * int
  | Completed of string | Failed of string * string | Cancelled

let task_state_str = function
  | Pending -> "pending" | Announced -> "announced" | Bidding -> "bidding"
  | Awarded c -> Printf.sprintf "awarded(%s)" c
  | InProgress (c, s) -> Printf.sprintf "in-progress(%s, step %d)" c s
  | Completed c -> Printf.sprintf "completed(%s)" c
  | Failed (c, r) -> Printf.sprintf "failed(%s: %s)" c r
  | Cancelled -> "cancelled"

(* ── Contractor ────────────────────────────────────────────────────── *)

type contractor = {
  c_name       : string;
  c_skills     : skill list;
  c_efficiency : float;    (* 0.5–2.0; lower = faster/cheaper *)
  c_reliability: float;    (* 0.0–1.0; probability of success *)
  c_capacity   : int;      (* max concurrent tasks *)
  c_strategy   : bid_strategy;
  mutable c_active : int;  (* current active tasks *)
  mutable c_completed : int;
  mutable c_failed    : int;
  mutable c_reputation: float;
}

let make_contractor name skills efficiency reliability capacity strategy = {
  c_name = name; c_skills = skills; c_efficiency = efficiency;
  c_reliability = reliability; c_capacity = capacity;
  c_strategy = strategy; c_active = 0; c_completed = 0;
  c_failed = 0; c_reputation = 0.5;
}

(* ── Simulation State ──────────────────────────────────────────────── *)

type sim = {
  mutable tasks       : (int * task * task_state) list;
  mutable contractors : contractor list;
  mutable bids        : bid list;
  mutable step        : int;
  mutable log         : string list;
  mutable award_strat : award_strategy;
  mutable next_id     : int;
}

let sim_create strat = {
  tasks = []; contractors = []; bids = []; step = 0;
  log = []; award_strat = strat; next_id = 1;
}

let log s msg =
  let line = Printf.sprintf "[step %d] %s" s.step msg in
  s.log <- line :: s.log;
  Printf.printf "  %s\n" line

let fresh_id s = let id = s.next_id in s.next_id <- id + 1; id

(* ── Bid Generation ────────────────────────────────────────────────── *)

let has_skills c task =
  List.for_all (fun sk -> List.mem sk c.c_skills) task.t_skills

let gen_bid c task =
  if c.c_active >= c.c_capacity then None
  else if not (has_skills c task) then None
  else begin
    let base_cost = task.t_complexity *. 100.0 *. c.c_efficiency in
    let base_time = max 1 (int_of_float (task.t_complexity *. 10.0 *. c.c_efficiency)) in
    let jitter () = 0.85 +. Random.float 0.3 in
    let (cost, time, conf) = match c.c_strategy with
      | LowCost ->
        (base_cost *. 0.75 *. jitter (), base_time + 2, 0.7 +. Random.float 0.2)
      | FastTime ->
        (base_cost *. 1.3 *. jitter (), max 1 (base_time - 2), 0.6 +. Random.float 0.3)
      | Balanced ->
        (base_cost *. jitter (), base_time, 0.75 +. Random.float 0.2)
      | Specialist ->
        let spec_bonus = if List.length c.c_skills <= 2 then 0.8 else 1.1 in
        (base_cost *. spec_bonus *. jitter (), base_time, 0.85 +. Random.float 0.15)
      | RandomBid ->
        (base_cost *. (0.5 +. Random.float 1.0), max 1 (base_time + Random.int 5 - 2),
         0.4 +. Random.float 0.5)
      | Adaptive ->
        let rep_factor = 0.7 +. c.c_reputation *. 0.6 in
        (base_cost *. rep_factor *. jitter (), base_time, c.c_reputation)
    in
    Some { b_contractor = c.c_name; b_task_id = task.t_id;
           b_cost = Float.round (cost *. 100.0) /. 100.0;
           b_time = time; b_confidence = Float.round (conf *. 100.0) /. 100.0 }
  end

(* ── Award Selection ───────────────────────────────────────────────── *)

let score_bid strat contractor_rep bid =
  let rep = match contractor_rep with Some r -> r | None -> 0.5 in
  match strat with
  | Cheapest -> -. bid.b_cost
  | Fastest -> -. (float_of_int bid.b_time)
  | BestValue w ->
    let cost_score = 1.0 /. (1.0 +. bid.b_cost) in
    let time_score = 1.0 /. (1.0 +. float_of_int bid.b_time) in
    w *. cost_score +. (1.0 -. w) *. time_score
    +. 0.2 *. bid.b_confidence +. 0.15 *. rep

let best_bid s bids_for_task =
  let scored = List.map (fun b ->
    let rep = List.find_opt (fun c -> c.c_name = b.b_contractor) s.contractors
              |> Option.map (fun c -> c.c_reputation) in
    (b, score_bid s.award_strat rep b)
  ) bids_for_task in
  let sorted = List.sort (fun (_, s1) (_, s2) -> compare s2 s1) scored in
  match sorted with [] -> None | (b, _) :: _ -> Some b

(* ── Task Lifecycle ────────────────────────────────────────────────── *)

let deps_met s task =
  List.for_all (fun dep_id ->
    List.exists (fun (id, _, st) -> id = dep_id &&
      (match st with Completed _ -> true | _ -> false)) s.tasks
  ) task.t_deps

let announce_tasks s =
  s.tasks <- List.map (fun (id, t, st) ->
    match st with
    | Pending when deps_met s t ->
      log s (Printf.sprintf "📢 CFP: Task '%s' (complexity=%.1f, skills=%s, deadline=%d)"
        t.t_name t.t_complexity (String.concat "," t.t_skills) t.t_deadline);
      (id, t, Announced)
    | _ -> (id, t, st)
  ) s.tasks

let collect_bids s =
  s.bids <- [];
  List.iter (fun (id, t, st) ->
    match st with
    | Announced ->
      List.iter (fun c ->
        match gen_bid c t with
        | Some bid ->
          log s (Printf.sprintf "  💼 %s bids on '%s': $%.2f, %d steps, conf=%.0f%%"
            c.c_name t.t_name bid.b_cost bid.b_time (bid.b_confidence *. 100.0));
          s.bids <- bid :: s.bids
        | None -> ()
      ) s.contractors
    | _ -> ()
  ) s.tasks;
  s.tasks <- List.map (fun (id, t, st) ->
    match st with Announced -> (id, t, Bidding) | _ -> (id, t, st)
  ) s.tasks

let award_tasks s =
  s.tasks <- List.map (fun (id, t, st) ->
    match st with
    | Bidding ->
      let bids_here = List.filter (fun b -> b.b_task_id = id) s.bids in
      begin match best_bid s bids_here with
      | Some b ->
        log s (Printf.sprintf "  🏆 Awarded '%s' to %s ($%.2f, %d steps)"
          t.t_name b.b_contractor b.b_cost b.b_time);
        let c = List.find (fun c -> c.c_name = b.b_contractor) s.contractors in
        c.c_active <- c.c_active + 1;
        (id, t, InProgress (b.b_contractor, b.b_time))
      | None ->
        log s (Printf.sprintf "  ⚠️ No bids for '%s' — re-announcing" t.t_name);
        (id, t, Pending)
      end
    | _ -> (id, t, st)
  ) s.tasks

let progress_tasks s =
  s.tasks <- List.map (fun (id, t, st) ->
    match st with
    | InProgress (c_name, remaining) when remaining <= 1 ->
      let c = List.find (fun c -> c.c_name = c_name) s.contractors in
      if Random.float 1.0 < c.c_reliability then begin
        log s (Printf.sprintf "  ✅ '%s' completed by %s" t.t_name c_name);
        c.c_active <- c.c_active - 1;
        c.c_completed <- c.c_completed + 1;
        c.c_reputation <- min 1.0 (c.c_reputation +. 0.05);
        (id, t, Completed c_name)
      end else begin
        let reason = match Random.int 4 with
          | 0 -> "resource shortage" | 1 -> "technical failure"
          | 2 -> "quality check failed" | _ -> "timeout" in
        log s (Printf.sprintf "  ❌ '%s' failed by %s: %s" t.t_name c_name reason);
        c.c_active <- c.c_active - 1;
        c.c_failed <- c.c_failed + 1;
        c.c_reputation <- max 0.0 (c.c_reputation -. 0.1);
        log s (Printf.sprintf "  🔄 Re-announcing '%s' for rebid" t.t_name);
        (id, t, Pending)
      end
    | InProgress (c, remaining) -> (id, t, InProgress (c, remaining - 1))
    | _ -> (id, t, st)
  ) s.tasks

let all_done s =
  List.for_all (fun (_, _, st) ->
    match st with Completed _ | Cancelled -> true | _ -> false
  ) s.tasks

let deadline_check s =
  s.tasks <- List.map (fun (id, t, st) ->
    match st with
    | InProgress (c, _) when s.step > t.t_deadline + 5 ->
      log s (Printf.sprintf "  ⏰ '%s' exceeded deadline — cancelling from %s" t.t_name c);
      let co = List.find (fun co -> co.c_name = c) s.contractors in
      co.c_active <- co.c_active - 1;
      co.c_failed <- co.c_failed + 1;
      co.c_reputation <- max 0.0 (co.c_reputation -. 0.15);
      (id, t, Pending)
    | _ -> (id, t, st)
  ) s.tasks

(* ── Simulation Step ───────────────────────────────────────────────── *)

let sim_step s =
  s.step <- s.step + 1;
  Printf.printf "\n═══ Step %d ═══\n" s.step;
  announce_tasks s;
  collect_bids s;
  award_tasks s;
  progress_tasks s;
  deadline_check s

(* ── Domains ───────────────────────────────────────────────────────── *)

let logistics_domain () =
  let s = sim_create (BestValue 0.5) in
  s.contractors <- [
    make_contractor "FastFreight" ["transport";"warehousing"] 0.8 0.9 3 FastTime;
    make_contractor "BudgetHaul" ["transport"] 1.5 0.85 4 LowCost;
    make_contractor "ProLogistics" ["transport";"warehousing";"customs"] 1.0 0.95 2 Balanced;
    make_contractor "SpecialistCargo" ["customs";"hazmat"] 1.2 0.98 2 Specialist;
    make_contractor "FlexShip" ["transport";"warehousing"] 1.0 0.88 3 Adaptive;
  ];
  let id1 = fresh_id s in let id2 = fresh_id s in let id3 = fresh_id s in
  let id4 = fresh_id s in let id5 = fresh_id s in
  s.tasks <- [
    (id1, { t_id=id1; t_name="Pickup from warehouse"; t_skills=["warehousing"];
             t_complexity=0.3; t_deadline=8; t_parent=None; t_deps=[] }, Pending);
    (id2, { t_id=id2; t_name="Transport to port"; t_skills=["transport"];
             t_complexity=0.5; t_deadline=12; t_parent=None; t_deps=[id1] }, Pending);
    (id3, { t_id=id3; t_name="Customs clearance"; t_skills=["customs"];
             t_complexity=0.7; t_deadline=15; t_parent=None; t_deps=[id2] }, Pending);
    (id4, { t_id=id4; t_name="Hazmat inspection"; t_skills=["hazmat"];
             t_complexity=0.6; t_deadline=15; t_parent=None; t_deps=[id2] }, Pending);
    (id5, { t_id=id5; t_name="Final delivery"; t_skills=["transport"];
             t_complexity=0.4; t_deadline=20; t_parent=None; t_deps=[id3;id4] }, Pending);
  ];
  s

let software_domain () =
  let s = sim_create (BestValue 0.4) in
  s.contractors <- [
    make_contractor "AlphaDevs" ["frontend";"design"] 0.9 0.92 2 Balanced;
    make_contractor "BackendPros" ["backend";"database"] 0.7 0.95 2 Specialist;
    make_contractor "FullStackInc" ["frontend";"backend";"testing"] 1.1 0.85 3 Adaptive;
    make_contractor "QAExperts" ["testing";"security"] 1.3 0.97 3 LowCost;
    make_contractor "SpeedCoders" ["frontend";"backend"] 0.6 0.80 2 FastTime;
  ];
  let id1 = fresh_id s in let id2 = fresh_id s in let id3 = fresh_id s in
  let id4 = fresh_id s in let id5 = fresh_id s in let id6 = fresh_id s in
  s.tasks <- [
    (id1, { t_id=id1; t_name="Design UI mockups"; t_skills=["design"];
             t_complexity=0.4; t_deadline=8; t_parent=None; t_deps=[] }, Pending);
    (id2, { t_id=id2; t_name="Build REST API"; t_skills=["backend"];
             t_complexity=0.7; t_deadline=12; t_parent=None; t_deps=[] }, Pending);
    (id3, { t_id=id3; t_name="Setup database"; t_skills=["database"];
             t_complexity=0.5; t_deadline=10; t_parent=None; t_deps=[] }, Pending);
    (id4, { t_id=id4; t_name="Frontend implementation"; t_skills=["frontend"];
             t_complexity=0.8; t_deadline=18; t_parent=None; t_deps=[id1;id2] }, Pending);
    (id5, { t_id=id5; t_name="Integration testing"; t_skills=["testing"];
             t_complexity=0.6; t_deadline=22; t_parent=None; t_deps=[id4;id3] }, Pending);
    (id6, { t_id=id6; t_name="Security audit"; t_skills=["security"];
             t_complexity=0.5; t_deadline=25; t_parent=None; t_deps=[id5] }, Pending);
  ];
  s

let construction_domain () =
  let s = sim_create Cheapest in
  s.contractors <- [
    make_contractor "SolidBuild" ["foundation";"framing"] 1.0 0.93 2 Balanced;
    make_contractor "QuickFrame" ["framing";"roofing"] 0.7 0.82 3 FastTime;
    make_contractor "ElectroPro" ["electrical";"plumbing"] 1.1 0.96 2 Specialist;
    make_contractor "BudgetCrew" ["foundation";"framing";"roofing"] 1.4 0.88 4 LowCost;
    make_contractor "FinishLine" ["interior";"roofing"] 0.9 0.90 2 Adaptive;
  ];
  let id1 = fresh_id s in let id2 = fresh_id s in let id3 = fresh_id s in
  let id4 = fresh_id s in let id5 = fresh_id s in let id6 = fresh_id s in
  s.tasks <- [
    (id1, { t_id=id1; t_name="Lay foundation"; t_skills=["foundation"];
             t_complexity=0.6; t_deadline=10; t_parent=None; t_deps=[] }, Pending);
    (id2, { t_id=id2; t_name="Framing"; t_skills=["framing"];
             t_complexity=0.7; t_deadline=16; t_parent=None; t_deps=[id1] }, Pending);
    (id3, { t_id=id3; t_name="Roofing"; t_skills=["roofing"];
             t_complexity=0.5; t_deadline=20; t_parent=None; t_deps=[id2] }, Pending);
    (id4, { t_id=id4; t_name="Electrical wiring"; t_skills=["electrical"];
             t_complexity=0.6; t_deadline=22; t_parent=None; t_deps=[id2] }, Pending);
    (id5, { t_id=id5; t_name="Plumbing"; t_skills=["plumbing"];
             t_complexity=0.5; t_deadline=22; t_parent=None; t_deps=[id2] }, Pending);
    (id6, { t_id=id6; t_name="Interior finishing"; t_skills=["interior"];
             t_complexity=0.8; t_deadline=28; t_parent=None; t_deps=[id3;id4;id5] }, Pending);
  ];
  s

(* ── Display ───────────────────────────────────────────────────────── *)

let print_status s =
  Printf.printf "\n┌─── Task Status ────────────────────────────────────────┐\n";
  List.iter (fun (id, t, st) ->
    Printf.printf "│ [%d] %-25s  %s\n" id t.t_name (task_state_str st)
  ) s.tasks;
  Printf.printf "└────────────────────────────────────────────────────────┘\n"

let print_contractors s =
  Printf.printf "\n┌─── Contractor Fleet ──────────────────────────────────────────────────┐\n";
  Printf.printf "│ %-16s  Skills             Active  Done  Fail  Rep    Strategy\n" "Name";
  Printf.printf "│ ────────────────  ─────────────────  ──────  ────  ────  ─────  ────────\n";
  List.iter (fun c ->
    let strat_str = match c.c_strategy with
      | LowCost -> "low-cost" | FastTime -> "fast" | Balanced -> "balanced"
      | Specialist -> "specialist" | RandomBid -> "random" | Adaptive -> "adaptive" in
    Printf.printf "│ %-16s  %-17s  %d/%d     %d     %d    %.0f%%   %s\n"
      c.c_name (String.concat "," c.c_skills)
      c.c_active c.c_capacity c.c_completed c.c_failed
      (c.c_reputation *. 100.0) strat_str
  ) s.contractors;
  Printf.printf "└───────────────────────────────────────────────────────────────────────┘\n"

let print_summary s =
  Printf.printf "\n╔═══ Final Summary ══════════════════════════════════════╗\n";
  Printf.printf "║ Total steps: %d\n" s.step;
  let completed = List.filter (fun (_, _, st) ->
    match st with Completed _ -> true | _ -> false) s.tasks in
  let total = List.length s.tasks in
  Printf.printf "║ Tasks completed: %d/%d\n" (List.length completed) total;
  Printf.printf "║\n║ Contractor Performance:\n";
  let sorted = List.sort (fun a b -> compare b.c_reputation a.c_reputation) s.contractors in
  List.iter (fun c ->
    let total_tasks = c.c_completed + c.c_failed in
    let rate = if total_tasks > 0 then float_of_int c.c_completed /. float_of_int total_tasks *. 100.0 else 0.0 in
    Printf.printf "║   %-16s  completed=%d  failed=%d  success=%.0f%%  rep=%.0f%%\n"
      c.c_name c.c_completed c.c_failed rate (c.c_reputation *. 100.0)
  ) sorted;
  Printf.printf "╚═══════════════════════════════════════════════════════╝\n"

(* ── REPL ──────────────────────────────────────────────────────────── *)

let print_help () =
  Printf.printf "\nCommands:\n";
  Printf.printf "  step / s       — advance one step\n";
  Printf.printf "  run N          — run N steps\n";
  Printf.printf "  auto           — run to completion (max 50 steps)\n";
  Printf.printf "  status / t     — show task status\n";
  Printf.printf "  fleet / f      — show contractors\n";
  Printf.printf "  log            — show event log\n";
  Printf.printf "  summary        — show final summary\n";
  Printf.printf "  add TASK SKILL COMPLEXITY DEADLINE — add a new task\n";
  Printf.printf "  hire NAME SKILL1,SKILL2 EFF REL CAP STRATEGY — add contractor\n";
  Printf.printf "  award MODE     — set award mode: cheapest|fastest|value:W\n";
  Printf.printf "  help / h       — this help\n";
  Printf.printf "  quit / q       — exit\n"

let run_steps s n =
  for _ = 1 to n do
    if not (all_done s) then sim_step s
  done;
  if all_done s then begin
    Printf.printf "\n🎉 All tasks completed!\n";
    print_summary s
  end

let parse_strategy str = match String.lowercase_ascii str with
  | "low-cost" | "lowcost" | "cheap" -> Some LowCost
  | "fast" | "fastest" -> Some FastTime
  | "balanced" -> Some Balanced
  | "specialist" -> Some Specialist
  | "random" -> Some RandomBid
  | "adaptive" -> Some Adaptive
  | _ -> None

let repl s =
  print_help ();
  print_status s;
  print_contractors s;
  let running = ref true in
  while !running do
    Printf.printf "\ncnet> %!";
    let line = try input_line stdin with End_of_file -> "quit" in
    let parts = String.split_on_char ' ' (String.trim line) in
    match parts with
    | ["quit"] | ["q"] -> running := false
    | ["help"] | ["h"] -> print_help ()
    | ["step"] | ["s"] ->
      if all_done s then Printf.printf "All tasks already completed.\n"
      else (sim_step s; print_status s)
    | ["run"; n] ->
      (try run_steps s (int_of_string n); print_status s
       with _ -> Printf.printf "Usage: run N\n")
    | ["auto"] -> run_steps s 50; print_status s
    | ["status"] | ["t"] -> print_status s
    | ["fleet"] | ["f"] -> print_contractors s
    | ["log"] ->
      Printf.printf "\n── Event Log ──\n";
      List.iter (fun l -> Printf.printf "  %s\n" l) (List.rev s.log)
    | ["summary"] -> print_summary s
    | ["award"; mode] ->
      let strat = match String.lowercase_ascii mode with
        | "cheapest" -> Some Cheapest
        | "fastest" -> Some Fastest
        | s when String.length s > 6 && String.sub s 0 6 = "value:" ->
          (try Some (BestValue (float_of_string (String.sub s 6 (String.length s - 6))))
           with _ -> None)
        | _ -> None in
      (match strat with
       | Some st -> s.award_strat <- st; Printf.printf "Award strategy updated.\n"
       | None -> Printf.printf "Usage: award cheapest|fastest|value:0.5\n")
    | "add" :: name_parts when List.length name_parts >= 3 ->
      let rev = List.rev name_parts in
      (try
        let deadline = int_of_string (List.hd rev) in
        let complexity = float_of_string (List.nth rev 1) in
        let skill = List.nth rev 2 in
        let name = String.concat " " (List.rev (List.tl (List.tl (List.tl rev)))) in
        let id = fresh_id s in
        let task = { t_id=id; t_name=name; t_skills=[skill];
                     t_complexity=complexity; t_deadline=deadline;
                     t_parent=None; t_deps=[] } in
        s.tasks <- s.tasks @ [(id, task, Pending)];
        Printf.printf "Added task '%s' [%d]\n" name id
       with _ -> Printf.printf "Usage: add TASK_NAME SKILL COMPLEXITY DEADLINE\n")
    | "hire" :: name :: rest when List.length rest >= 4 ->
      (try
        let skills_str = List.hd rest in
        let skills = String.split_on_char ',' skills_str in
        let eff = float_of_string (List.nth rest 1) in
        let rel = float_of_string (List.nth rest 2) in
        let cap = int_of_string (List.nth rest 3) in
        let strat = if List.length rest > 4 then
          match parse_strategy (List.nth rest 4) with Some s -> s | None -> Balanced
          else Balanced in
        let c = make_contractor name skills eff rel cap strat in
        s.contractors <- s.contractors @ [c];
        Printf.printf "Hired %s.\n" name
       with _ -> Printf.printf "Usage: hire NAME SKILL1,SKILL2 EFF REL CAP [STRATEGY]\n")
    | [""] -> ()
    | _ -> Printf.printf "Unknown command. Type 'help' for commands.\n"
  done

(* ── Main ──────────────────────────────────────────────────────────── *)

let () =
  Random.self_init ();
  let domain = ref "logistics" in
  let auto = ref false in
  let args = Array.to_list Sys.argv |> List.tl in
  let rec parse = function
    | "--domain" :: d :: rest -> domain := d; parse rest
    | "--auto" :: rest -> auto := true; parse rest
    | _ :: rest -> parse rest
    | [] -> ()
  in
  parse args;
  Printf.printf "╔═══════════════════════════════════════════════════════╗\n";
  Printf.printf "║     Contract Net Protocol Simulator                  ║\n";
  Printf.printf "║     FIPA-style multi-agent task allocation           ║\n";
  Printf.printf "╚═══════════════════════════════════════════════════════╝\n";
  Printf.printf "Domain: %s\n" !domain;
  let s = match !domain with
    | "software" | "sw" -> software_domain ()
    | "construction" | "build" -> construction_domain ()
    | _ -> logistics_domain ()
  in
  if !auto then begin
    run_steps s 50;
    print_status s;
    print_contractors s
  end else
    repl s
