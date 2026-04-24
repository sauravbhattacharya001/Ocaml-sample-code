(* behavior_tree.ml — Behavior Tree Engine
   Hierarchical task planning for autonomous agents with composable
   decision trees, reactive control flow, and runtime introspection.

   Node types:
   - Sequence (run children until one fails)
   - Selector/Fallback (run children until one succeeds)
   - Parallel (run all children, succeed/fail by policy)
   - Decorator: Inverter, Repeat, RetryUntilSuccess, Timeout, Cooldown
   - Condition (predicate check)
   - Action (effectful leaf)

   Features:
   - Blackboard (shared key-value memory)
   - Tick-by-tick execution with Running state
   - Execution trace / tree visualization
   - 3 built-in domains: Robot patrol, NPC behavior, Smart thermostat
   - Interactive REPL

   Usage: ocaml behavior_tree.ml
*)

(* ── Blackboard: shared agent memory ──────────────────────────────── *)

module Blackboard = struct
  type value =
    | Int of int
    | Float of float
    | Str of string
    | Bool of bool

  type t = (string, value) Hashtbl.t

  let create () : t = Hashtbl.create 16

  let set (bb : t) k v = Hashtbl.replace bb k v
  let get (bb : t) k = Hashtbl.find_opt bb k

  let get_int bb k = match get bb k with Some (Int i) -> Some i | _ -> None
  let get_float bb k = match get bb k with Some (Float f) -> Some f | _ -> None
  let get_str bb k = match get bb k with Some (Str s) -> Some s | _ -> None
  let get_bool bb k = match get bb k with Some (Bool b) -> Some b | _ -> None

  let show_value = function
    | Int i -> string_of_int i
    | Float f -> Printf.sprintf "%.2f" f
    | Str s -> Printf.sprintf "%S" s
    | Bool b -> string_of_bool b

  let dump bb =
    Hashtbl.fold (fun k v acc -> (k, show_value v) :: acc) bb []
    |> List.sort compare
end

(* ── Core types ───────────────────────────────────────────────────── *)

type status = Success | Failure | Running

type node =
  | Action of string * (Blackboard.t -> status)
  | Condition of string * (Blackboard.t -> bool)
  | Sequence of string * node list
  | Selector of string * node list
  | Parallel of string * parallel_policy * node list
  | Inverter of string * node
  | Repeat of string * int * node          (* repeat N times *)
  | RetryUntilSuccess of string * int * node  (* max retries *)
  | Cooldown of string * int * node        (* skip for N ticks after success *)
  | AlwaysSucceed of string * node
  | AlwaysFail of string * node

and parallel_policy =
  | RequireAll    (* succeed when all succeed, fail when any fails *)
  | RequireOne    (* succeed when any succeeds, fail when all fail *)

let node_name = function
  | Action (n, _) | Condition (n, _) | Sequence (n, _) | Selector (n, _)
  | Parallel (n, _, _) | Inverter (n, _) | Repeat (n, _, _)
  | RetryUntilSuccess (n, _, _) | Cooldown (n, _, _)
  | AlwaysSucceed (n, _) | AlwaysFail (n, _) -> n

let status_str = function
  | Success -> "✓"
  | Failure -> "✗"
  | Running -> "⟳"

let status_word = function
  | Success -> "SUCCESS"
  | Failure -> "FAILURE"
  | Running -> "RUNNING"

(* ── Tick execution ───────────────────────────────────────────────── *)

type trace_entry = {
  depth : int;
  name : string;
  result : status;
}

type tick_ctx = {
  bb : Blackboard.t;
  mutable tick_num : int;
  mutable trace : trace_entry list;
  (* Per-node state for stateful decorators *)
  cooldown_until : (string, int) Hashtbl.t;
  repeat_count : (string, int) Hashtbl.t;
  retry_count : (string, int) Hashtbl.t;
}

let make_ctx bb = {
  bb;
  tick_num = 0;
  trace = [];
  cooldown_until = Hashtbl.create 8;
  repeat_count = Hashtbl.create 8;
  retry_count = Hashtbl.create 8;
}

let rec tick ctx depth node =
  let log name result =
    ctx.trace <- { depth; name; result } :: ctx.trace;
    result
  in
  match node with
  | Action (name, f) ->
    log name (f ctx.bb)

  | Condition (name, pred) ->
    log name (if pred ctx.bb then Success else Failure)

  | Sequence (name, children) ->
    let rec run = function
      | [] -> Success
      | c :: rest ->
        match tick ctx (depth + 1) c with
        | Success -> run rest
        | other -> other
    in
    log name (run children)

  | Selector (name, children) ->
    let rec run = function
      | [] -> Failure
      | c :: rest ->
        match tick ctx (depth + 1) c with
        | Failure -> run rest
        | other -> other
    in
    log name (run children)

  | Parallel (name, policy, children) ->
    let results = List.map (tick ctx (depth + 1)) children in
    let successes = List.filter (fun r -> r = Success) results in
    let failures = List.filter (fun r -> r = Failure) results in
    let result = match policy with
      | RequireAll ->
        if List.length failures > 0 then Failure
        else if List.length successes = List.length children then Success
        else Running
      | RequireOne ->
        if List.length successes > 0 then Success
        else if List.length failures = List.length children then Failure
        else Running
    in
    log name result

  | Inverter (name, child) ->
    let r = tick ctx (depth + 1) child in
    let result = match r with
      | Success -> Failure | Failure -> Success | Running -> Running
    in
    log name result

  | Repeat (name, n, child) ->
    let key = name in
    let count = try Hashtbl.find ctx.repeat_count key with Not_found -> 0 in
    if count >= n then begin
      Hashtbl.replace ctx.repeat_count key 0;
      log name Success
    end else begin
      let r = tick ctx (depth + 1) child in
      (match r with
       | Success -> Hashtbl.replace ctx.repeat_count key (count + 1)
       | Failure -> Hashtbl.replace ctx.repeat_count key 0
       | Running -> ());
      log name (if r = Failure then Failure else Running)
    end

  | RetryUntilSuccess (name, max_retries, child) ->
    let key = name in
    let count = try Hashtbl.find ctx.retry_count key with Not_found -> 0 in
    let r = tick ctx (depth + 1) child in
    (match r with
     | Success ->
       Hashtbl.replace ctx.retry_count key 0;
       log name Success
     | Failure ->
       if count >= max_retries then begin
         Hashtbl.replace ctx.retry_count key 0;
         log name Failure
       end else begin
         Hashtbl.replace ctx.retry_count key (count + 1);
         log name Running
       end
     | Running -> log name Running)

  | Cooldown (name, ticks, child) ->
    let until = try Hashtbl.find ctx.cooldown_until name with Not_found -> 0 in
    if ctx.tick_num < until then
      log name Failure
    else begin
      let r = tick ctx (depth + 1) child in
      (if r = Success then
         Hashtbl.replace ctx.cooldown_until name (ctx.tick_num + ticks));
      log name r
    end

  | AlwaysSucceed (name, child) ->
    ignore (tick ctx (depth + 1) child);
    log name Success

  | AlwaysFail (name, child) ->
    ignore (tick ctx (depth + 1) child);
    log name Failure

let run_tick ctx root =
  ctx.tick_num <- ctx.tick_num + 1;
  ctx.trace <- [];
  let result = tick ctx 0 root in
  ctx.trace <- List.rev ctx.trace;
  result

(* ── Tree visualization ───────────────────────────────────────────── *)

let rec print_tree ?(indent=0) node =
  let pad = String.make (indent * 2) ' ' in
  let kind = match node with
    | Action _ -> "🎯" | Condition _ -> "❓" | Sequence _ -> "→"
    | Selector _ -> "?" | Parallel _ -> "⇉" | Inverter _ -> "¬"
    | Repeat _ -> "🔁" | RetryUntilSuccess _ -> "♻" | Cooldown _ -> "⏳"
    | AlwaysSucceed _ -> "✓" | AlwaysFail _ -> "✗"
  in
  Printf.printf "%s%s %s\n" pad kind (node_name node);
  match node with
  | Sequence (_, cs) | Selector (_, cs) | Parallel (_, _, cs) ->
    List.iter (print_tree ~indent:(indent + 1)) cs
  | Inverter (_, c) | Repeat (_, _, c) | RetryUntilSuccess (_, _, c)
  | Cooldown (_, _, c) | AlwaysSucceed (_, c) | AlwaysFail (_, c) ->
    print_tree ~indent:(indent + 1) c
  | Action _ | Condition _ -> ()

let print_trace trace =
  List.iter (fun e ->
    let pad = String.make (e.depth * 2) ' ' in
    Printf.printf "  %s%s %s\n" pad (status_str e.result) e.name
  ) trace

(* ── Domain 1: Robot Patrol ───────────────────────────────────────── *)

let make_robot_patrol () =
  let bb = Blackboard.create () in
  Blackboard.set bb "battery" (Int 100);
  Blackboard.set bb "position" (Int 0);
  Blackboard.set bb "target" (Int 5);
  Blackboard.set bb "obstacle" (Bool false);
  Blackboard.set bb "charging" (Bool false);
  let tree =
    Selector ("RobotRoot", [
      (* Priority 1: charge if low battery *)
      Sequence ("ChargeBehavior", [
        Condition ("BatteryLow?", fun bb ->
          match Blackboard.get_int bb "battery" with
          | Some b -> b < 20 | None -> false);
        Action ("GoToCharger", fun bb ->
          Blackboard.set bb "position" (Int 0);
          Blackboard.set bb "charging" (Bool true);
          Printf.printf "    [Robot] Heading to charger...\n";
          Success);
        Action ("Charge", fun bb ->
          let b = match Blackboard.get_int bb "battery" with Some b -> b | None -> 0 in
          let new_b = min 100 (b + 30) in
          Blackboard.set bb "battery" (Int new_b);
          Printf.printf "    [Robot] Charging... battery=%d%%\n" new_b;
          if new_b >= 100 then begin
            Blackboard.set bb "charging" (Bool false);
            Success
          end else Running);
      ]);
      (* Priority 2: avoid obstacle *)
      Sequence ("AvoidObstacle", [
        Condition ("ObstacleAhead?", fun bb ->
          Blackboard.get_bool bb "obstacle" = Some true);
        Action ("Dodge", fun bb ->
          Blackboard.set bb "obstacle" (Bool false);
          Printf.printf "    [Robot] Dodging obstacle!\n";
          Success);
      ]);
      (* Priority 3: patrol *)
      Sequence ("Patrol", [
        Condition ("HasEnergy?", fun bb ->
          match Blackboard.get_int bb "battery" with
          | Some b -> b >= 20 | None -> false);
        Action ("MoveToTarget", fun bb ->
          let pos = match Blackboard.get_int bb "position" with Some p -> p | None -> 0 in
          let target = match Blackboard.get_int bb "target" with Some t -> t | None -> 5 in
          let new_pos = if pos < target then pos + 1
                        else if pos > target then pos - 1 else pos in
          Blackboard.set bb "position" (Int new_pos);
          let b = match Blackboard.get_int bb "battery" with Some b -> b | None -> 100 in
          Blackboard.set bb "battery" (Int (b - 5));
          Printf.printf "    [Robot] Moving to %d (battery=%d%%)\n" new_pos (b - 5);
          if new_pos = target then begin
            (* Pick new random target *)
            let new_target = Random.int 10 in
            Blackboard.set bb "target" (Int new_target);
            Printf.printf "    [Robot] Reached target! New target: %d\n" new_target;
            Success
          end else Running);
      ]);
    ])
  in
  (bb, tree)

(* ── Domain 2: NPC Behavior ───────────────────────────────────────── *)

let make_npc_behavior () =
  let bb = Blackboard.create () in
  Blackboard.set bb "health" (Int 80);
  Blackboard.set bb "enemy_dist" (Int 10);
  Blackboard.set bb "has_potion" (Bool true);
  Blackboard.set bb "gold" (Int 50);
  Blackboard.set bb "reputation" (Int 5);
  let tree =
    Selector ("NPCRoot", [
      (* Emergency: heal *)
      Sequence ("HealSelf", [
        Condition ("LowHealth?", fun bb ->
          Blackboard.get_int bb "health" = Some 20 ||
          (match Blackboard.get_int bb "health" with Some h -> h < 30 | None -> false));
        Condition ("HasPotion?", fun bb ->
          Blackboard.get_bool bb "has_potion" = Some true);
        Action ("DrinkPotion", fun bb ->
          let h = match Blackboard.get_int bb "health" with Some h -> h | None -> 0 in
          Blackboard.set bb "health" (Int (min 100 (h + 40)));
          Blackboard.set bb "has_potion" (Bool false);
          Printf.printf "    [NPC] Drinks potion! Health: %d → %d\n" h (min 100 (h + 40));
          Success);
      ]);
      (* Combat: fight if enemy nearby *)
      Sequence ("Combat", [
        Condition ("EnemyNear?", fun bb ->
          match Blackboard.get_int bb "enemy_dist" with Some d -> d < 5 | None -> false);
        Selector ("FightOrFlee", [
          Sequence ("Fight", [
            Condition ("StrongEnough?", fun bb ->
              match Blackboard.get_int bb "health" with Some h -> h > 40 | None -> false);
            Action ("Attack", fun bb ->
              let d = match Blackboard.get_int bb "enemy_dist" with Some d -> d | None -> 5 in
              let h = match Blackboard.get_int bb "health" with Some h -> h | None -> 100 in
              Blackboard.set bb "health" (Int (h - 10));
              Blackboard.set bb "enemy_dist" (Int (d + 3));
              Blackboard.set bb "gold" (Int (match Blackboard.get_int bb "gold" with Some g -> g + 15 | None -> 15));
              Blackboard.set bb "reputation" (Int (match Blackboard.get_int bb "reputation" with Some r -> r + 1 | None -> 1));
              Printf.printf "    [NPC] Attacks! Enemy retreats to dist=%d, health=%d\n" (d + 3) (h - 10);
              Success);
          ]);
          Action ("Flee", fun bb ->
            let d = match Blackboard.get_int bb "enemy_dist" with Some d -> d | None -> 5 in
            Blackboard.set bb "enemy_dist" (Int (d + 5));
            Printf.printf "    [NPC] Fleeing! Enemy now at dist=%d\n" (d + 5);
            Success);
        ]);
      ]);
      (* Idle: wander and trade *)
      Sequence ("Idle", [
        Action ("Wander", fun bb ->
          let d = match Blackboard.get_int bb "enemy_dist" with Some d -> d | None -> 10 in
          let new_d = max 1 (d + (Random.int 5) - 2) in
          Blackboard.set bb "enemy_dist" (Int new_d);
          Printf.printf "    [NPC] Wandering... enemy_dist=%d\n" new_d;
          Success);
        Cooldown ("TradeCD", 3,
          Action ("Trade", fun bb ->
            let g = match Blackboard.get_int bb "gold" with Some g -> g | None -> 0 in
            Blackboard.set bb "gold" (Int (g + 10));
            Blackboard.set bb "has_potion" (Bool true);
            Printf.printf "    [NPC] Trading! Gold=%d, bought potion\n" (g + 10);
            Success));
      ]);
    ])
  in
  (bb, tree)

(* ── Domain 3: Smart Thermostat ───────────────────────────────────── *)

let make_smart_thermostat () =
  let bb = Blackboard.create () in
  Blackboard.set bb "current_temp" (Float 18.0);
  Blackboard.set bb "target_temp" (Float 22.0);
  Blackboard.set bb "occupied" (Bool true);
  Blackboard.set bb "time_hour" (Int 8);
  Blackboard.set bb "heating_on" (Bool false);
  Blackboard.set bb "cooling_on" (Bool false);
  Blackboard.set bb "energy_used" (Float 0.0);
  let tree =
    Selector ("ThermostatRoot", [
      (* Eco mode when unoccupied *)
      Sequence ("EcoMode", [
        Inverter ("NotOccupied", Condition ("Occupied?", fun bb ->
          Blackboard.get_bool bb "occupied" = Some true));
        Action ("SetEcoTarget", fun bb ->
          Blackboard.set bb "target_temp" (Float 16.0);
          Printf.printf "    [Thermo] Eco mode: target=16°C\n";
          Success);
      ]);
      (* Schedule-aware: night mode *)
      Sequence ("NightMode", [
        Condition ("IsNight?", fun bb ->
          match Blackboard.get_int bb "time_hour" with
          | Some h -> h >= 22 || h < 6 | None -> false);
        Action ("SetNightTarget", fun bb ->
          Blackboard.set bb "target_temp" (Float 19.0);
          Printf.printf "    [Thermo] Night mode: target=19°C\n";
          Success);
      ]);
      (* Active climate control *)
      Parallel ("ClimateControl", RequireOne, [
        Sequence ("Heating", [
          Condition ("TooCold?", fun bb ->
            match Blackboard.get_float bb "current_temp", Blackboard.get_float bb "target_temp" with
            | Some cur, Some tgt -> cur < tgt -. 0.5 | _ -> false);
          Action ("HeatUp", fun bb ->
            let cur = match Blackboard.get_float bb "current_temp" with Some c -> c | None -> 20.0 in
            let new_temp = cur +. 0.8 in
            Blackboard.set bb "current_temp" (Float new_temp);
            Blackboard.set bb "heating_on" (Bool true);
            Blackboard.set bb "cooling_on" (Bool false);
            let e = match Blackboard.get_float bb "energy_used" with Some e -> e | None -> 0.0 in
            Blackboard.set bb "energy_used" (Float (e +. 0.5));
            Printf.printf "    [Thermo] Heating: %.1f°C → %.1f°C (energy: %.1f kWh)\n" cur new_temp (e +. 0.5);
            Success);
        ]);
        Sequence ("Cooling", [
          Condition ("TooHot?", fun bb ->
            match Blackboard.get_float bb "current_temp", Blackboard.get_float bb "target_temp" with
            | Some cur, Some tgt -> cur > tgt +. 0.5 | _ -> false);
          Action ("CoolDown", fun bb ->
            let cur = match Blackboard.get_float bb "current_temp" with Some c -> c | None -> 20.0 in
            let new_temp = cur -. 0.6 in
            Blackboard.set bb "current_temp" (Float new_temp);
            Blackboard.set bb "cooling_on" (Bool true);
            Blackboard.set bb "heating_on" (Bool false);
            let e = match Blackboard.get_float bb "energy_used" with Some e -> e | None -> 0.0 in
            Blackboard.set bb "energy_used" (Float (e +. 0.3));
            Printf.printf "    [Thermo] Cooling: %.1f°C → %.1f°C (energy: %.1f kWh)\n" cur new_temp (e +. 0.3);
            Success);
        ]);
        Sequence ("Stable", [
          Condition ("InRange?", fun bb ->
            match Blackboard.get_float bb "current_temp", Blackboard.get_float bb "target_temp" with
            | Some cur, Some tgt -> Float.abs (cur -. tgt) <= 0.5 | _ -> false);
          Action ("Idle", fun bb ->
            Blackboard.set bb "heating_on" (Bool false);
            Blackboard.set bb "cooling_on" (Bool false);
            let cur = match Blackboard.get_float bb "current_temp" with Some c -> c | None -> 20.0 in
            Printf.printf "    [Thermo] Stable at %.1f°C ✓\n" cur;
            Success);
        ]);
      ]);
    ])
  in
  (bb, tree)

(* ── Simulation runner ────────────────────────────────────────────── *)

let simulate name bb tree ticks =
  Printf.printf "\n═══ %s (%d ticks) ═══\n\n" name ticks;
  print_endline "Tree structure:";
  print_tree tree;
  print_newline ();
  let ctx = make_ctx bb in
  for _ = 1 to ticks do
    Printf.printf "─── Tick %d ───\n" (ctx.tick_num + 1);
    let result = run_tick ctx tree in
    Printf.printf "  Result: %s\n" (status_word result);
    print_endline "  Trace:";
    print_trace ctx.trace;
    print_endline "  Blackboard:";
    List.iter (fun (k, v) ->
      Printf.printf "    %s = %s\n" k v
    ) (Blackboard.dump bb);
    print_newline ()
  done

(* ── Interactive REPL ─────────────────────────────────────────────── *)

let print_help () =
  print_endline "";
  print_endline "╔═══════════════════════════════════════════════════════════╗";
  print_endline "║          Behavior Tree Engine — Interactive REPL         ║";
  print_endline "╠═══════════════════════════════════════════════════════════╣";
  print_endline "║  robot [N]       Run robot patrol for N ticks (def 10)   ║";
  print_endline "║  npc [N]         Run NPC behavior for N ticks (def 10)   ║";
  print_endline "║  thermo [N]      Run thermostat for N ticks (def 10)     ║";
  print_endline "║  demo            Run all 3 domains (5 ticks each)        ║";
  print_endline "║  help            Show this help                          ║";
  print_endline "║  quit            Exit                                    ║";
  print_endline "╚═══════════════════════════════════════════════════════════╝";
  print_endline ""

let parse_ticks parts default =
  match parts with
  | [_; n] -> (try int_of_string n with _ -> default)
  | _ -> default

let repl () =
  print_help ();
  let running = ref true in
  while !running do
    Printf.printf "bt> %!";
    let line = try Some (input_line stdin) with End_of_file -> None in
    match line with
    | None -> running := false
    | Some line ->
      let parts = String.split_on_char ' ' (String.trim line) in
      match parts with
      | ["quit"] | ["exit"] | ["q"] -> running := false
      | ["help"] | ["h"] | ["?"] -> print_help ()
      | "robot" :: _ ->
        let n = parse_ticks parts 10 in
        let (bb, tree) = make_robot_patrol () in
        simulate "Robot Patrol" bb tree n
      | "npc" :: _ ->
        let n = parse_ticks parts 10 in
        let (bb, tree) = make_npc_behavior () in
        simulate "NPC Behavior" bb tree n
      | "thermo" :: _ ->
        let n = parse_ticks parts 10 in
        let (bb, tree) = make_smart_thermostat () in
        simulate "Smart Thermostat" bb tree n
      | ["demo"] ->
        let (bb, tree) = make_robot_patrol () in
        simulate "Robot Patrol" bb tree 5;
        let (bb, tree) = make_npc_behavior () in
        simulate "NPC Behavior" bb tree 5;
        let (bb, tree) = make_smart_thermostat () in
        simulate "Smart Thermostat" bb tree 5
      | [""] -> ()
      | _ -> Printf.printf "Unknown command. Type 'help' for options.\n%!"
  done;
  print_endline "\nGoodbye! 🌳"

let () = repl ()
