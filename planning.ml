(* planning.ml — STRIPS-Style AI Planner
 *
 * A goal-oriented planning system implementing classical AI planning:
 * - STRIPS representation (preconditions, add/delete effects)
 * - Forward state-space search (BFS, DFS, iterative deepening)
 * - A* search with relaxed-plan heuristic
 * - Plan validation and execution simulation
 * - Built-in domains: Blocks World, Logistics, Robot Navigation
 * - Interactive REPL for defining and solving planning problems
 *
 * Usage: ocamlfind ocamlopt -package str -linkpkg planning.ml -o planning
 *        ./planning              # interactive REPL
 *        ./planning --demo       # run built-in demos
 *
 * This is the kind of reasoning that underlies autonomous AI agents:
 * given a current state and a goal, figure out what actions to take.
 *)

(* ── Types ─────────────────────────────────────────────────────────── *)

module StringSet = Set.Make(String)
type state = StringSet.t

type action = {
  name: string;
  parameters: string list;
  preconditions: StringSet.t;
  add_effects: StringSet.t;
  delete_effects: StringSet.t;
}

type plan = action list

type search_strategy = BFS | DFS | IDDeepening | AStar

type search_stats = {
  nodes_expanded: int;
  nodes_generated: int;
  max_frontier: int;
  plan_length: int;
  search_time_ms: float;
}

(* ── State Operations ──────────────────────────────────────────────── *)

let state_of_list preds = StringSet.of_list preds

let state_to_list s = StringSet.elements s

let state_satisfies (state : state) (goal : state) : bool =
  StringSet.subset goal state

let apply_action (state : state) (act : action) : state option =
  if StringSet.subset act.preconditions state then
    let s' = StringSet.diff state act.delete_effects in
    Some (StringSet.union s' act.add_effects)
  else
    None

let applicable_actions (state : state) (actions : action list) : action list =
  List.filter (fun a -> StringSet.subset a.preconditions state) actions

(* ── Plan Validation ───────────────────────────────────────────────── *)

let validate_plan (init : state) (goal : state) (plan : plan) : (state, string) result =
  let rec exec st = function
    | [] ->
      if state_satisfies st goal then Ok st
      else Error "Plan completed but goal not satisfied"
    | act :: rest ->
      match apply_action st act with
      | Some st' -> exec st' rest
      | None -> Error (Printf.sprintf "Action '%s' not applicable at step %d"
                         act.name (List.length plan - List.length rest))
  in
  exec init plan

(* ── Heuristics ────────────────────────────────────────────────────── *)

(* Goal-count heuristic: number of unsatisfied goal predicates *)
let h_goal_count (state : state) (goal : state) : int =
  StringSet.cardinal (StringSet.diff goal state)

(* Relaxed plan heuristic: ignore delete effects, count layers *)
let h_relaxed (state : state) (goal : state) (actions : action list) : int =
  let max_iters = 100 in
  let rec grow st layer =
    if layer >= max_iters then layer
    else if state_satisfies st goal then layer
    else
      let new_facts = List.fold_left (fun acc a ->
          if StringSet.subset a.preconditions st then
            StringSet.union acc a.add_effects
          else acc
        ) StringSet.empty actions
      in
      let st' = StringSet.union st new_facts in
      if StringSet.equal st st' then max_iters  (* unreachable *)
      else grow st' (layer + 1)
  in
  grow state 0

(* ── Search Algorithms ─────────────────────────────────────────────── *)

module StateKey = struct
  type t = string list
  let compare = compare
end
module StateSet = Set.Make(StateKey)

let state_key (s : state) : StateKey.t = StringSet.elements s

(* BFS search *)
let search_bfs (init : state) (goal : state) (actions : action list) : (plan * search_stats) option =
  let t0 = Sys.time () in
  let visited = ref StateSet.empty in
  let expanded = ref 0 in
  let generated = ref 0 in
  let max_front = ref 0 in
  let queue = Queue.create () in
  Queue.add (init, []) queue;
  visited := StateSet.add (state_key init) !visited;
  let result = ref None in
  while not (Queue.is_empty queue) && !result = None do
    let sz = Queue.length queue in
    if sz > !max_front then max_front := sz;
    let (st, path) = Queue.pop queue in
    incr expanded;
    if state_satisfies st goal then
      result := Some (List.rev path)
    else begin
      let apps = applicable_actions st actions in
      List.iter (fun a ->
          match apply_action st a with
          | Some st' ->
            let key = state_key st' in
            if not (StateSet.mem key !visited) then begin
              incr generated;
              visited := StateSet.add key !visited;
              Queue.add (st', a :: path) queue
            end
          | None -> ()
        ) apps
    end
  done;
  let t1 = Sys.time () in
  match !result with
  | Some plan ->
    Some (plan, {
        nodes_expanded = !expanded;
        nodes_generated = !generated;
        max_frontier = !max_front;
        plan_length = List.length plan;
        search_time_ms = (t1 -. t0) *. 1000.0;
      })
  | None -> None

(* DFS search with depth limit *)
let search_dfs ?(max_depth=50) (init : state) (goal : state) (actions : action list)
  : (plan * search_stats) option =
  let t0 = Sys.time () in
  let expanded = ref 0 in
  let generated = ref 0 in
  let best = ref None in
  let rec dfs st path depth visited =
    if !best <> None then ()
    else if state_satisfies st goal then
      best := Some (List.rev path)
    else if depth >= max_depth then ()
    else begin
      incr expanded;
      let apps = applicable_actions st actions in
      List.iter (fun a ->
          match apply_action st a with
          | Some st' ->
            let key = state_key st' in
            if not (StateSet.mem key visited) then begin
              incr generated;
              dfs st' (a :: path) (depth + 1) (StateSet.add key visited)
            end
          | None -> ()
        ) apps
    end
  in
  dfs init [] 0 (StateSet.singleton (state_key init));
  let t1 = Sys.time () in
  match !best with
  | Some plan ->
    Some (plan, {
        nodes_expanded = !expanded;
        nodes_generated = !generated;
        max_frontier = 0;
        plan_length = List.length plan;
        search_time_ms = (t1 -. t0) *. 1000.0;
      })
  | None -> None

(* Iterative deepening *)
let search_id (init : state) (goal : state) (actions : action list) : (plan * search_stats) option =
  let max_depth = 30 in
  let total_expanded = ref 0 in
  let total_generated = ref 0 in
  let t0 = Sys.time () in
  let result = ref None in
  let d = ref 1 in
  while !d <= max_depth && !result = None do
    (match search_dfs ~max_depth:!d init goal actions with
     | Some (plan, stats) ->
       total_expanded := !total_expanded + stats.nodes_expanded;
       total_generated := !total_generated + stats.nodes_generated;
       result := Some plan
     | None ->
       total_expanded := !total_expanded + 0;  (* already counted *)
       incr d)
  done;
  let t1 = Sys.time () in
  match !result with
  | Some plan ->
    Some (plan, {
        nodes_expanded = !total_expanded;
        nodes_generated = !total_generated;
        max_frontier = 0;
        plan_length = List.length plan;
        search_time_ms = (t1 -. t0) *. 1000.0;
      })
  | None -> None

(* A* search *)
module PQ = struct
  type 'a entry = { priority: int; value: 'a; seq: int }
  type 'a t = { mutable data: 'a entry list; mutable counter: int }
  let create () = { data = []; counter = 0 }
  let push pq priority value =
    let e = { priority; value; seq = pq.counter } in
    pq.counter <- pq.counter + 1;
    pq.data <- List.merge (fun a b ->
        let c = compare a.priority b.priority in
        if c <> 0 then c else compare a.seq b.seq
      ) [e] pq.data
  let pop pq = match pq.data with
    | [] -> None
    | e :: rest -> pq.data <- rest; Some e.value
  let is_empty pq = pq.data = []
  let length pq = List.length pq.data
end

let search_astar (init : state) (goal : state) (actions : action list) : (plan * search_stats) option =
  let t0 = Sys.time () in
  let visited = ref StateSet.empty in
  let expanded = ref 0 in
  let generated = ref 0 in
  let max_front = ref 0 in
  let pq = PQ.create () in
  let h0 = h_relaxed init goal actions in
  PQ.push pq h0 (init, [], 0);
  let result = ref None in
  while not (PQ.is_empty pq) && !result = None do
    let sz = PQ.length pq in
    if sz > !max_front then max_front := sz;
    match PQ.pop pq with
    | None -> ()
    | Some (st, path, g) ->
      let key = state_key st in
      if StateSet.mem key !visited then ()
      else begin
        visited := StateSet.add key !visited;
        incr expanded;
        if state_satisfies st goal then
          result := Some (List.rev path)
        else begin
          let apps = applicable_actions st actions in
          List.iter (fun a ->
              match apply_action st a with
              | Some st' ->
                let key' = state_key st' in
                if not (StateSet.mem key' !visited) then begin
                  incr generated;
                  let g' = g + 1 in
                  let h = h_relaxed st' goal actions in
                  PQ.push pq (g' + h) (st', a :: path, g')
                end
              | None -> ()
            ) apps
        end
      end
  done;
  let t1 = Sys.time () in
  match !result with
  | Some plan ->
    Some (plan, {
        nodes_expanded = !expanded;
        nodes_generated = !generated;
        max_frontier = !max_front;
        plan_length = List.length plan;
        search_time_ms = (t1 -. t0) *. 1000.0;
      })
  | None -> None

let search strategy init goal actions =
  match strategy with
  | BFS -> search_bfs init goal actions
  | DFS -> search_dfs init goal actions
  | IDDeepening -> search_id init goal actions
  | AStar -> search_astar init goal actions

(* ── Built-in Domains ──────────────────────────────────────────────── *)

(* Blocks World *)
module BlocksWorld = struct
  let make_actions blocks =
    let actions = ref [] in
    List.iter (fun b ->
        (* pick-up from table *)
        actions := {
          name = Printf.sprintf "pick-up(%s)" b;
          parameters = [b];
          preconditions = state_of_list [
              Printf.sprintf "on-table(%s)" b;
              Printf.sprintf "clear(%s)" b;
              "arm-empty"
            ];
          add_effects = state_of_list [
              Printf.sprintf "holding(%s)" b
            ];
          delete_effects = state_of_list [
              Printf.sprintf "on-table(%s)" b;
              Printf.sprintf "clear(%s)" b;
              "arm-empty"
            ];
        } :: !actions;
        (* put-down to table *)
        actions := {
          name = Printf.sprintf "put-down(%s)" b;
          parameters = [b];
          preconditions = state_of_list [
              Printf.sprintf "holding(%s)" b
            ];
          add_effects = state_of_list [
              Printf.sprintf "on-table(%s)" b;
              Printf.sprintf "clear(%s)" b;
              "arm-empty"
            ];
          delete_effects = state_of_list [
              Printf.sprintf "holding(%s)" b
            ];
        } :: !actions;
        List.iter (fun b2 ->
            if b <> b2 then begin
              (* stack b on b2 *)
              actions := {
                name = Printf.sprintf "stack(%s,%s)" b b2;
                parameters = [b; b2];
                preconditions = state_of_list [
                    Printf.sprintf "holding(%s)" b;
                    Printf.sprintf "clear(%s)" b2
                  ];
                add_effects = state_of_list [
                    Printf.sprintf "on(%s,%s)" b b2;
                    Printf.sprintf "clear(%s)" b;
                    "arm-empty"
                  ];
                delete_effects = state_of_list [
                    Printf.sprintf "holding(%s)" b;
                    Printf.sprintf "clear(%s)" b2
                  ];
              } :: !actions;
              (* unstack b from b2 *)
              actions := {
                name = Printf.sprintf "unstack(%s,%s)" b b2;
                parameters = [b; b2];
                preconditions = state_of_list [
                    Printf.sprintf "on(%s,%s)" b b2;
                    Printf.sprintf "clear(%s)" b;
                    "arm-empty"
                  ];
                add_effects = state_of_list [
                    Printf.sprintf "holding(%s)" b;
                    Printf.sprintf "clear(%s)" b2
                  ];
                delete_effects = state_of_list [
                    Printf.sprintf "on(%s,%s)" b b2;
                    Printf.sprintf "clear(%s)" b;
                    "arm-empty"
                  ];
              } :: !actions
            end
          ) blocks
      ) blocks;
    !actions

  let demo_problem () =
    (* Goal: build tower A on B on C, starting from all on table *)
    let blocks = ["A"; "B"; "C"] in
    let init = state_of_list [
        "on-table(A)"; "on-table(B)"; "on-table(C)";
        "clear(A)"; "clear(B)"; "clear(C)"; "arm-empty"
      ] in
    let goal = state_of_list [
        "on(A,B)"; "on(B,C)"
      ] in
    (init, goal, make_actions blocks)

  let demo_problem_4 () =
    (* 4 blocks: rearrange stacks *)
    let blocks = ["A"; "B"; "C"; "D"] in
    let init = state_of_list [
        "on(A,B)"; "on-table(B)"; "on-table(C)"; "on-table(D)";
        "clear(A)"; "clear(C)"; "clear(D)"; "arm-empty"
      ] in
    let goal = state_of_list [
        "on(D,C)"; "on(C,B)"; "on(B,A)"
      ] in
    (init, goal, make_actions blocks)
end

(* Robot Navigation *)
module RobotNav = struct
  let make_actions rooms connections =
    let actions = ref [] in
    List.iter (fun (r1, r2) ->
        (* bidirectional movement *)
        actions := {
          name = Printf.sprintf "move(%s,%s)" r1 r2;
          parameters = [r1; r2];
          preconditions = state_of_list [
              Printf.sprintf "at(%s)" r1;
              Printf.sprintf "connected(%s,%s)" r1 r2
            ];
          add_effects = state_of_list [Printf.sprintf "at(%s)" r2];
          delete_effects = state_of_list [Printf.sprintf "at(%s)" r1];
        } :: !actions;
        actions := {
          name = Printf.sprintf "move(%s,%s)" r2 r1;
          parameters = [r2; r1];
          preconditions = state_of_list [
              Printf.sprintf "at(%s)" r2;
              Printf.sprintf "connected(%s,%s)" r1 r2
            ];
          add_effects = state_of_list [Printf.sprintf "at(%s)" r1];
          delete_effects = state_of_list [Printf.sprintf "at(%s)" r2];
        } :: !actions
      ) connections;
    (* pick/drop items *)
    List.iter (fun r ->
        List.iter (fun item ->
            actions := {
              name = Printf.sprintf "pick(%s,%s)" item r;
              parameters = [item; r];
              preconditions = state_of_list [
                  Printf.sprintf "at(%s)" r;
                  Printf.sprintf "item-at(%s,%s)" item r;
                  "gripper-free"
                ];
              add_effects = state_of_list [Printf.sprintf "carrying(%s)" item];
              delete_effects = state_of_list [
                  Printf.sprintf "item-at(%s,%s)" item r;
                  "gripper-free"
                ];
            } :: !actions;
            actions := {
              name = Printf.sprintf "drop(%s,%s)" item r;
              parameters = [item; r];
              preconditions = state_of_list [
                  Printf.sprintf "at(%s)" r;
                  Printf.sprintf "carrying(%s)" item
                ];
              add_effects = state_of_list [
                  Printf.sprintf "item-at(%s,%s)" item r;
                  "gripper-free"
                ];
              delete_effects = state_of_list [Printf.sprintf "carrying(%s)" item];
            } :: !actions
          ) ["package1"; "package2"]
      ) rooms;
    !actions

  let demo_problem () =
    let rooms = ["lobby"; "office"; "lab"; "warehouse"] in
    let connections = [
        ("lobby", "office"); ("lobby", "lab");
        ("office", "lab"); ("lab", "warehouse")
      ] in
    let init = state_of_list [
        "at(lobby)"; "gripper-free";
        "item-at(package1,warehouse)"; "item-at(package2,lab)";
        "connected(lobby,office)"; "connected(lobby,lab)";
        "connected(office,lab)"; "connected(lab,warehouse)"
      ] in
    let goal = state_of_list [
        "item-at(package1,office)"; "item-at(package2,office)"
      ] in
    (init, goal, make_actions rooms connections)
end

(* Logistics / Delivery *)
module Logistics = struct
  let make_actions cities routes packages =
    let actions = ref [] in
    (* truck movement *)
    List.iter (fun (c1, c2) ->
        actions := {
          name = Printf.sprintf "drive(%s,%s)" c1 c2;
          parameters = [c1; c2];
          preconditions = state_of_list [
              Printf.sprintf "truck-at(%s)" c1;
              Printf.sprintf "road(%s,%s)" c1 c2
            ];
          add_effects = state_of_list [Printf.sprintf "truck-at(%s)" c2];
          delete_effects = state_of_list [Printf.sprintf "truck-at(%s)" c1];
        } :: !actions;
        actions := {
          name = Printf.sprintf "drive(%s,%s)" c2 c1;
          parameters = [c2; c1];
          preconditions = state_of_list [
              Printf.sprintf "truck-at(%s)" c2;
              Printf.sprintf "road(%s,%s)" c1 c2
            ];
          add_effects = state_of_list [Printf.sprintf "truck-at(%s)" c1];
          delete_effects = state_of_list [Printf.sprintf "truck-at(%s)" c2];
        } :: !actions
      ) routes;
    (* load/unload packages *)
    List.iter (fun city ->
        List.iter (fun pkg ->
            actions := {
              name = Printf.sprintf "load(%s,%s)" pkg city;
              parameters = [pkg; city];
              preconditions = state_of_list [
                  Printf.sprintf "truck-at(%s)" city;
                  Printf.sprintf "pkg-at(%s,%s)" pkg city
                ];
              add_effects = state_of_list [Printf.sprintf "in-truck(%s)" pkg];
              delete_effects = state_of_list [Printf.sprintf "pkg-at(%s,%s)" pkg city];
            } :: !actions;
            actions := {
              name = Printf.sprintf "unload(%s,%s)" pkg city;
              parameters = [pkg; city];
              preconditions = state_of_list [
                  Printf.sprintf "truck-at(%s)" city;
                  Printf.sprintf "in-truck(%s)" pkg
                ];
              add_effects = state_of_list [Printf.sprintf "pkg-at(%s,%s)" pkg city];
              delete_effects = state_of_list [Printf.sprintf "in-truck(%s)" pkg];
            } :: !actions
          ) packages
      ) cities;
    !actions

  let demo_problem () =
    let cities = ["seattle"; "portland"; "sanfrancisco"] in
    let routes = [("seattle", "portland"); ("portland", "sanfrancisco")] in
    let packages = ["electronics"; "food"] in
    let init = state_of_list [
        "truck-at(seattle)";
        "pkg-at(electronics,seattle)"; "pkg-at(food,portland)";
        "road(seattle,portland)"; "road(portland,sanfrancisco)"
      ] in
    let goal = state_of_list [
        "pkg-at(electronics,sanfrancisco)"; "pkg-at(food,sanfrancisco)"
      ] in
    (init, goal, make_actions cities routes packages)
end

(* ── Display ───────────────────────────────────────────────────────── *)

let print_state label st =
  Printf.printf "  %s: {%s}\n" label
    (String.concat ", " (state_to_list st))

let print_plan plan =
  Printf.printf "\n  Plan (%d steps):\n" (List.length plan);
  List.iteri (fun i a ->
      Printf.printf "    %d. %s\n" (i + 1) a.name
    ) plan

let print_stats stats =
  Printf.printf "\n  Search Statistics:\n";
  Printf.printf "    Nodes expanded:  %d\n" stats.nodes_expanded;
  Printf.printf "    Nodes generated: %d\n" stats.nodes_generated;
  if stats.max_frontier > 0 then
    Printf.printf "    Max frontier:    %d\n" stats.max_frontier;
  Printf.printf "    Plan length:     %d\n" stats.plan_length;
  Printf.printf "    Time:            %.2f ms\n" stats.search_time_ms

let strategy_name = function
  | BFS -> "BFS" | DFS -> "DFS" | IDDeepening -> "Iterative Deepening" | AStar -> "A*"

(* ── Demo Runner ───────────────────────────────────────────────────── *)

let run_demo name init goal actions strategies =
  Printf.printf "\n╔══════════════════════════════════════════════════════╗\n";
  Printf.printf "║  %s\n" name;
  Printf.printf "╚══════════════════════════════════════════════════════╝\n";
  print_state "Initial" init;
  print_state "Goal" goal;
  Printf.printf "  Available actions: %d\n" (List.length actions);
  List.iter (fun strat ->
      Printf.printf "\n  ── %s Search ──\n" (strategy_name strat);
      match search strat init goal actions with
      | Some (plan, stats) ->
        print_plan plan;
        print_stats stats;
        (match validate_plan init goal plan with
         | Ok _ -> Printf.printf "    ✓ Plan validated successfully\n"
         | Error e -> Printf.printf "    ✗ Validation failed: %s\n" e)
      | None ->
        Printf.printf "    No plan found.\n"
    ) strategies

let run_demos () =
  Printf.printf "╔══════════════════════════════════════════════════════╗\n";
  Printf.printf "║       STRIPS-Style AI Planner — Demos              ║\n";
  Printf.printf "║       Goal-Oriented Action Planning                 ║\n";
  Printf.printf "╚══════════════════════════════════════════════════════╝\n";

  let strategies = [BFS; AStar] in

  (* Blocks World 3 *)
  let (init, goal, actions) = BlocksWorld.demo_problem () in
  run_demo "Blocks World (3 blocks: build A-B-C tower)" init goal actions strategies;

  (* Blocks World 4 *)
  let (init, goal, actions) = BlocksWorld.demo_problem_4 () in
  run_demo "Blocks World (4 blocks: reverse stack)" init goal actions strategies;

  (* Robot Navigation *)
  let (init, goal, actions) = RobotNav.demo_problem () in
  run_demo "Robot Navigation (deliver 2 packages)" init goal actions strategies;

  (* Logistics *)
  let (init, goal, actions) = Logistics.demo_problem () in
  run_demo "Logistics (truck delivery across 3 cities)" init goal actions strategies;

  Printf.printf "\n══════════════════════════════════════════════════════\n";
  Printf.printf "All demos complete.\n"

(* ── REPL ──────────────────────────────────────────────────────────── *)

type repl_env = {
  mutable preds: StringSet.t;
  mutable goal_preds: StringSet.t;
  mutable user_actions: action list;
}

let env = { preds = StringSet.empty; goal_preds = StringSet.empty; user_actions = [] }

let parse_pred_list s =
  let s = String.trim s in
  if s = "" then []
  else
    String.split_on_char ',' s
    |> List.map String.trim
    |> List.filter (fun x -> x <> "")

let repl () =
  Printf.printf "╔══════════════════════════════════════════════════════╗\n";
  Printf.printf "║       STRIPS Planner — Interactive REPL             ║\n";
  Printf.printf "╚══════════════════════════════════════════════════════╝\n";
  Printf.printf "\nCommands:\n";
  Printf.printf "  init <pred1, pred2, ...>   Set initial state\n";
  Printf.printf "  goal <pred1, pred2, ...>   Set goal state\n";
  Printf.printf "  action <name> pre:<p1,p2> add:<a1,a2> del:<d1,d2>\n";
  Printf.printf "  solve [bfs|dfs|id|astar]   Find a plan\n";
  Printf.printf "  state                      Show current state/goal\n";
  Printf.printf "  actions                    List defined actions\n";
  Printf.printf "  demo blocks|robot|logistics Run built-in demo\n";
  Printf.printf "  clear                      Reset everything\n";
  Printf.printf "  help                       Show this help\n";
  Printf.printf "  quit                       Exit\n\n";
  let running = ref true in
  while !running do
    Printf.printf "planner> %!";
    match try Some (input_line stdin) with End_of_file -> None with
    | None -> running := false
    | Some line ->
      let line = String.trim line in
      if line = "" then ()
      else if line = "quit" || line = "exit" then running := false
      else if line = "help" then begin
        Printf.printf "  init <predicates>   — set initial state (comma-separated)\n";
        Printf.printf "  goal <predicates>   — set goal predicates\n";
        Printf.printf "  action <name> pre:<preds> add:<preds> del:<preds>\n";
        Printf.printf "  solve [bfs|dfs|id|astar]  — search for plan\n";
        Printf.printf "  state / actions / clear / demo / quit\n"
      end
      else if line = "state" then begin
        Printf.printf "  Init: {%s}\n" (String.concat ", " (state_to_list env.preds));
        Printf.printf "  Goal: {%s}\n" (String.concat ", " (state_to_list env.goal_preds))
      end
      else if line = "actions" then begin
        if env.user_actions = [] then Printf.printf "  (no actions defined)\n"
        else List.iter (fun a ->
            Printf.printf "  %s  pre:{%s}  add:{%s}  del:{%s}\n"
              a.name
              (String.concat "," (state_to_list a.preconditions))
              (String.concat "," (state_to_list a.add_effects))
              (String.concat "," (state_to_list a.delete_effects))
          ) env.user_actions
      end
      else if line = "clear" then begin
        env.preds <- StringSet.empty;
        env.goal_preds <- StringSet.empty;
        env.user_actions <- [];
        Printf.printf "  Cleared.\n"
      end
      else if String.length line > 5 && String.sub line 0 5 = "init " then begin
        let rest = String.sub line 5 (String.length line - 5) in
        env.preds <- state_of_list (parse_pred_list rest);
        Printf.printf "  Initial state set (%d predicates)\n" (StringSet.cardinal env.preds)
      end
      else if String.length line > 5 && String.sub line 0 5 = "goal " then begin
        let rest = String.sub line 5 (String.length line - 5) in
        env.goal_preds <- state_of_list (parse_pred_list rest);
        Printf.printf "  Goal set (%d predicates)\n" (StringSet.cardinal env.goal_preds)
      end
      else if String.length line > 7 && String.sub line 0 7 = "action " then begin
        (* parse: action name pre:a,b add:c,d del:e,f *)
        let parts = String.split_on_char ' ' (String.sub line 7 (String.length line - 7)) in
        let parts = List.filter (fun s -> s <> "") parts in
        match parts with
        | name :: rest ->
          let pre = ref [] and add = ref [] and del = ref [] in
          List.iter (fun p ->
              if String.length p > 4 && String.sub p 0 4 = "pre:" then
                pre := parse_pred_list (String.sub p 4 (String.length p - 4))
              else if String.length p > 4 && String.sub p 0 4 = "add:" then
                add := parse_pred_list (String.sub p 4 (String.length p - 4))
              else if String.length p > 4 && String.sub p 0 4 = "del:" then
                del := parse_pred_list (String.sub p 4 (String.length p - 4))
            ) rest;
          let act = {
            name; parameters = [];
            preconditions = state_of_list !pre;
            add_effects = state_of_list !add;
            delete_effects = state_of_list !del;
          } in
          env.user_actions <- act :: env.user_actions;
          Printf.printf "  Action '%s' added\n" name
        | [] -> Printf.printf "  Usage: action <name> pre:... add:... del:...\n"
      end
      else if String.length line >= 5 && String.sub line 0 5 = "solve" then begin
        let strat =
          let rest = String.trim (
              if String.length line > 5 then String.sub line 6 (String.length line - 6)
              else ""
            ) in
          match rest with
          | "bfs" -> BFS | "dfs" -> DFS | "id" -> IDDeepening
          | "astar" | "a*" -> AStar | _ -> AStar
        in
        if StringSet.is_empty env.preds then
          Printf.printf "  Error: set initial state first (init ...)\n"
        else if StringSet.is_empty env.goal_preds then
          Printf.printf "  Error: set goal first (goal ...)\n"
        else if env.user_actions = [] then
          Printf.printf "  Error: define actions first (action ...)\n"
        else begin
          Printf.printf "  Searching with %s...\n" (strategy_name strat);
          match search strat env.preds env.goal_preds env.user_actions with
          | Some (plan, stats) ->
            print_plan plan; print_stats stats;
            (match validate_plan env.preds env.goal_preds plan with
             | Ok _ -> Printf.printf "    ✓ Plan valid\n"
             | Error e -> Printf.printf "    ✗ %s\n" e)
          | None -> Printf.printf "  No plan found.\n"
        end
      end
      else if String.length line >= 4 && String.sub line 0 4 = "demo" then begin
        let rest = String.trim (
            if String.length line > 4 then String.sub line 5 (String.length line - 5)
            else ""
          ) in
        let strategies = [BFS; AStar] in
        (match rest with
         | "blocks" ->
           let (i, g, a) = BlocksWorld.demo_problem () in
           run_demo "Blocks World (3 blocks)" i g a strategies
         | "robot" ->
           let (i, g, a) = RobotNav.demo_problem () in
           run_demo "Robot Navigation" i g a strategies
         | "logistics" ->
           let (i, g, a) = Logistics.demo_problem () in
           run_demo "Logistics" i g a strategies
         | _ -> Printf.printf "  Demos: blocks, robot, logistics\n")
      end
      else
        Printf.printf "  Unknown command. Type 'help' for usage.\n"
  done;
  Printf.printf "Goodbye!\n"

(* ── Main ──────────────────────────────────────────────────────────── *)

let () =
  let args = Array.to_list Sys.argv in
  if List.mem "--demo" args || List.mem "-d" args then
    run_demos ()
  else
    repl ()
