(* BDI Agent Simulator — Belief-Desire-Intention autonomous agent framework
   
   Implements the classic BDI architecture:
   - Beliefs: agent's knowledge about the world (key-value store)
   - Desires: goals the agent wants to achieve (conditions on beliefs)
   - Intentions: committed plans being executed
   - Plan Library: plans with preconditions, body steps, and effects
   - Deliberation Cycle: belief revision → option generation → filtering → execution
   
   Features:
   - Multiple agent support with message passing
   - Built-in plan library with customizable plans
   - Step-by-step or continuous execution
   - Event-driven reactivity (external events trigger plan adoption)
   - 3 built-in domains (logistics, smart-home, trading)
   - Interactive REPL
   
   Usage: ocaml bdi_agent.ml
*)

(* ========== Core Types ========== *)

module StringMap = Map.Make(String)
module StringSet = Set.Make(String)

type belief = string * string  (* key, value *)

type condition =
  | HasBelief of string * string       (* key = value *)
  | NotBelief of string * string       (* key <> value *)
  | HasKey of string                   (* key exists *)
  | NotKey of string                   (* key doesn't exist *)

type action =
  | SetBelief of string * string       (* set key = value *)
  | RemoveBelief of string             (* remove key *)
  | Print of string                    (* output message *)
  | SendMessage of string * string * string  (* to_agent, performative, content *)
  | Wait of int                        (* wait N cycles *)
  | Subgoal of string                  (* adopt a subgoal *)

type plan = {
  plan_name: string;
  trigger: string;                     (* event/goal that triggers this plan *)
  preconditions: condition list;
  body: action list;
  postconditions: (string * string) list;  (* beliefs to set on completion *)
  priority: int;
}

type desire = {
  desire_name: string;
  goal_condition: condition list;      (* satisfied when all true *)
  priority: int;
  persistent: bool;                    (* re-adopt if condition becomes false *)
}

type intention = {
  from_plan: string;
  remaining_actions: action list;
  wait_counter: int;
}

type message = {
  from_agent: string;
  performative: string;  (* inform, request, propose, accept, reject *)
  content: string;
}

type agent = {
  name: string;
  beliefs: string StringMap.t;
  desires: desire list;
  intentions: intention list;
  plan_library: plan list;
  inbox: message list;
  cycle_count: int;
  log: string list;
}

(* ========== Condition Evaluation ========== *)

let eval_condition beliefs = function
  | HasBelief (k, v) ->
    (match StringMap.find_opt k beliefs with Some v2 -> v2 = v | None -> false)
  | NotBelief (k, v) ->
    (match StringMap.find_opt k beliefs with Some v2 -> v2 <> v | None -> true)
  | HasKey k -> StringMap.mem k beliefs
  | NotKey k -> not (StringMap.mem k beliefs)

let eval_conditions beliefs conds =
  List.for_all (eval_condition beliefs) conds

(* ========== Agent Operations ========== *)

let create_agent name plans desires =
  { name; beliefs = StringMap.empty; desires; intentions = [];
    plan_library = plans; inbox = []; cycle_count = 0; log = [] }

let add_belief agent k v =
  { agent with beliefs = StringMap.add k v agent.beliefs }

let remove_belief agent k =
  { agent with beliefs = StringMap.remove k agent.beliefs }

let add_log agent msg =
  let entry = Printf.sprintf "[%s@%d] %s" agent.name agent.cycle_count msg in
  { agent with log = entry :: agent.log }

(* ========== Deliberation Cycle ========== *)

(* Phase 1: Belief Revision from inbox *)
let revise_beliefs agent =
  let process_msg ag msg =
    let ag = add_log ag (Printf.sprintf "Received %s from %s: %s"
      msg.performative msg.from_agent msg.content) in
    match msg.performative with
    | "inform" ->
      (* Parse "key=value" *)
      (match String.split_on_char '=' msg.content with
       | [k; v] -> add_belief ag (String.trim k) (String.trim v)
       | _ -> ag)
    | "request" ->
      (* Add a goal belief *)
      add_belief ag ("requested:" ^ msg.content) "true"
    | _ -> ag
  in
  let agent = List.fold_left process_msg agent agent.inbox in
  { agent with inbox = [] }

(* Phase 2: Option Generation — find desires not yet satisfied & not intended *)
let generate_options agent =
  let intended_goals = List.map (fun i -> i.from_plan) agent.intentions in
  let unsatisfied = List.filter (fun d ->
    not (eval_conditions agent.beliefs d.goal_condition) &&
    not (List.mem d.desire_name intended_goals)
  ) agent.desires in
  (* Sort by priority descending *)
  List.sort (fun a b -> compare b.priority a.priority) unsatisfied

(* Phase 3: Filter — select applicable plans for options *)
let select_plans agent options =
  let find_plan_for desire =
    let applicable = List.filter (fun p ->
      p.trigger = desire.desire_name &&
      eval_conditions agent.beliefs p.preconditions
    ) agent.plan_library in
    let sorted = List.sort (fun a b -> compare b.priority a.priority) applicable in
    match sorted with
    | p :: _ -> Some { from_plan = p.plan_name; remaining_actions = p.body; wait_counter = 0 }
    | [] -> None
  in
  List.filter_map find_plan_for options

(* Phase 4: Execute one step of each intention *)
type exec_result = {
  agent: agent;
  outbox: (string * message) list;  (* (recipient, message) *)
  subgoals: string list;
}

let execute_intentions agent =
  let outbox = ref [] in
  let subgoals = ref [] in
  let step_intention ag intention =
    if intention.wait_counter > 0 then
      (ag, Some { intention with wait_counter = intention.wait_counter - 1 })
    else
      match intention.remaining_actions with
      | [] ->
        (* Plan completed — apply postconditions from plan library *)
        let plan_opt = List.find_opt (fun p -> p.plan_name = intention.from_plan)
          ag.plan_library in
        let ag = match plan_opt with
          | Some plan ->
            List.fold_left (fun a (k,v) -> add_belief a k v) ag plan.postconditions
          | None -> ag
        in
        let ag = add_log ag (Printf.sprintf "Plan '%s' completed" intention.from_plan) in
        (ag, None)
      | action :: rest ->
        let intention' = { intention with remaining_actions = rest } in
        match action with
        | SetBelief (k, v) ->
          let ag = add_belief ag k v in
          let ag = add_log ag (Printf.sprintf "Set belief %s=%s" k v) in
          (ag, Some intention')
        | RemoveBelief k ->
          let ag = remove_belief ag k in
          let ag = add_log ag (Printf.sprintf "Removed belief %s" k) in
          (ag, Some intention')
        | Print msg ->
          let ag = add_log ag (Printf.sprintf ">>> %s" msg) in
          (ag, Some intention')
        | SendMessage (to_ag, perf, content) ->
          outbox := (to_ag, { from_agent = ag.name; performative = perf; content }) :: !outbox;
          let ag = add_log ag (Printf.sprintf "Sent %s to %s: %s" perf to_ag content) in
          (ag, Some intention')
        | Wait n ->
          let ag = add_log ag (Printf.sprintf "Waiting %d cycles" n) in
          (ag, Some { intention with remaining_actions = rest; wait_counter = n })
        | Subgoal g ->
          subgoals := g :: !subgoals;
          let ag = add_log ag (Printf.sprintf "Adopted subgoal: %s" g) in
          (ag, Some intention')
  in
  let ag_ref = ref agent in
  let new_intentions = List.filter_map (fun i ->
    let (ag, i') = step_intention !ag_ref i in
    ag_ref := ag;
    i'
  ) agent.intentions in
  { agent = { !ag_ref with intentions = new_intentions };
    outbox = !outbox; subgoals = !subgoals }

(* Full deliberation cycle *)
let deliberate agent =
  let agent = revise_beliefs agent in
  let options = generate_options agent in
  let new_intentions = select_plans agent options in
  let agent = { agent with
    intentions = agent.intentions @ new_intentions;
    cycle_count = agent.cycle_count + 1 }
  in
  let agent = if new_intentions <> [] then
    add_log agent (Printf.sprintf "Adopted %d new intention(s): %s"
      (List.length new_intentions)
      (String.concat ", " (List.map (fun i -> i.from_plan) new_intentions)))
  else agent
  in
  execute_intentions agent

(* ========== Multi-Agent System ========== *)

type world = {
  agents: agent StringMap.t;
  global_cycle: int;
}

let create_world agents =
  let map = List.fold_left (fun m a -> StringMap.add a.name a m)
    StringMap.empty agents in
  { agents = map; global_cycle = 0 }

let world_step world =
  let deliver_messages outbox agents =
    List.fold_left (fun ags (recipient, msg) ->
      match StringMap.find_opt recipient ags with
      | Some ag -> StringMap.add recipient { ag with inbox = ag.inbox @ [msg] } ags
      | None -> ags
    ) agents outbox
  in
  let all_outbox = ref [] in
  let agents = StringMap.map (fun agent ->
    let result = deliberate agent in
    all_outbox := !all_outbox @ result.outbox;
    (* Handle subgoals by adding temporary desires *)
    let extra_desires = List.map (fun g ->
      { desire_name = g; goal_condition = [HasBelief (g, "done")];
        priority = 10; persistent = false }
    ) result.subgoals in
    { result.agent with desires = result.agent.desires @ extra_desires }
  ) world.agents in
  let agents = deliver_messages !all_outbox agents in
  { agents; global_cycle = world.global_cycle + 1 }

(* ========== Built-in Domains ========== *)

(* Domain 1: Logistics — pickup and deliver packages *)
let logistics_plans = [
  { plan_name = "pickup_package";
    trigger = "deliver_package";
    preconditions = [HasBelief ("package_location", "warehouse"); NotKey "holding_package"];
    body = [
      Print "Navigating to warehouse...";
      SetBelief ("agent_location", "warehouse");
      Print "Picking up package";
      SetBelief ("holding_package", "true");
      RemoveBelief "package_location";
      Subgoal "transport_package";
    ];
    postconditions = [];
    priority = 5;
  };
  { plan_name = "transport_to_dest";
    trigger = "transport_package";
    preconditions = [HasBelief ("holding_package", "true"); HasKey "destination"];
    body = [
      Print "Transporting package to destination...";
      Wait 2;
      Print "Arrived at destination";
      SetBelief ("holding_package", "false");
      SetBelief ("package_delivered", "true");
      Print "Package delivered successfully!";
    ];
    postconditions = [("transport_package", "done"); ("deliver_package", "done")];
    priority = 5;
  };
  { plan_name = "report_delivery";
    trigger = "notify_sender";
    preconditions = [HasBelief ("package_delivered", "true")];
    body = [
      SendMessage ("dispatcher", "inform", "package_delivered=true");
      Print "Dispatcher notified of delivery";
    ];
    postconditions = [("notify_sender", "done")];
    priority = 3;
  };
]

let logistics_desires = [
  { desire_name = "deliver_package";
    goal_condition = [HasBelief ("package_delivered", "true")];
    priority = 10; persistent = false };
  { desire_name = "notify_sender";
    goal_condition = [HasBelief ("notify_sender", "done")];
    priority = 5; persistent = false };
]

let dispatcher_plans = [
  { plan_name = "ack_delivery";
    trigger = "process_notification";
    preconditions = [HasBelief ("package_delivered", "true")];
    body = [
      Print "Delivery confirmed! Updating records.";
      SetBelief ("records_updated", "true");
    ];
    postconditions = [("process_notification", "done")];
    priority = 5;
  };
]

let dispatcher_desires = [
  { desire_name = "process_notification";
    goal_condition = [HasBelief ("records_updated", "true")];
    priority = 5; persistent = true };
]

(* Domain 2: Smart Home *)
let smarthome_plans = [
  { plan_name = "adjust_temp_hot";
    trigger = "comfort_control";
    preconditions = [HasBelief ("temperature", "hot")];
    body = [
      Print "Temperature is too hot — turning on AC";
      SetBelief ("ac", "on");
      SetBelief ("temperature", "comfortable");
      Print "AC activated. Temperature normalizing.";
    ];
    postconditions = [("comfort_control", "done")];
    priority = 8;
  };
  { plan_name = "adjust_temp_cold";
    trigger = "comfort_control";
    preconditions = [HasBelief ("temperature", "cold")];
    body = [
      Print "Temperature is too cold — turning on heater";
      SetBelief ("heater", "on");
      SetBelief ("temperature", "comfortable");
      Print "Heater activated. Temperature normalizing.";
    ];
    postconditions = [("comfort_control", "done")];
    priority = 8;
  };
  { plan_name = "security_alert";
    trigger = "security_check";
    preconditions = [HasBelief ("motion_detected", "true"); HasBelief ("home_occupied", "false")];
    body = [
      Print "⚠ INTRUSION DETECTED! Home unoccupied but motion sensed.";
      SetBelief ("alarm", "on");
      SetBelief ("cameras", "recording");
      SendMessage ("owner", "inform", "alarm=triggered");
      Print "Alarm activated, cameras recording, owner notified.";
    ];
    postconditions = [("security_check", "done")];
    priority = 10;
  };
  { plan_name = "lights_evening";
    trigger = "lighting_control";
    preconditions = [HasBelief ("time_of_day", "evening"); HasBelief ("lights", "off")];
    body = [
      Print "Evening detected — turning on ambient lights";
      SetBelief ("lights", "on");
      SetBelief ("light_mode", "ambient");
    ];
    postconditions = [("lighting_control", "done")];
    priority = 4;
  };
]

let smarthome_desires = [
  { desire_name = "comfort_control";
    goal_condition = [HasBelief ("temperature", "comfortable")];
    priority = 8; persistent = true };
  { desire_name = "security_check";
    goal_condition = [HasBelief ("security_check", "done")];
    priority = 10; persistent = true };
  { desire_name = "lighting_control";
    goal_condition = [HasBelief ("lighting_control", "done")];
    priority = 4; persistent = true };
]

(* Domain 3: Trading Agent *)
let trading_plans = [
  { plan_name = "buy_low";
    trigger = "profit_strategy";
    preconditions = [HasBelief ("price_trend", "falling"); HasBelief ("has_cash", "true")];
    body = [
      Print "Price trend falling — buying opportunity detected";
      SetBelief ("position", "long");
      SetBelief ("has_cash", "false");
      Print "Bought asset. Holding long position.";
    ];
    postconditions = [];
    priority = 7;
  };
  { plan_name = "sell_high";
    trigger = "profit_strategy";
    preconditions = [HasBelief ("price_trend", "rising"); HasBelief ("position", "long")];
    body = [
      Print "Price trend rising with long position — selling!";
      SetBelief ("position", "none");
      SetBelief ("has_cash", "true");
      SetBelief ("last_trade", "profit");
      Print "Sold for profit! Position closed.";
    ];
    postconditions = [("profit_strategy", "done")];
    priority = 7;
  };
  { plan_name = "stop_loss";
    trigger = "risk_management";
    preconditions = [HasBelief ("price_trend", "crashing"); HasBelief ("position", "long")];
    body = [
      Print "⚠ CRASH DETECTED — executing stop-loss!";
      SetBelief ("position", "none");
      SetBelief ("has_cash", "true");
      SetBelief ("last_trade", "loss");
      Print "Stop-loss executed. Capital preserved.";
    ];
    postconditions = [("risk_management", "done")];
    priority = 10;
  };
  { plan_name = "report_portfolio";
    trigger = "status_report";
    preconditions = [];
    body = [
      Print "=== Portfolio Status Report ===";
      Subgoal "analyze_risk";
    ];
    postconditions = [("status_report", "done")];
    priority = 2;
  };
]

let trading_desires = [
  { desire_name = "profit_strategy";
    goal_condition = [HasBelief ("profit_strategy", "done")];
    priority = 7; persistent = true };
  { desire_name = "risk_management";
    goal_condition = [HasBelief ("risk_management", "done")];
    priority = 10; persistent = true };
]

(* ========== Display ========== *)

let show_beliefs beliefs =
  if StringMap.is_empty beliefs then
    Printf.printf "  (no beliefs)\n"
  else
    StringMap.iter (fun k v -> Printf.printf "  %s = %s\n" k v) beliefs

let show_desires desires =
  if desires = [] then Printf.printf "  (no desires)\n"
  else List.iter (fun d ->
    Printf.printf "  [%d] %s%s\n" d.priority d.desire_name
      (if d.persistent then " (persistent)" else "")
  ) desires

let show_intentions intentions =
  if intentions = [] then Printf.printf "  (no active intentions)\n"
  else List.iter (fun i ->
    let remaining = List.length i.remaining_actions in
    let wait = if i.wait_counter > 0 then Printf.sprintf " (waiting %d)" i.wait_counter else "" in
    Printf.printf "  Plan '%s': %d steps remaining%s\n" i.from_plan remaining wait
  ) intentions

let show_agent agent =
  Printf.printf "\n══════ Agent: %s (cycle %d) ══════\n" agent.name agent.cycle_count;
  Printf.printf "Beliefs:\n"; show_beliefs agent.beliefs;
  Printf.printf "Desires:\n"; show_desires agent.desires;
  Printf.printf "Intentions:\n"; show_intentions agent.intentions;
  Printf.printf "Inbox: %d message(s)\n" (List.length agent.inbox)

let show_log agent n =
  let recent = List.filteri (fun i _ -> i < n) agent.log in
  List.iter (fun l -> Printf.printf "  %s\n" l) (List.rev recent)

let show_world world =
  Printf.printf "\n╔══════════════════════════════════════╗\n";
  Printf.printf "║  BDI World — Global Cycle %-4d       ║\n" world.global_cycle;
  Printf.printf "╚══════════════════════════════════════╝\n";
  StringMap.iter (fun _ agent -> show_agent agent) world.agents

(* ========== REPL ========== *)

let print_help () =
  Printf.printf "\n";
  Printf.printf "╔══════════════════════════════════════════════════════╗\n";
  Printf.printf "║         BDI Agent Simulator — Commands              ║\n";
  Printf.printf "╠══════════════════════════════════════════════════════╣\n";
  Printf.printf "║  step [N]           Run N deliberation cycles (1)   ║\n";
  Printf.printf "║  run                Run until all intentions done   ║\n";
  Printf.printf "║  show [agent]       Show world or specific agent    ║\n";
  Printf.printf "║  log <agent> [N]    Show last N log entries (10)    ║\n";
  Printf.printf "║  believe <ag> <k> <v>  Set agent belief             ║\n";
  Printf.printf "║  forget <ag> <k>      Remove agent belief           ║\n";
  Printf.printf "║  send <from> <to> <perf> <content>  Send message    ║\n";
  Printf.printf "║  desire <ag> <name> <priority>  Add desire          ║\n";
  Printf.printf "║  domain <name>      Load domain (logistics|home|    ║\n";
  Printf.printf "║                     trading)                        ║\n";
  Printf.printf "║  reset              Reset world                     ║\n";
  Printf.printf "║  help               Show this help                  ║\n";
  Printf.printf "║  quit               Exit                            ║\n";
  Printf.printf "╚══════════════════════════════════════════════════════╝\n";
  Printf.printf "\n"

let setup_logistics () =
  let courier = create_agent "courier" logistics_plans logistics_desires in
  let courier = add_belief courier "package_location" "warehouse" in
  let courier = add_belief courier "destination" "customer_address" in
  let dispatcher = create_agent "dispatcher" dispatcher_plans dispatcher_desires in
  create_world [courier; dispatcher]

let setup_smarthome () =
  let home = create_agent "home_agent" smarthome_plans smarthome_desires in
  let home = add_belief home "temperature" "hot" in
  let home = add_belief home "time_of_day" "evening" in
  let home = add_belief home "lights" "off" in
  let home = add_belief home "home_occupied" "false" in
  let home = add_belief home "motion_detected" "true" in
  let owner = create_agent "owner" [] [] in
  create_world [home; owner]

let setup_trading () =
  let trader = create_agent "trader" trading_plans trading_desires in
  let trader = add_belief trader "price_trend" "falling" in
  let trader = add_belief trader "has_cash" "true" in
  create_world [trader]

let () =
  Printf.printf "\n";
  Printf.printf "╔══════════════════════════════════════════════════════╗\n";
  Printf.printf "║     🧠 BDI Agent Simulator                         ║\n";
  Printf.printf "║     Belief-Desire-Intention Architecture            ║\n";
  Printf.printf "╠══════════════════════════════════════════════════════╣\n";
  Printf.printf "║  Autonomous agents that reason about goals,         ║\n";
  Printf.printf "║  select plans, and execute intentions.              ║\n";
  Printf.printf "║                                                     ║\n";
  Printf.printf "║  Domains: logistics, home, trading                  ║\n";
  Printf.printf "║  Type 'help' for commands, 'domain <name>' to load ║\n";
  Printf.printf "╚══════════════════════════════════════════════════════╝\n";
  Printf.printf "\n";
  let world = ref (setup_logistics ()) in
  Printf.printf "Loaded 'logistics' domain (courier + dispatcher)\n";
  show_world !world;
  Printf.printf "\nbdi> ";
  let running = ref true in
  while !running do
    match input_line stdin with
    | exception End_of_file -> running := false
    | line ->
      let parts = String.split_on_char ' ' (String.trim line) in
      (match parts with
       | ["quit"] | ["exit"] | ["q"] ->
         Printf.printf "Goodbye!\n"; running := false
       | ["help"] | ["h"] | ["?"] ->
         print_help ()
       | ["step"] ->
         world := world_step !world;
         show_world !world
       | ["step"; n_str] ->
         let n = try int_of_string n_str with _ -> 1 in
         for _ = 1 to n do world := world_step !world done;
         show_world !world
       | ["run"] ->
         let max_cycles = 50 in
         let i = ref 0 in
         let has_intentions () =
           StringMap.exists (fun _ ag -> ag.intentions <> []) (!world).agents in
         while !i < max_cycles && has_intentions () do
           world := world_step !world;
           incr i
         done;
         Printf.printf "\nRan %d cycles.\n" !i;
         show_world !world
       | ["show"] -> show_world !world
       | ["show"; ag_name] ->
         (match StringMap.find_opt ag_name (!world).agents with
          | Some ag -> show_agent ag
          | None -> Printf.printf "Unknown agent: %s\n" ag_name)
       | ["log"; ag_name] ->
         (match StringMap.find_opt ag_name (!world).agents with
          | Some ag -> show_log ag 10
          | None -> Printf.printf "Unknown agent: %s\n" ag_name)
       | ["log"; ag_name; n_str] ->
         (match StringMap.find_opt ag_name (!world).agents with
          | Some ag -> show_log ag (try int_of_string n_str with _ -> 10)
          | None -> Printf.printf "Unknown agent: %s\n" ag_name)
       | "believe" :: ag_name :: k :: v_parts when v_parts <> [] ->
         let v = String.concat " " v_parts in
         world := { !world with agents =
           StringMap.update ag_name (Option.map (fun ag -> add_belief ag k v))
             (!world).agents };
         Printf.printf "Set %s's belief: %s = %s\n" ag_name k v
       | ["forget"; ag_name; k] ->
         world := { !world with agents =
           StringMap.update ag_name (Option.map (fun ag -> remove_belief ag k))
             (!world).agents };
         Printf.printf "Removed %s's belief: %s\n" ag_name k
       | "send" :: from_ag :: to_ag :: perf :: content_parts when content_parts <> [] ->
         let content = String.concat " " content_parts in
         let msg = { from_agent = from_ag; performative = perf; content } in
         world := { !world with agents =
           StringMap.update to_ag
             (Option.map (fun ag -> { ag with inbox = ag.inbox @ [msg] }))
             (!world).agents };
         Printf.printf "Message sent: %s -> %s [%s] %s\n" from_ag to_ag perf content
       | "desire" :: ag_name :: d_name :: prio_parts ->
         let prio = match prio_parts with
           | [s] -> (try int_of_string s with _ -> 5) | _ -> 5 in
         let d = { desire_name = d_name; goal_condition = [HasBelief (d_name, "done")];
                    priority = prio; persistent = false } in
         world := { !world with agents =
           StringMap.update ag_name
             (Option.map (fun ag -> { ag with desires = ag.desires @ [d] }))
             (!world).agents };
         Printf.printf "Added desire '%s' to %s (priority %d)\n" d_name ag_name prio
       | ["domain"; "logistics"] ->
         world := setup_logistics ();
         Printf.printf "Loaded 'logistics' domain\n"; show_world !world
       | ["domain"; "home"] ->
         world := setup_smarthome ();
         Printf.printf "Loaded 'smart-home' domain\n"; show_world !world
       | ["domain"; "trading"] ->
         world := setup_trading ();
         Printf.printf "Loaded 'trading' domain\n"; show_world !world
       | ["domain"; _] ->
         Printf.printf "Available domains: logistics, home, trading\n"
       | ["reset"] ->
         world := create_world [];
         Printf.printf "World reset (empty). Use 'domain <name>' to load.\n"
       | [""] -> ()
       | _ -> Printf.printf "Unknown command. Type 'help' for available commands.\n");
      if !running then Printf.printf "bdi> "
  done
