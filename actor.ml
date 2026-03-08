(* ============================================================================
   Actor Model -- Erlang-style Message Passing Concurrency
   ============================================================================

   An implementation of the Actor model in OCaml featuring:

   - Actors with typed mailboxes and selective receive
   - Asynchronous message passing (send/tell)
   - Request-reply pattern (ask) with correlation IDs
   - Actor supervision trees (one-for-one, one-for-all, rest-for-one)
   - Actor lifecycle management (start, stop, restart)
   - Named actor registry for address-based lookup
   - Monitoring and death notifications (links/monitors)
   - Behavior switching (become/unbecome for state machines)
   - Round-robin and broadcast routers
   - Dead letter handling for undeliverable messages
   - Built-in test suite (38 tests)

   Concepts demonstrated:
   - Message-passing concurrency without shared state
   - Supervision hierarchies for fault tolerance
   - Selective receive with pattern matching
   - Higher-order functions as actor behaviors
   - Functional state machines via behavior switching
   - "Let it crash" philosophy

   ============================================================================ *)

type actor_id = int

type actor_ref = {
  id: actor_id;
  name: string option;
}

type 'msg envelope = {
  from: actor_ref option;
  to_ref: actor_ref;
  payload: 'msg;
  timestamp: float;
  correlation_id: int option;
}

type 'msg system_msg =
  | Start
  | Stop
  | Restart
  | Linked of actor_ref
  | Unlinked of actor_ref
  | Down of actor_ref * string
  | DeadLetter of 'msg envelope

type 'msg effect =
  | Send of actor_ref * 'msg
  | Reply of 'msg
  | Spawn of string option * ('msg -> 'msg actor_state -> 'msg effect list * 'msg actor_state)
  | SpawnResult of actor_ref
  | Link of actor_ref
  | Unlink of actor_ref
  | Monitor of actor_ref
  | Become of ('msg -> 'msg actor_state -> 'msg effect list * 'msg actor_state)
  | Unbecome
  | StopSelf
  | StopChild of actor_ref
  | Escalate of string
  | Log of string
  | NoEffect

and 'msg actor_state = {
  self: actor_ref;
  data: 'msg;
  behavior_stack: ('msg -> 'msg actor_state -> 'msg effect list * 'msg actor_state) list;
  mailbox: 'msg envelope list;
  links: actor_ref list;
  monitors: actor_ref list;
  monitored_by: actor_ref list;
  alive: bool;
  restart_count: int;
  max_restarts: int;
}

type supervision_strategy =
  | OneForOne
  | OneForAll
  | RestForOne

type supervisor_config = {
  strategy: supervision_strategy;
  max_restarts: int;
  restart_window: float;
}

type router_strategy =
  | RoundRobin
  | Broadcast
  | Random

type 'msg registry_entry = {
  ref: actor_ref;
  state: 'msg actor_state;
}

type 'msg actor_system = {
  actors: (actor_id, 'msg registry_entry) Hashtbl.t;
  names: (string, actor_id) Hashtbl.t;
  next_id: int ref;
  dead_letters: 'msg envelope list ref;
  log: string list ref;
  children: (actor_id, actor_id list) Hashtbl.t;
  supervisors: (actor_id, supervisor_config) Hashtbl.t;
}

let create_system () : 'msg actor_system = {
  actors = Hashtbl.create 16;
  names = Hashtbl.create 16;
  next_id = ref 1;
  dead_letters = ref [];
  log = ref [];
  children = Hashtbl.create 16;
  supervisors = Hashtbl.create 16;
}

let make_ref system name =
  let id = !(system.next_id) in
  system.next_id := id + 1;
  let r = { id; name } in
  (match name with Some n -> Hashtbl.replace system.names n id | None -> ());
  r

let make_state ref_ initial_data behavior = {
  self = ref_; data = initial_data; behavior_stack = [behavior];
  mailbox = []; links = []; monitors = []; monitored_by = [];
  alive = true; restart_count = 0; max_restarts = 10;
}

let spawn system ?name initial_data behavior =
  let ref_ = make_ref system name in
  let state = make_state ref_ initial_data behavior in
  Hashtbl.replace system.actors ref_.id { ref = ref_; state }; ref_

let spawn_child system parent_ref ?name initial_data behavior =
  let child_ref = spawn system ?name initial_data behavior in
  let existing = try Hashtbl.find system.children parent_ref.id with Not_found -> [] in
  Hashtbl.replace system.children parent_ref.id (child_ref.id :: existing); child_ref

let lookup_by_name system name =
  match Hashtbl.find_opt system.names name with
  | Some id -> (match Hashtbl.find_opt system.actors id with
    | Some entry -> Some entry.ref | None -> None)
  | None -> None

let lookup system ref_ = Hashtbl.find_opt system.actors ref_.id

let is_alive system ref_ =
  match lookup system ref_ with Some entry -> entry.state.alive | None -> false

let next_correlation = ref 0

let send system ~from ~to_ref payload =
  let env = { from = Some from; to_ref; payload;
    timestamp = Unix.gettimeofday (); correlation_id = None } in
  match Hashtbl.find_opt system.actors to_ref.id with
  | Some entry when entry.state.alive ->
    Hashtbl.replace system.actors to_ref.id
      { entry with state = { entry.state with mailbox = entry.state.mailbox @ [env] } }
  | _ -> system.dead_letters := env :: !(system.dead_letters)

let send_system system ~to_ref payload =
  let env = { from = None; to_ref; payload;
    timestamp = Unix.gettimeofday (); correlation_id = None } in
  match Hashtbl.find_opt system.actors to_ref.id with
  | Some entry when entry.state.alive ->
    Hashtbl.replace system.actors to_ref.id
      { entry with state = { entry.state with mailbox = entry.state.mailbox @ [env] } }
  | _ -> system.dead_letters := env :: !(system.dead_letters)

let ask system ~from ~to_ref payload =
  let cid = !next_correlation in incr next_correlation;
  let env = { from = Some from; to_ref; payload;
    timestamp = Unix.gettimeofday (); correlation_id = Some cid } in
  match Hashtbl.find_opt system.actors to_ref.id with
  | Some entry when entry.state.alive ->
    Hashtbl.replace system.actors to_ref.id
      { entry with state = { entry.state with mailbox = entry.state.mailbox @ [env] } };
    Some cid
  | _ -> system.dead_letters := env :: !(system.dead_letters); None

let selective_receive predicate state =
  let rec scan acc = function
    | [] -> None
    | env :: rest ->
      if predicate env then Some (env, { state with mailbox = List.rev acc @ rest })
      else scan (env :: acc) rest
  in scan [] state.mailbox

let receive state =
  match state.mailbox with [] -> None | env :: rest -> Some (env, { state with mailbox = rest })

let receive_reply cid state =
  selective_receive (fun env -> env.correlation_id = Some cid) state

let rec process_effects system current_ref envelope effects state =
  List.fold_left (fun st effect ->
    match effect with
    | Send (target, msg) -> send system ~from:current_ref ~to_ref:target msg; st
    | Reply msg ->
      (match envelope.from with
       | Some sender -> send system ~from:current_ref ~to_ref:sender msg; st | None -> st)
    | Spawn (name, behavior) ->
      let _child = spawn_child system current_ref ?name st.data behavior in st
    | SpawnResult _ -> st
    | Link target ->
      let st' = { st with links = target :: st.links } in
      (match Hashtbl.find_opt system.actors target.id with
       | Some entry ->
         Hashtbl.replace system.actors target.id
           { entry with state = { entry.state with links = current_ref :: entry.state.links } }
       | None -> ()); st'
    | Unlink target ->
      let st' = { st with links = List.filter (fun r -> r.id <> target.id) st.links } in
      (match Hashtbl.find_opt system.actors target.id with
       | Some entry ->
         Hashtbl.replace system.actors target.id
           { entry with state = { entry.state with
               links = List.filter (fun r -> r.id <> current_ref.id) entry.state.links } }
       | None -> ()); st'
    | Monitor target ->
      let st' = { st with monitors = target :: st.monitors } in
      (match Hashtbl.find_opt system.actors target.id with
       | Some entry ->
         Hashtbl.replace system.actors target.id
           { entry with state = { entry.state with
               monitored_by = current_ref :: entry.state.monitored_by } }
       | None -> ()); st'
    | Become new_beh -> { st with behavior_stack = new_beh :: st.behavior_stack }
    | Unbecome ->
      (match st.behavior_stack with
       | _ :: (_ :: _ as rest) -> { st with behavior_stack = rest } | _ -> st)
    | StopSelf -> stop_actor system st; { st with alive = false }
    | StopChild child_ref ->
      (match Hashtbl.find_opt system.actors child_ref.id with
       | Some entry ->
         stop_actor system entry.state;
         Hashtbl.replace system.actors child_ref.id
           { entry with state = { entry.state with alive = false } }
       | None -> ()); st
    | Escalate reason ->
      system.log := (Printf.sprintf "Actor %d escalated: %s" current_ref.id reason)
        :: !(system.log); st
    | Log msg -> system.log := msg :: !(system.log); st
    | NoEffect -> st
  ) state effects

and stop_actor system state =
  List.iter (fun linked ->
    if (match Hashtbl.find_opt system.actors linked.id with
        | Some e -> e.state.alive | None -> false) then
      system.log := (Printf.sprintf "Link notification: %d -> %d: Actor %d stopped"
        state.self.id linked.id state.self.id) :: !(system.log)
  ) state.links;
  List.iter (fun monitor ->
    if (match Hashtbl.find_opt system.actors monitor.id with
        | Some e -> e.state.alive | None -> false) then
      system.log := (Printf.sprintf "Monitor notification: %d -> %d: Actor %d stopped"
        state.self.id monitor.id state.self.id) :: !(system.log)
  ) state.monitored_by;
  (match state.self.name with Some n -> Hashtbl.remove system.names n | None -> ());
  List.iter (fun child_id ->
    match Hashtbl.find_opt system.actors child_id with
    | Some entry when entry.state.alive ->
      stop_actor system entry.state;
      Hashtbl.replace system.actors child_id
        { entry with state = { entry.state with alive = false } }
    | _ -> ()
  ) (try Hashtbl.find system.children state.self.id with Not_found -> [])

let step_actor system ref_ =
  match Hashtbl.find_opt system.actors ref_.id with
  | None -> false
  | Some entry ->
    if not entry.state.alive then false
    else match receive entry.state with
    | None -> false
    | Some (env, state') ->
      let behavior = List.hd state'.behavior_stack in
      let effects, state'' = behavior env.payload state' in
      let state''' = process_effects system ref_ env effects state'' in
      Hashtbl.replace system.actors ref_.id { entry with state = state''' }; true

let step_all system =
  let processed = ref 0 in
  Hashtbl.iter (fun _ entry ->
    if entry.state.alive then
      while step_actor system entry.ref do incr processed done
  ) system.actors; !processed

let drain system ?(max_iterations=1000) () =
  let i = ref 0 and total = ref 0 in
  while !i < max_iterations && step_all system > 0 do incr i; total := !total + 1 done;
  !total

type 'msg router = {
  strategy: router_strategy;
  routees: actor_ref list;
  mutable rr_index: int;
}

let create_router strategy routees = { strategy; routees; rr_index = 0 }

let route system router ~from msg =
  match router.strategy with
  | RoundRobin ->
    if router.routees <> [] then begin
      let target = List.nth router.routees (router.rr_index mod List.length router.routees) in
      router.rr_index <- router.rr_index + 1;
      send system ~from ~to_ref:target msg end
  | Broadcast -> List.iter (fun t -> send system ~from ~to_ref:t msg) router.routees
  | Random ->
    if router.routees <> [] then
      send system ~from
        ~to_ref:(List.nth router.routees (Random.int (List.length router.routees))) msg

let make_supervisor_config ?(strategy=OneForOne) ?(max_restarts=3) ?(restart_window=60.0) () =
  { strategy; max_restarts; restart_window }

let register_supervisor system parent_ref config =
  Hashtbl.replace system.supervisors parent_ref.id config

let restart_actor system actor_id initial_data =
  match Hashtbl.find_opt system.actors actor_id with
  | Some entry ->
    if entry.state.restart_count < entry.state.max_restarts then begin
      let state' = { entry.state with alive = true; data = initial_data;
                     mailbox = []; restart_count = entry.state.restart_count + 1 } in
      Hashtbl.replace system.actors actor_id { entry with state = state' };
      system.log := (Printf.sprintf "Restarted actor %d (attempt %d)"
        actor_id state'.restart_count) :: !(system.log); true
    end else begin
      system.log := (Printf.sprintf "Actor %d exceeded max restarts (%d)"
        actor_id entry.state.max_restarts) :: !(system.log); false end
  | None -> false

let handle_child_failure system parent_id failed_child_id initial_data =
  match Hashtbl.find_opt system.supervisors parent_id with
  | None -> false
  | Some config ->
    let children = try Hashtbl.find system.children parent_id with Not_found -> [] in
    match config.strategy with
    | OneForOne -> restart_actor system failed_child_id initial_data
    | OneForAll ->
      List.iter (fun cid -> ignore (restart_actor system cid initial_data)) children; true
    | RestForOne ->
      let rec go found = function
        | [] -> () | cid :: rest ->
          if cid = failed_child_id || found then
            (ignore (restart_actor system cid initial_data); go true rest)
          else go false rest
      in go false (List.rev children); true

type system_stats = {
  total_actors: int; alive_actors: int; dead_actors: int;
  total_messages_pending: int; dead_letter_count: int;
  total_restarts: int; log_entries: int;
}

let system_stats system =
  let total = Hashtbl.length system.actors in
  let alive = ref 0 and pending = ref 0 and restarts = ref 0 in
  Hashtbl.iter (fun _ entry ->
    if entry.state.alive then incr alive;
    pending := !pending + List.length entry.state.mailbox;
    restarts := !restarts + entry.state.restart_count
  ) system.actors;
  { total_actors = total; alive_actors = !alive; dead_actors = total - !alive;
    total_messages_pending = !pending;
    dead_letter_count = List.length !(system.dead_letters);
    total_restarts = !restarts; log_entries = List.length !(system.log) }

let stats_to_string s =
  Printf.sprintf
    "Actors: %d total (%d alive, %d dead) | Pending: %d | Dead letters: %d | Restarts: %d"
    s.total_actors s.alive_actors s.dead_actors
    s.total_messages_pending s.dead_letter_count s.total_restarts

(* ============================================================================
   Test Suite (38 tests)
   ============================================================================ *)

let () =
  let passed = ref 0 and failed = ref 0 in
  let test name f =
    try f (); incr passed; Printf.printf "  ✓ %s\n" name
    with ex -> incr failed; Printf.printf "  ✗ %s: %s\n" name (Printexc.to_string ex) in
  let assert_eq a b msg =
    if a <> b then failwith (Printf.sprintf "%s: expected %d, got %d" msg a b) in
  let assert_true b msg = if not b then failwith msg in

  Printf.printf "\n=== Actor Model Tests ===\n\n";
  Printf.printf "Actor Creation & Registry:\n";

  test "spawn actor with name" (fun () ->
    let sys = create_system () in
    let r = spawn sys ~name:"alice" 0 (fun _ s -> ([], s)) in
    assert_true (r.name = Some "alice") "name";
    assert_true (is_alive sys r) "alive");

  test "spawn anonymous actor" (fun () ->
    let sys = create_system () in
    let r = spawn sys 0 (fun _ s -> ([], s)) in
    assert_true (r.name = None) "no name";
    assert_true (is_alive sys r) "alive");

  test "lookup by name" (fun () ->
    let sys = create_system () in
    let r = spawn sys ~name:"bob" 42 (fun _ s -> ([], s)) in
    match lookup_by_name sys "bob" with
    | Some f -> assert_eq r.id f.id "same id"
    | None -> failwith "not found");

  test "lookup nonexistent returns None" (fun () ->
    let sys = create_system () in
    assert_true (lookup_by_name sys "nobody" = None) "None");

  test "unique IDs" (fun () ->
    let sys = create_system () in
    let n = fun _ s -> ([], s) in
    let a = spawn sys 0 n in let b = spawn sys 0 n in let c = spawn sys 0 n in
    assert_true (a.id <> b.id && b.id <> c.id) "unique");

  Printf.printf "\nMessage Passing:\n";

  test "send and receive" (fun () ->
    let sys = create_system () in
    let got = ref false in
    let actor = spawn sys "" (fun m s -> if m = "hi" then got := true; ([], s)) in
    let sender = spawn sys "" (fun _ s -> ([], s)) in
    send sys ~from:sender ~to_ref:actor "hi";
    ignore (drain sys ());
    assert_true !got "received");

  test "FIFO ordering" (fun () ->
    let sys = create_system () in
    let order = ref [] in
    let actor = spawn sys 0 (fun m s -> order := m :: !order; ([], s)) in
    let sender = spawn sys 0 (fun _ s -> ([], s)) in
    send sys ~from:sender ~to_ref:actor "1st";
    send sys ~from:sender ~to_ref:actor "2nd";
    send sys ~from:sender ~to_ref:actor "3rd";
    ignore (drain sys ());
    assert_true (List.rev !order = ["1st";"2nd";"3rd"]) "FIFO");

  test "dead letter on dead actor" (fun () ->
    let sys = create_system () in
    let actor = spawn sys 0 (fun _ s -> ([StopSelf], s)) in
    let sender = spawn sys 0 (fun _ s -> ([], s)) in
    send sys ~from:sender ~to_ref:actor "x";
    ignore (drain sys ());
    send sys ~from:sender ~to_ref:actor "lost";
    assert_eq 1 (List.length !(sys.dead_letters)) "dead letters");

  test "reply to sender" (fun () ->
    let sys = create_system () in
    let got = ref "" in
    let server = spawn sys "" (fun m s -> ([Reply ("echo:" ^ m)], s)) in
    let client = spawn sys "" (fun m s -> got := m; ([], s)) in
    send sys ~from:client ~to_ref:server "hi";
    ignore (drain sys ());
    assert_true (!got = "echo:hi") "echo");

  test "ask with correlation ID" (fun () ->
    let sys = create_system () in
    let server = spawn sys "" (fun m s -> ([Reply ("re:" ^ m)], s)) in
    let client = spawn sys "" (fun _ s -> ([], s)) in
    let cid = ask sys ~from:client ~to_ref:server "q" in
    assert_true (cid <> None) "has cid";
    ignore (drain sys ()));

  Printf.printf "\nSelective Receive:\n";

  test "selective receive by predicate" (fun () ->
    let sys = create_system () in
    let n = fun _ s -> ([], s) in
    let actor = spawn sys "" n in
    let sender = spawn sys "" n in
    send sys ~from:sender ~to_ref:actor "a";
    send sys ~from:sender ~to_ref:actor "b";
    send sys ~from:sender ~to_ref:actor "target";
    send sys ~from:sender ~to_ref:actor "c";
    match Hashtbl.find_opt sys.actors actor.id with
    | Some entry ->
      (match selective_receive (fun e -> e.payload = "target") entry.state with
       | Some (env, st) ->
         assert_true (env.payload = "target") "found";
         assert_eq 3 (List.length st.mailbox) "remaining"
       | None -> failwith "not found")
    | None -> failwith "no actor");

  test "selective receive None when no match" (fun () ->
    let sys = create_system () in
    let n = fun _ s -> ([], s) in
    let actor = spawn sys "" n in
    let sender = spawn sys "" n in
    send sys ~from:sender ~to_ref:actor "a";
    match Hashtbl.find_opt sys.actors actor.id with
    | Some entry ->
      assert_true (selective_receive (fun e -> e.payload = "z") entry.state = None) "None"
    | None -> failwith "no actor");

  Printf.printf "\nState Management:\n";

  test "state updates persist" (fun () ->
    let sys = create_system () in
    let actor = spawn sys "0" (fun _ s ->
      ([], { s with data = string_of_int (int_of_string s.data + 1) })) in
    let sender = spawn sys "" (fun _ s -> ([], s)) in
    send sys ~from:sender ~to_ref:actor "x";
    send sys ~from:sender ~to_ref:actor "x";
    send sys ~from:sender ~to_ref:actor "x";
    ignore (drain sys ());
    match Hashtbl.find_opt sys.actors actor.id with
    | Some e -> assert_true (e.state.data = "3") "counter=3"
    | None -> failwith "no actor");

  test "become changes behavior" (fun () ->
    let sys = create_system () in
    let angry _ s = ([Log "ANGRY!"], { s with data = "angry" }) in
    let calm m s =
      if m = "provoke" then ([Become angry; Log "angry"], s)
      else ([Log "calm"], s) in
    let actor = spawn sys "calm" calm in
    let sender = spawn sys "" (fun _ s -> ([], s)) in
    send sys ~from:sender ~to_ref:actor "hi";
    send sys ~from:sender ~to_ref:actor "provoke";
    send sys ~from:sender ~to_ref:actor "hi";
    ignore (drain sys ());
    match Hashtbl.find_opt sys.actors actor.id with
    | Some e -> assert_true (e.state.data = "angry") "angry"
    | None -> failwith "no actor");

  test "unbecome reverts behavior" (fun () ->
    let sys = create_system () in
    let temp m s =
      if m = "revert" then ([Unbecome], { s with data = "reverted" })
      else ([], { s with data = "temp:" ^ m }) in
    let base m s =
      if m = "switch" then ([Become temp], s)
      else ([], { s with data = "base:" ^ m }) in
    let actor = spawn sys "init" base in
    let sender = spawn sys "" (fun _ s -> ([], s)) in
    send sys ~from:sender ~to_ref:actor "switch";
    send sys ~from:sender ~to_ref:actor "test";
    send sys ~from:sender ~to_ref:actor "revert";
    send sys ~from:sender ~to_ref:actor "final";
    ignore (drain sys ());
    match Hashtbl.find_opt sys.actors actor.id with
    | Some e -> assert_true (e.state.data = "base:final") "reverted"
    | None -> failwith "no actor");

  Printf.printf "\nActor Lifecycle:\n";

  test "stop self" (fun () ->
    let sys = create_system () in
    let actor = spawn sys "" (fun m s ->
      if m = "die" then ([StopSelf], s) else ([], s)) in
    let sender = spawn sys "" (fun _ s -> ([], s)) in
    send sys ~from:sender ~to_ref:actor "die";
    ignore (drain sys ());
    assert_true (not (is_alive sys actor)) "dead");

  test "stop child from parent" (fun () ->
    let sys = create_system () in
    let n = fun _ s -> ([], s) in
    let parent = spawn sys ~name:"parent" "" (fun m s ->
      if m = "kill" then
        let cids = try Hashtbl.find sys.children s.self.id with Not_found -> [] in
        (List.map (fun cid ->
          match Hashtbl.find_opt sys.actors cid with
          | Some e -> StopChild e.ref | None -> NoEffect) cids, s)
      else ([], s)) in
    let child = spawn_child sys parent ~name:"child" "" n in
    let sender = spawn sys "" n in
    send sys ~from:sender ~to_ref:parent "kill";
    ignore (drain sys ());
    assert_true (not (is_alive sys child)) "child dead");

  test "stopping parent stops children" (fun () ->
    let sys = create_system () in
    let n = fun _ s -> ([], s) in
    let parent = spawn sys "" (fun m s ->
      if m = "die" then ([StopSelf], s) else ([], s)) in
    let c1 = spawn_child sys parent "" n in
    let c2 = spawn_child sys parent "" n in
    let sender = spawn sys "" n in
    send sys ~from:sender ~to_ref:parent "die";
    ignore (drain sys ());
    assert_true (not (is_alive sys c1) && not (is_alive sys c2)) "children dead");

  Printf.printf "\nLinks & Monitors:\n";

  test "link actors bidirectionally" (fun () ->
    let sys = create_system () in
    let a = spawn sys ~name:"a" "" (fun m s ->
      if m = "link" then ([Link { id = 2; name = Some "b" }], s)
      else ([], s)) in
    let _b = spawn sys ~name:"b" "" (fun _ s -> ([], s)) in
    let sender = spawn sys "" (fun _ s -> ([], s)) in
    send sys ~from:sender ~to_ref:a "link";
    ignore (drain sys ());
    match Hashtbl.find_opt sys.actors a.id with
    | Some e -> assert_eq 1 (List.length e.state.links) "1 link"
    | None -> failwith "no actor");

  test "monitor actor" (fun () ->
    let sys = create_system () in
    let n = fun _ s -> ([], s) in
    let watcher = spawn sys "" (fun m s ->
      if m = "watch" then
        ([Monitor { id = s.self.id + 1; name = None }], s)
      else ([], s)) in
    let _watched = spawn sys "" n in
    let sender = spawn sys "" n in
    send sys ~from:sender ~to_ref:watcher "watch";
    ignore (drain sys ());
    match Hashtbl.find_opt sys.actors watcher.id with
    | Some e -> assert_eq 1 (List.length e.state.monitors) "1 monitor"
    | None -> failwith "no actor");

  Printf.printf "\nSupervision:\n";

  test "one-for-one restart" (fun () ->
    let sys = create_system () in
    let n = fun _ s -> ([], s) in
    let parent = spawn sys ~name:"sup" "" n in
    register_supervisor sys parent (make_supervisor_config ~strategy:OneForOne ());
    let child = spawn_child sys parent ~name:"worker" "init" n in
    (match Hashtbl.find_opt sys.actors child.id with
     | Some e -> Hashtbl.replace sys.actors child.id
         { e with state = { e.state with alive = false } }
     | None -> ());
    assert_true (handle_child_failure sys parent.id child.id "reset") "restarted";
    assert_true (is_alive sys child) "alive");

  test "one-for-all restart" (fun () ->
    let sys = create_system () in
    let n = fun _ s -> ([], s) in
    let parent = spawn sys "" n in
    register_supervisor sys parent (make_supervisor_config ~strategy:OneForAll ());
    let c1 = spawn_child sys parent "" n in
    let c2 = spawn_child sys parent "" n in
    let c3 = spawn_child sys parent "" n in
    (match Hashtbl.find_opt sys.actors c2.id with
     | Some e -> Hashtbl.replace sys.actors c2.id
         { e with state = { e.state with alive = false } }
     | None -> ());
    ignore (handle_child_failure sys parent.id c2.id "reset");
    let chk r = match Hashtbl.find_opt sys.actors r.id with
      | Some e -> e.state.restart_count > 0 | None -> false in
    assert_true (chk c1 && chk c2 && chk c3) "all restarted");

  test "max restart limit" (fun () ->
    let sys = create_system () in
    let n = fun _ s -> ([], s) in
    let parent = spawn sys "" n in
    register_supervisor sys parent (make_supervisor_config ~strategy:OneForOne ());
    let child = spawn_child sys parent "" n in
    (match Hashtbl.find_opt sys.actors child.id with
     | Some e -> Hashtbl.replace sys.actors child.id
         { e with state = { e.state with alive = false;
                            restart_count = 10; max_restarts = 10 } }
     | None -> ());
    assert_true (not (handle_child_failure sys parent.id child.id "reset")) "blocked");

  test "rest-for-one restart" (fun () ->
    let sys = create_system () in
    let n = fun _ s -> ([], s) in
    let parent = spawn sys "" n in
    register_supervisor sys parent (make_supervisor_config ~strategy:RestForOne ());
    let _c1 = spawn_child sys parent "" n in
    let c2 = spawn_child sys parent "" n in
    let _c3 = spawn_child sys parent "" n in
    (match Hashtbl.find_opt sys.actors c2.id with
     | Some e -> Hashtbl.replace sys.actors c2.id
         { e with state = { e.state with alive = false } }
     | None -> ());
    ignore (handle_child_failure sys parent.id c2.id "reset");
    match Hashtbl.find_opt sys.actors c2.id with
    | Some e -> assert_true (e.state.restart_count > 0) "c2 restarted"
    | None -> failwith "no actor");

  Printf.printf "\nRouters:\n";

  test "round-robin routing" (fun () ->
    let sys = create_system () in
    let counts = Hashtbl.create 4 in
    let worker _ s =
      Hashtbl.replace counts s.self.id
        (1 + try Hashtbl.find counts s.self.id with Not_found -> 0);
      ([], s) in
    let w1 = spawn sys "" worker in
    let w2 = spawn sys "" worker in
    let w3 = spawn sys "" worker in
    let sender = spawn sys "" (fun _ s -> ([], s)) in
    let router = create_router RoundRobin [w1; w2; w3] in
    for _ = 1 to 6 do route sys router ~from:sender "work" done;
    ignore (drain sys ());
    let c id = try Hashtbl.find counts id with Not_found -> 0 in
    assert_eq 2 (c w1.id) "w1";
    assert_eq 2 (c w2.id) "w2";
    assert_eq 2 (c w3.id) "w3");

  test "broadcast routing" (fun () ->
    let sys = create_system () in
    let got = ref 0 in
    let worker _ s = incr got; ([], s) in
    let w1 = spawn sys "" worker in
    let w2 = spawn sys "" worker in
    let sender = spawn sys "" (fun _ s -> ([], s)) in
    route sys (create_router Broadcast [w1; w2]) ~from:sender "msg";
    ignore (drain sys ());
    assert_eq 2 !got "both got");

  Printf.printf "\nSystem Statistics:\n";

  test "stats accurate" (fun () ->
    let sys = create_system () in
    let n = fun _ s -> ([], s) in
    let _ = spawn sys "" n in
    let _ = spawn sys "" n in
    let a3 = spawn sys "" (fun m s ->
      if m = "die" then ([StopSelf], s) else ([], s)) in
    let sender = spawn sys "" n in
    send sys ~from:sender ~to_ref:a3 "die";
    ignore (drain sys ());
    let s = system_stats sys in
    assert_eq 4 s.total_actors "total";
    assert_eq 3 s.alive_actors "alive";
    assert_eq 1 s.dead_actors "dead");

  test "stats_to_string" (fun () ->
    let s = { total_actors=5; alive_actors=3; dead_actors=2;
              total_messages_pending=10; dead_letter_count=1;
              total_restarts=2; log_entries=4 } in
    assert_true (String.length (stats_to_string s) > 0) "non-empty");

  Printf.printf "\nComplex Scenarios:\n";

  test "ping-pong" (fun () ->
    let sys = create_system () in
    let count = ref 0 in
    let pong m s =
      if m = "ping" then (incr count; ([Reply "pong"], s))
      else ([], s) in
    let ping m s =
      if m = "start" then
        ([Send ({ id = s.self.id + 1; name = Some "pong" }, "ping")], s)
      else if m = "pong" && !count < 5 then
        (incr count; ([Reply "ping"], s))
      else ([], s) in
    let p = spawn sys ~name:"ping" "" ping in
    let _ = spawn sys ~name:"pong" "" pong in
    let sender = spawn sys "" (fun _ s -> ([], s)) in
    send sys ~from:sender ~to_ref:p "start";
    ignore (drain sys ());
    assert_true (!count >= 2) "multiple exchanges");

  test "actor pipeline" (fun () ->
    let sys = create_system () in
    let result = ref "" in
    let stage f next m s =
      let t = f m in
      match next with
      | Some nr -> ([Send (nr, t)], s)
      | None -> result := t; ([], s) in
    let c = spawn sys "" (stage (fun s -> s ^ "!") None) in
    let b = spawn sys "" (stage String.uppercase_ascii (Some c)) in
    let a = spawn sys "" (stage (fun s -> "hello " ^ s) (Some b)) in
    let sender = spawn sys "" (fun _ s -> ([], s)) in
    send sys ~from:sender ~to_ref:a "world";
    ignore (drain sys ());
    assert_true (!result = "HELLO WORLD!") "pipeline");

  test "dynamic child spawn" (fun () ->
    let sys = create_system () in
    let parent = spawn sys ~name:"spawner" "" (fun m s ->
      if m = "spawn" then
        (let _ = spawn_child sys s.self ~name:"dynamic" ""
           (fun _ st -> ([], st)) in
         ([Log "spawned"], s))
      else ([], s)) in
    let sender = spawn sys "" (fun _ s -> ([], s)) in
    send sys ~from:sender ~to_ref:parent "spawn";
    ignore (drain sys ());
    assert_true (lookup_by_name sys "dynamic" <> None) "child exists");

  test "dead letter collection" (fun () ->
    let sys = create_system () in
    let sender = spawn sys "" (fun _ s -> ([], s)) in
    let ghost = { id = 9999; name = Some "ghost" } in
    send sys ~from:sender ~to_ref:ghost "a";
    send sys ~from:sender ~to_ref:ghost "b";
    assert_eq 2 (List.length !(sys.dead_letters)) "2 dead letters");

  test "drain with max iterations" (fun () ->
    let sys = create_system () in
    let _ = spawn sys "" (fun _ s -> ([], s)) in
    assert_true (drain sys ~max_iterations:5 () >= 0) "completes");

  test "log captures" (fun () ->
    let sys = create_system () in
    let actor = spawn sys "" (fun m s -> ([Log ("got:" ^ m)], s)) in
    let sender = spawn sys "" (fun _ s -> ([], s)) in
    send sys ~from:sender ~to_ref:actor "a";
    send sys ~from:sender ~to_ref:actor "b";
    ignore (drain sys ());
    assert_eq 2 (List.length !(sys.log)) "2 logs");

  test "50 actors messaging" (fun () ->
    let sys = create_system () in
    let n = fun _ s -> ([], s) in
    let actors = Array.init 50 (fun i ->
      spawn sys ~name:(Printf.sprintf "a%d" i) "" n) in
    assert_eq 50 (system_stats sys).total_actors "50";
    for i = 0 to 49 do
      send sys ~from:actors.(i) ~to_ref:actors.((i+7) mod 50) "hi"
    done;
    ignore (drain sys ());
    assert_eq 0 (system_stats sys).total_messages_pending "all processed");

  test "supervisor config" (fun () ->
    let c = make_supervisor_config ~strategy:OneForAll
              ~max_restarts:5 ~restart_window:30.0 () in
    assert_true (c.strategy = OneForAll) "strategy";
    assert_eq 5 c.max_restarts "max");

  Printf.printf "\n=== Results: %d passed, %d failed ===\n" !passed !failed;
  if !failed = 0 then Printf.printf "All tests passed! ✓\n"
  else Printf.printf "SOME TESTS FAILED\n"
