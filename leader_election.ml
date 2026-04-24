(* leader_election.ml — Distributed Leader Election Simulator
 *
 * Implements three classic leader election algorithms across a
 * simulated cluster of nodes with crash/recovery, message loss,
 * network partitions, and autonomous failure detection.
 *
 * Algorithms:
 *   - Bully Algorithm (Garcia-Molina, 1982)
 *   - Ring Algorithm (LeLann, 1977)
 *   - Chang-Roberts Optimized Ring (1979)
 *
 * Usage:
 *   ocamlfind ocamlopt -package unix -linkpkg leader_election.ml -o leader_election && ./leader_election
 *   ocamlfind ocamlc  -package unix -linkpkg leader_election.ml -o leader_election && ./leader_election
 *
 * Features:
 *   - Configurable cluster size and message loss probability
 *   - Step-by-step message passing with round-by-round visualization
 *   - Crash and recover nodes at will
 *   - Network partition and healing
 *   - Autonomous leader failure detection with auto-election
 *   - Election history and message statistics
 *   - ASCII cluster topology display
 *   - Interactive REPL
 *)

let () = Random.self_init ()
let rand_float () = Random.float 1.0

(* ---- Types ---- *)

type node_id = int

type algo = Bully | Ring | ChangRoberts

type msg_kind =
  | Election of node_id       (* candidate id *)
  | Answer of node_id         (* responder id *)
  | Coordinator of node_id    (* new leader id *)
  | RingElect of node_id list (* collected ids so far *)

type message = {
  src   : node_id;
  dst   : node_id;
  kind  : msg_kind;
  round : int;  (* round sent *)
}

type node_state = Alive | Crashed

type node = {
  id            : node_id;
  mutable state : node_state;
  mutable is_leader : bool;
  mutable knows_leader : node_id option;
  mutable got_answer : bool;  (* bully: received answer? *)
  mutable msgs_sent : int;
  mutable msgs_recv : int;
}

type election_record = {
  algo_used   : algo;
  initiator   : node_id;
  winner      : node_id option;
  rounds      : int;
  messages    : int;
  start_round : int;
}

type cluster = {
  mutable nodes       : node array;
  mutable msg_queue   : message list;   (* pending for next round *)
  mutable delivering  : message list;   (* being delivered this round *)
  mutable round       : int;
  mutable loss_prob   : float;
  mutable partitions  : node_id list list;  (* empty = no partition *)
  mutable leader      : node_id option;
  mutable auto_mode   : bool;
  mutable election_active : bool;
  mutable current_algo : algo option;
  mutable election_initiator : node_id option;
  mutable election_start : int;
  mutable election_msgs : int;
  mutable history     : election_record list;
  mutable log         : string list;
}

let algo_to_string = function
  | Bully -> "Bully" | Ring -> "Ring" | ChangRoberts -> "Chang-Roberts"

let msg_kind_to_string = function
  | Election id -> Printf.sprintf "ELECTION(%d)" id
  | Answer id -> Printf.sprintf "ANSWER(%d)" id
  | Coordinator id -> Printf.sprintf "COORDINATOR(%d)" id
  | RingElect ids -> Printf.sprintf "RING_ELECT[%s]" (String.concat "," (List.map string_of_int ids))

(* ---- Cluster creation ---- *)

let make_node id = {
  id; state = Alive; is_leader = false; knows_leader = None;
  got_answer = false; msgs_sent = 0; msgs_recv = 0;
}

let make_cluster n = {
  nodes = Array.init n (fun i -> make_node (i + 1));
  msg_queue = []; delivering = [];
  round = 0; loss_prob = 0.0;
  partitions = [];
  leader = None; auto_mode = false;
  election_active = false; current_algo = None;
  election_initiator = None; election_start = 0; election_msgs = 0;
  history = []; log = [];
}

let cluster = ref (make_cluster 5)

let log_msg s =
  let c = !cluster in
  c.log <- s :: c.log;
  Printf.printf "  %s\n" s

let get_node c id =
  if id >= 1 && id <= Array.length c.nodes then Some c.nodes.(id - 1) else None

let alive_nodes c = Array.to_list c.nodes |> List.filter (fun n -> n.state = Alive)

let can_reach c src dst =
  if c.partitions = [] then true
  else
    List.exists (fun part -> List.mem src part && List.mem dst part) c.partitions

let send_msg c src dst kind =
  let msg = { src; dst; kind; round = c.round } in
  c.msg_queue <- msg :: c.msg_queue;
  (match get_node c src with Some n -> n.msgs_sent <- n.msgs_sent + 1 | None -> ());
  c.election_msgs <- c.election_msgs + 1;
  log_msg (Printf.sprintf "[Round %d] Node %d -> Node %d: %s"
    c.round src dst (msg_kind_to_string kind))

(* ---- Ring topology helpers ---- *)

let ring_successor c id =
  let n = Array.length c.nodes in
  let rec find offset =
    if offset > n then None
    else
      let next_id = ((id - 1 + offset) mod n) + 1 in
      match get_node c next_id with
      | Some nd when nd.state = Alive && can_reach c id next_id -> Some next_id
      | _ -> find (offset + 1)
  in
  find 1

(* ---- Bully Algorithm ---- *)

let start_bully c initiator_id =
  c.election_active <- true;
  c.current_algo <- Some Bully;
  c.election_initiator <- Some initiator_id;
  c.election_start <- c.round;
  c.election_msgs <- 0;
  log_msg (Printf.sprintf "[Round %d] === BULLY ELECTION started by Node %d ===" c.round initiator_id);
  (* initiator sends ELECTION to all higher-ID nodes *)
  let init_node = c.nodes.(initiator_id - 1) in
  init_node.got_answer <- false;
  let higher = alive_nodes c |> List.filter (fun n -> n.id > initiator_id && can_reach c initiator_id n.id) in
  if higher = [] then begin
    (* I'm the highest alive — declare self leader *)
    log_msg (Printf.sprintf "[Round %d] Node %d is highest alive, self-electing" c.round initiator_id);
    let all_alive = alive_nodes c in
    List.iter (fun n ->
      if n.id <> initiator_id && can_reach c initiator_id n.id then
        send_msg c initiator_id n.id (Coordinator initiator_id)
    ) all_alive
  end else
    List.iter (fun n -> send_msg c initiator_id n.id (Election initiator_id)) higher

let handle_bully_msg c node msg =
  match msg.kind with
  | Election _from_id ->
    (* respond with ANSWER, then start own election *)
    send_msg c node.id msg.src (Answer node.id);
    (* start own election to higher nodes *)
    let higher = alive_nodes c |> List.filter (fun n -> n.id > node.id && can_reach c node.id n.id) in
    node.got_answer <- false;
    if higher = [] then begin
      let all_alive = alive_nodes c in
      List.iter (fun n ->
        if n.id <> node.id && can_reach c node.id n.id then
          send_msg c node.id n.id (Coordinator node.id)
      ) all_alive
    end else
      List.iter (fun n -> send_msg c node.id n.id (Election node.id)) higher
  | Answer _responder ->
    node.got_answer <- true
  | Coordinator leader_id ->
    node.is_leader <- (node.id = leader_id);
    node.knows_leader <- Some leader_id;
    log_msg (Printf.sprintf "[Round %d] Node %d accepts Node %d as leader" c.round node.id leader_id);
    c.leader <- Some leader_id;
    (match get_node c leader_id with Some l -> l.is_leader <- true; l.knows_leader <- Some leader_id | None -> ())
  | RingElect _ -> ()

(* ---- Ring Algorithm ---- *)

let start_ring c initiator_id =
  c.election_active <- true;
  c.current_algo <- Some Ring;
  c.election_initiator <- Some initiator_id;
  c.election_start <- c.round;
  c.election_msgs <- 0;
  log_msg (Printf.sprintf "[Round %d] === RING ELECTION started by Node %d ===" c.round initiator_id);
  match ring_successor c initiator_id with
  | Some next -> send_msg c initiator_id next (RingElect [initiator_id])
  | None -> log_msg (Printf.sprintf "[Round %d] Node %d: no reachable successor!" c.round initiator_id)

let handle_ring_msg c node msg =
  match msg.kind with
  | RingElect ids ->
    if List.mem node.id ids then begin
      (* message went full circle — pick max as leader *)
      let leader_id = List.fold_left max 0 ids in
      log_msg (Printf.sprintf "[Round %d] Node %d: ring complete, leader = %d" c.round node.id leader_id);
      (* send coordinator to all alive *)
      let all_alive = alive_nodes c in
      List.iter (fun n ->
        if n.id <> node.id && can_reach c node.id n.id then
          send_msg c node.id n.id (Coordinator leader_id)
      ) all_alive;
      node.is_leader <- (node.id = leader_id);
      node.knows_leader <- Some leader_id;
      c.leader <- Some leader_id;
      (match get_node c leader_id with Some l -> l.is_leader <- true; l.knows_leader <- Some leader_id | None -> ())
    end else begin
      let new_ids = node.id :: ids in
      match ring_successor c node.id with
      | Some next -> send_msg c node.id next (RingElect new_ids)
      | None -> log_msg (Printf.sprintf "[Round %d] Node %d: ring broken!" c.round node.id)
    end
  | Coordinator leader_id ->
    node.is_leader <- (node.id = leader_id);
    node.knows_leader <- Some leader_id;
    log_msg (Printf.sprintf "[Round %d] Node %d accepts Node %d as leader" c.round node.id leader_id);
    c.leader <- Some leader_id;
    (match get_node c leader_id with Some l -> l.is_leader <- true; l.knows_leader <- Some leader_id | None -> ())
  | _ -> ()

(* ---- Chang-Roberts Optimized Ring ---- *)

let start_chang_roberts c initiator_id =
  c.election_active <- true;
  c.current_algo <- Some ChangRoberts;
  c.election_initiator <- Some initiator_id;
  c.election_start <- c.round;
  c.election_msgs <- 0;
  log_msg (Printf.sprintf "[Round %d] === CHANG-ROBERTS ELECTION started by Node %d ===" c.round initiator_id);
  match ring_successor c initiator_id with
  | Some next -> send_msg c initiator_id next (Election initiator_id)
  | None -> log_msg (Printf.sprintf "[Round %d] Node %d: no reachable successor!" c.round initiator_id)

let handle_chang_roberts_msg c node msg =
  match msg.kind with
  | Election candidate_id ->
    if candidate_id > node.id then begin
      (* forward — candidate is higher *)
      match ring_successor c node.id with
      | Some next -> send_msg c node.id next (Election candidate_id)
      | None -> ()
    end else if candidate_id < node.id then begin
      (* replace with own id *)
      match ring_successor c node.id with
      | Some next -> send_msg c node.id next (Election node.id)
      | None -> ()
    end else begin
      (* got own id back — I'm the leader *)
      log_msg (Printf.sprintf "[Round %d] Node %d elected as leader (Chang-Roberts)" c.round node.id);
      let all_alive = alive_nodes c in
      List.iter (fun n ->
        if n.id <> node.id && can_reach c node.id n.id then
          send_msg c node.id n.id (Coordinator node.id)
      ) all_alive;
      node.is_leader <- true;
      node.knows_leader <- Some node.id;
      c.leader <- Some node.id
    end
  | Coordinator leader_id ->
    node.is_leader <- (node.id = leader_id);
    node.knows_leader <- Some leader_id;
    log_msg (Printf.sprintf "[Round %d] Node %d accepts Node %d as leader" c.round node.id leader_id);
    c.leader <- Some leader_id;
    (match get_node c leader_id with Some l -> l.is_leader <- true; l.knows_leader <- Some leader_id | None -> ())
  | _ -> ()

(* ---- Step simulation ---- *)

let deliver_round c =
  c.round <- c.round + 1;
  c.delivering <- c.msg_queue;
  c.msg_queue <- [];
  let delivered = ref 0 in
  let dropped = ref 0 in
  List.iter (fun msg ->
    match get_node c msg.dst with
    | None -> incr dropped
    | Some dst_node ->
      if dst_node.state = Crashed then begin
        log_msg (Printf.sprintf "[Round %d] Message to Node %d dropped (crashed)" c.round msg.dst);
        incr dropped
      end else if not (can_reach c msg.src msg.dst) then begin
        log_msg (Printf.sprintf "[Round %d] Message %d->%d dropped (partition)" c.round msg.src msg.dst);
        incr dropped
      end else if c.loss_prob > 0.0 && rand_float () < c.loss_prob then begin
        log_msg (Printf.sprintf "[Round %d] Message %d->%d lost (%.0f%% loss)" c.round msg.src msg.dst (c.loss_prob *. 100.0));
        incr dropped
      end else begin
        dst_node.msgs_recv <- dst_node.msgs_recv + 1;
        incr delivered;
        match c.current_algo with
        | Some Bully -> handle_bully_msg c dst_node msg
        | Some Ring -> handle_ring_msg c dst_node msg
        | Some ChangRoberts -> handle_chang_roberts_msg c dst_node msg
        | None -> ()
      end
  ) c.delivering;
  c.delivering <- [];
  (* check if election resolved *)
  if c.election_active && c.msg_queue = [] then begin
    let rec_entry = {
      algo_used = (match c.current_algo with Some a -> a | None -> Bully);
      initiator = (match c.election_initiator with Some i -> i | None -> 0);
      winner = c.leader;
      rounds = c.round - c.election_start;
      messages = c.election_msgs;
      start_round = c.election_start;
    } in
    c.history <- rec_entry :: c.history;
    c.election_active <- false;
    log_msg (Printf.sprintf "[Round %d] === Election complete: leader=%s, %d msgs, %d rounds ==="
      c.round
      (match c.leader with Some l -> string_of_int l | None -> "none")
      rec_entry.messages rec_entry.rounds)
  end;
  (* auto mode: check leader health *)
  if c.auto_mode && not c.election_active then begin
    match c.leader with
    | Some lid ->
      (match get_node c lid with
       | Some n when n.state = Crashed ->
         log_msg (Printf.sprintf "[Round %d] AUTO: Leader %d is down! Triggering election..." c.round lid);
         c.leader <- None;
         Array.iter (fun n -> n.is_leader <- false; n.knows_leader <- None) c.nodes;
         let alive = alive_nodes c in
         (match alive with
          | first :: _ ->
            let algo = match c.current_algo with Some a -> a | None -> Bully in
            (match algo with
             | Bully -> start_bully c first.id
             | Ring -> start_ring c first.id
             | ChangRoberts -> start_chang_roberts c first.id)
          | [] -> log_msg (Printf.sprintf "[Round %d] AUTO: No alive nodes!" c.round))
       | _ -> ())
    | None -> ()
  end;
  Printf.printf "  --- Round %d: %d delivered, %d dropped, queue=%d ---\n"
    c.round !delivered !dropped (List.length c.msg_queue)

(* ---- Display ---- *)

let show_status c =
  Printf.printf "\n  === Cluster Status (Round %d) ===\n" c.round;
  Printf.printf "  Leader: %s | Auto: %s | Loss: %.0f%% | Election: %s\n"
    (match c.leader with Some l -> string_of_int l | None -> "none")
    (if c.auto_mode then "ON" else "OFF")
    (c.loss_prob *. 100.0)
    (if c.election_active then
       match c.current_algo with Some a -> algo_to_string a | None -> "yes"
     else "idle");
  if c.partitions <> [] then
    Printf.printf "  Partitions: %s\n"
      (String.concat " | " (List.map (fun p ->
        "[" ^ String.concat "," (List.map string_of_int p) ^ "]") c.partitions));
  Printf.printf "  ┌──────┬─────────┬────────┬──────────┬──────┬──────┐\n";
  Printf.printf "  │ Node │  State  │ Leader │ Knows Ldr│ Sent │ Recv │\n";
  Printf.printf "  ├──────┼─────────┼────────┼──────────┼──────┼──────┤\n";
  Array.iter (fun n ->
    Printf.printf "  │ %4d │ %7s │ %6s │ %8s │ %4d │ %4d │\n"
      n.id
      (match n.state with Alive -> "Alive" | Crashed -> "CRASHED")
      (if n.is_leader then "  *" else " ")
      (match n.knows_leader with Some l -> string_of_int l | None -> "-")
      n.msgs_sent n.msgs_recv
  ) c.nodes;
  Printf.printf "  └──────┴─────────┴────────┴──────────┴──────┴──────┘\n";
  (* ASCII ring *)
  let n = Array.length c.nodes in
  if n <= 10 then begin
    Printf.printf "\n  Ring topology:\n  ";
    Array.iteri (fun i nd ->
      let sym = match nd.state with
        | Crashed -> "X"
        | Alive -> if nd.is_leader then "★" else "○"
      in
      Printf.printf "%s%d" sym nd.id;
      if i < n - 1 then Printf.printf " → "
    ) c.nodes;
    Printf.printf " ↩\n"
  end;
  Printf.printf "\n"

let show_stats c =
  Printf.printf "\n  === Election History ===\n";
  if c.history = [] then
    Printf.printf "  No elections yet.\n"
  else begin
    Printf.printf "  ┌─────┬──────────────┬─────────┬────────┬────────┬──────┐\n";
    Printf.printf "  │  #  │  Algorithm   │ Starter │ Winner │ Rounds │ Msgs │\n";
    Printf.printf "  ├─────┼──────────────┼─────────┼────────┼────────┼──────┤\n";
    List.iteri (fun i r ->
      Printf.printf "  │ %3d │ %12s │   %3d   │  %4s  │  %4d  │ %4d │\n"
        (List.length c.history - i)
        (algo_to_string r.algo_used)
        r.initiator
        (match r.winner with Some w -> string_of_int w | None -> "none")
        r.rounds r.messages
    ) c.history;
    Printf.printf "  └─────┴──────────────┴─────────┴────────┴────────┴──────┘\n"
  end;
  Printf.printf "\n  Node totals:\n";
  Array.iter (fun n ->
    Printf.printf "    Node %d: sent=%d recv=%d\n" n.id n.msgs_sent n.msgs_recv
  ) c.nodes;
  Printf.printf "\n"

(* ---- REPL ---- *)

let show_help () =
  Printf.printf "\n  === Leader Election Simulator ===\n";
  Printf.printf "  Commands:\n";
  Printf.printf "    status              Show cluster state & topology\n";
  Printf.printf "    crash <id>          Crash a node\n";
  Printf.printf "    recover <id>        Recover a crashed node\n";
  Printf.printf "    elect <algo>        Start election (bully|ring|chang-roberts)\n";
  Printf.printf "    auto                Toggle autonomous failure detection\n";
  Printf.printf "    partition <a,b|c,d> Split network (e.g., 1,2|3,4,5)\n";
  Printf.printf "    heal                Heal all partitions\n";
  Printf.printf "    step [n]            Advance n rounds (default 1)\n";
  Printf.printf "    run                 Run until election completes\n";
  Printf.printf "    stats               Election history & message counts\n";
  Printf.printf "    reset [n]           Reset cluster with n nodes (default 5)\n";
  Printf.printf "    config loss <f>     Set message loss probability (0.0-1.0)\n";
  Printf.printf "    quit                Exit\n\n"

let parse_algo s =
  match String.lowercase_ascii (String.trim s) with
  | "bully" -> Some Bully
  | "ring" -> Some Ring
  | "chang-roberts" | "changroberts" | "cr" -> Some ChangRoberts
  | _ -> None

let parse_int s = try Some (int_of_string (String.trim s)) with _ -> None
let parse_float s = try Some (float_of_string (String.trim s)) with _ -> None

let split_on_char ch s =
  let rec aux acc start =
    match String.index_from_opt s start ch with
    | None -> List.rev (String.sub s start (String.length s - start) :: acc)
    | Some i -> aux (String.sub s start (i - start) :: acc) (i + 1)
  in
  if String.length s = 0 then [""] else aux [] 0

let trim_split ch s =
  split_on_char ch s |> List.map String.trim |> List.filter (fun x -> x <> "")

let reset_cluster n =
  cluster := make_cluster n;
  Printf.printf "  Cluster reset with %d nodes.\n" n

let do_crash c id =
  match get_node c id with
  | None -> Printf.printf "  Invalid node %d\n" id
  | Some n ->
    n.state <- Crashed; n.is_leader <- false;
    if c.leader = Some id then c.leader <- None;
    Printf.printf "  Node %d crashed.\n" id

let do_recover c id =
  match get_node c id with
  | None -> Printf.printf "  Invalid node %d\n" id
  | Some n ->
    n.state <- Alive; n.knows_leader <- None;
    Printf.printf "  Node %d recovered.\n" id

let do_elect c algo_str =
  match parse_algo algo_str with
  | None -> Printf.printf "  Unknown algorithm. Use: bully, ring, chang-roberts\n"
  | Some algo ->
    if c.election_active then
      Printf.printf "  Election already in progress.\n"
    else begin
      Array.iter (fun n -> n.is_leader <- false; n.knows_leader <- None; n.got_answer <- false) c.nodes;
      c.leader <- None;
      let alive = alive_nodes c in
      match alive with
      | [] -> Printf.printf "  No alive nodes!\n"
      | first :: _ ->
        match algo with
        | Bully -> start_bully c first.id
        | Ring -> start_ring c first.id
        | ChangRoberts -> start_chang_roberts c first.id
    end

let do_partition c spec =
  let groups = split_on_char '|' spec in
  let parts = List.map (fun g ->
    trim_split ',' g |> List.filter_map parse_int
  ) groups in
  let parts = List.filter (fun p -> p <> []) parts in
  if parts = [] then Printf.printf "  Invalid partition spec. Example: 1,2|3,4,5\n"
  else begin
    c.partitions <- parts;
    Printf.printf "  Network partitioned: %s\n"
      (String.concat " | " (List.map (fun p ->
        "[" ^ String.concat "," (List.map string_of_int p) ^ "]") parts))
  end

let do_step c n =
  for _ = 1 to n do
    deliver_round c
  done

let do_run c =
  if not c.election_active then
    Printf.printf "  No active election. Use 'elect <algo>' first.\n"
  else begin
    let max_rounds = 100 in
    let i = ref 0 in
    while c.election_active && !i < max_rounds do
      deliver_round c;
      incr i
    done;
    if c.election_active then
      Printf.printf "  Election did not complete in %d rounds.\n" max_rounds
  end

let repl () =
  show_help ();
  show_status !cluster;
  let running = ref true in
  while !running do
    Printf.printf "leader> %!";
    let line = try Some (input_line stdin) with End_of_file -> None in
    match line with
    | None -> running := false
    | Some raw ->
      let line_t = String.trim raw in
      if line_t = "" then ()
      else
        let parts = trim_split ' ' line_t in
        let c = !cluster in
        match parts with
        | ["help"] -> show_help ()
        | ["status"] -> show_status c
        | ["stats"] -> show_stats c
        | ["quit"] | ["exit"] | ["q"] -> running := false
        | ["auto"] ->
          c.auto_mode <- not c.auto_mode;
          Printf.printf "  Auto mode: %s\n" (if c.auto_mode then "ON" else "OFF")
        | ["heal"] ->
          c.partitions <- [];
          Printf.printf "  Partitions healed.\n"
        | ["reset"] -> reset_cluster 5
        | ["reset"; n_s] ->
          (match parse_int n_s with
           | Some n when n > 0 -> reset_cluster n
           | _ -> Printf.printf "  Usage: reset [n]\n")
        | ["crash"; id_s] ->
          (match parse_int id_s with
           | Some id -> do_crash c id
           | None -> Printf.printf "  Usage: crash <id>\n")
        | ["recover"; id_s] ->
          (match parse_int id_s with
           | Some id -> do_recover c id
           | None -> Printf.printf "  Usage: recover <id>\n")
        | "elect" :: rest ->
          do_elect c (String.concat " " rest)
        | "partition" :: rest ->
          do_partition c (String.concat " " rest)
        | ["step"] -> do_step c 1
        | ["step"; n_s] ->
          (match parse_int n_s with
           | Some n when n > 0 -> do_step c n
           | _ -> Printf.printf "  Usage: step [n]\n")
        | ["run"] -> do_run c
        | ["config"; "loss"; f_s] ->
          (match parse_float f_s with
           | Some f when f >= 0.0 && f <= 1.0 -> c.loss_prob <- f;
             Printf.printf "  Loss probability: %.0f%%\n" (f *. 100.0)
           | _ -> Printf.printf "  Usage: config loss <0.0-1.0>\n")
        | ["config"; "nodes"; n_s] ->
          (match parse_int n_s with
           | Some n when n > 0 -> reset_cluster n
           | _ -> Printf.printf "  Usage: config nodes <n>\n")
        | _ -> Printf.printf "  Unknown command. Type 'help' for commands.\n"
  done;
  Printf.printf "  Goodbye!\n"

let () = repl ()
