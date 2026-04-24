(* gossip.ml — Gossip Protocol Simulator
 *
 * Epidemic-style information dissemination across a network of nodes.
 * Implements push, pull, and push-pull gossip strategies with
 * convergence tracking, network partition simulation, and
 * autonomous protocol selection.
 *
 * Usage:
 *   ocamlfind ocamlopt -package unix -linkpkg gossip.ml -o gossip && ./gossip
 *   ocamlfind ocamlc  -package unix -linkpkg gossip.ml -o gossip && ./gossip
 *
 * Features:
 *   - Push, Pull, and Push-Pull gossip strategies
 *   - Configurable fanout and infection probability
 *   - Convergence tracking with round-by-round stats
 *   - Network partition and healing simulation
 *   - Rumor aging and expiration
 *   - Anti-entropy protocol for consistency repair
 *   - Autonomous protocol advisor based on network conditions
 *   - Multiple network topologies (full mesh, ring, random)
 *   - Interactive REPL
 *)

(* ---- Random ---- *)

let () = Random.self_init ()
let rand_int n = if n <= 0 then 0 else Random.int n
let rand_float () = Random.float 1.0
let shuffle arr =
  let n = Array.length arr in
  for i = n - 1 downto 1 do
    let j = rand_int (i + 1) in
    let tmp = arr.(i) in
    arr.(i) <- arr.(j);
    arr.(j) <- tmp
  done

(* ---- Types ---- *)

type node_id = int

type gossip_strategy = Push | Pull | PushPull

type rumor = {
  rumor_id    : int;
  origin      : node_id;
  payload     : string;
  created_at  : int;   (* round created *)
  ttl         : int;   (* rounds to live, 0 = infinite *)
}

type node = {
  id            : node_id;
  mutable rumors : (int, rumor * int) Hashtbl.t;  (* rumor_id -> (rumor, round_received) *)
  mutable neighbors : node_id list;
  mutable active : bool;
  mutable msgs_sent : int;
  mutable msgs_recv : int;
}

type partition = {
  part_id : int;
  members : node_id list;
  created_round : int;
}

type topology = FullMesh | Ring | RandomGraph of float (* edge probability *)

type network = {
  nodes           : (node_id, node) Hashtbl.t;
  mutable round   : int;
  mutable strategy : gossip_strategy;
  mutable fanout  : int;
  mutable infection_prob : float;
  mutable partitions : partition list;
  mutable next_rumor_id : int;
  mutable topology : topology;
  mutable history : round_stats list;
}

and round_stats = {
  rs_round       : int;
  rs_total_nodes : int;
  rs_informed    : int;     (* nodes knowing at least one rumor *)
  rs_msgs_sent   : int;
  rs_msgs_recv   : int;
  rs_unique_rumors : int;
  rs_coverage    : float;   (* fraction of (nodes * rumors) pairs known *)
}

(* ---- Helpers ---- *)

let strategy_to_string = function
  | Push -> "push" | Pull -> "pull" | PushPull -> "push-pull"

let topology_to_string = function
  | FullMesh -> "full-mesh" | Ring -> "ring"
  | RandomGraph p -> Printf.sprintf "random(%.2f)" p

let pick_random lst =
  match lst with
  | [] -> None
  | _ -> Some (List.nth lst (rand_int (List.length lst)))

let pick_n_random n lst =
  let arr = Array.of_list lst in
  shuffle arr;
  let take = min n (Array.length arr) in
  Array.to_list (Array.sub arr 0 take)

(* ---- Network Construction ---- *)

let create_node id =
  { id; rumors = Hashtbl.create 16; neighbors = [];
    active = true; msgs_sent = 0; msgs_recv = 0 }

let create_network ?(strategy=PushPull) ?(fanout=3) ?(prob=1.0)
    ?(topology=FullMesh) n =
  let nodes = Hashtbl.create n in
  for i = 0 to n - 1 do
    Hashtbl.replace nodes i (create_node i)
  done;
  let net = {
    nodes; round = 0; strategy; fanout; infection_prob = prob;
    partitions = []; next_rumor_id = 0; topology;
    history = [];
  } in
  (* build edges *)
  let all_ids = List.init n Fun.id in
  (match topology with
   | FullMesh ->
     Hashtbl.iter (fun id nd ->
       nd.neighbors <- List.filter (fun j -> j <> id) all_ids
     ) nodes
   | Ring ->
     Hashtbl.iter (fun id nd ->
       nd.neighbors <- [(id + n - 1) mod n; (id + 1) mod n]
     ) nodes
   | RandomGraph p ->
     (* ensure connected: start with a spanning tree *)
     let arr = Array.init n Fun.id in
     shuffle arr;
     for i = 1 to n - 1 do
       let a = arr.(i) and b = arr.(rand_int i) in
       let na = Hashtbl.find nodes a and nb = Hashtbl.find nodes b in
       if not (List.mem b na.neighbors) then
         na.neighbors <- b :: na.neighbors;
       if not (List.mem a nb.neighbors) then
         nb.neighbors <- a :: nb.neighbors
     done;
     (* add random edges *)
     for i = 0 to n - 1 do
       for j = i + 1 to n - 1 do
         let ni = Hashtbl.find nodes i and nj = Hashtbl.find nodes j in
         if not (List.mem j ni.neighbors) && rand_float () < p then begin
           ni.neighbors <- j :: ni.neighbors;
           nj.neighbors <- i :: nj.neighbors
         end
       done
     done);
  net

(* ---- Partition Management ---- *)

let same_partition net a b =
  if net.partitions = [] then true
  else
    List.exists (fun p ->
      List.mem a p.members && List.mem b p.members
    ) net.partitions

let create_partition net members =
  let pid = List.length net.partitions in
  let p = { part_id = pid; members; created_round = net.round } in
  net.partitions <- p :: net.partitions;
  Printf.printf "  Partition %d created: nodes [%s] (round %d)\n"
    pid (String.concat ", " (List.map string_of_int members)) net.round;
  p

let heal_partitions net =
  let n = List.length net.partitions in
  net.partitions <- [];
  Printf.printf "  All %d partition(s) healed at round %d\n" n net.round

(* ---- Rumor Management ---- *)

let inject_rumor net node_id payload ?(ttl=0) () =
  let rid = net.next_rumor_id in
  net.next_rumor_id <- rid + 1;
  let r = { rumor_id = rid; origin = node_id; payload;
            created_at = net.round; ttl } in
  let nd = Hashtbl.find net.nodes node_id in
  Hashtbl.replace nd.rumors rid (r, net.round);
  Printf.printf "  Rumor #%d injected at node %d: \"%s\"%s\n"
    rid node_id payload
    (if ttl > 0 then Printf.sprintf " (TTL=%d)" ttl else "");
  r

let expire_rumors net =
  Hashtbl.iter (fun _ nd ->
    let to_remove = Hashtbl.fold (fun rid (r, _) acc ->
      if r.ttl > 0 && net.round - r.created_at >= r.ttl then
        rid :: acc
      else acc
    ) nd.rumors [] in
    List.iter (Hashtbl.remove nd.rumors) to_remove
  ) net.nodes

(* ---- Gossip Rounds ---- *)

let gossip_push net nd =
  if Hashtbl.length nd.rumors = 0 then ()
  else begin
    let reachable = List.filter (fun nid ->
      let target = Hashtbl.find net.nodes nid in
      target.active && same_partition net nd.id nid
    ) nd.neighbors in
    let targets = pick_n_random net.fanout reachable in
    List.iter (fun tid ->
      let target = Hashtbl.find net.nodes tid in
      Hashtbl.iter (fun rid (r, _) ->
        if rand_float () <= net.infection_prob then begin
          if not (Hashtbl.mem target.rumors rid) then begin
            Hashtbl.replace target.rumors rid (r, net.round);
            target.msgs_recv <- target.msgs_recv + 1
          end;
          nd.msgs_sent <- nd.msgs_sent + 1
        end
      ) nd.rumors
    ) targets
  end

let gossip_pull net nd =
  let reachable = List.filter (fun nid ->
    let target = Hashtbl.find net.nodes nid in
    target.active && same_partition net nd.id nid
  ) nd.neighbors in
  let targets = pick_n_random net.fanout reachable in
  List.iter (fun tid ->
    let target = Hashtbl.find net.nodes tid in
    nd.msgs_sent <- nd.msgs_sent + 1;
    target.msgs_recv <- target.msgs_recv + 1;
    (* pull: copy rumors from target *)
    Hashtbl.iter (fun rid (r, _) ->
      if rand_float () <= net.infection_prob then begin
        if not (Hashtbl.mem nd.rumors rid) then
          Hashtbl.replace nd.rumors rid (r, net.round)
      end
    ) target.rumors
  ) targets

let gossip_push_pull net nd =
  let reachable = List.filter (fun nid ->
    let target = Hashtbl.find net.nodes nid in
    target.active && same_partition net nd.id nid
  ) nd.neighbors in
  let targets = pick_n_random net.fanout reachable in
  List.iter (fun tid ->
    let target = Hashtbl.find net.nodes tid in
    (* push *)
    Hashtbl.iter (fun rid (r, _) ->
      if rand_float () <= net.infection_prob then begin
        if not (Hashtbl.mem target.rumors rid) then begin
          Hashtbl.replace target.rumors rid (r, net.round);
          target.msgs_recv <- target.msgs_recv + 1
        end;
        nd.msgs_sent <- nd.msgs_sent + 1
      end
    ) nd.rumors;
    (* pull *)
    Hashtbl.iter (fun rid (r, _) ->
      if rand_float () <= net.infection_prob then begin
        if not (Hashtbl.mem nd.rumors rid) then begin
          Hashtbl.replace nd.rumors rid (r, net.round);
          nd.msgs_recv <- nd.msgs_recv + 1
        end;
        target.msgs_sent <- target.msgs_sent + 1
      end
    ) target.rumors
  ) targets

let run_round net =
  net.round <- net.round + 1;
  expire_rumors net;
  let all_nodes = Hashtbl.fold (fun _ nd acc -> nd :: acc) net.nodes [] in
  let active_nodes = List.filter (fun nd -> nd.active) all_nodes in
  let prev_sent = List.fold_left (fun a nd -> a + nd.msgs_sent) 0 all_nodes in
  let prev_recv = List.fold_left (fun a nd -> a + nd.msgs_recv) 0 all_nodes in
  (* each active node gossips *)
  List.iter (fun nd ->
    match net.strategy with
    | Push -> gossip_push net nd
    | Pull -> gossip_pull net nd
    | PushPull -> gossip_push_pull net nd
  ) active_nodes;
  let total_sent = List.fold_left (fun a nd -> a + nd.msgs_sent) 0 all_nodes in
  let total_recv = List.fold_left (fun a nd -> a + nd.msgs_recv) 0 all_nodes in
  let n_nodes = List.length all_nodes in
  let n_informed = List.length (List.filter (fun nd ->
    Hashtbl.length nd.rumors > 0) all_nodes) in
  let n_rumors = net.next_rumor_id in
  let total_pairs = n_nodes * (max 1 n_rumors) in
  let known_pairs = List.fold_left (fun a nd ->
    a + Hashtbl.length nd.rumors) 0 all_nodes in
  let coverage = if total_pairs > 0 then
    float_of_int known_pairs /. float_of_int total_pairs
  else 0.0 in
  let stats = {
    rs_round = net.round; rs_total_nodes = n_nodes;
    rs_informed = n_informed;
    rs_msgs_sent = total_sent - prev_sent;
    rs_msgs_recv = total_recv - prev_recv;
    rs_unique_rumors = n_rumors;
    rs_coverage = coverage;
  } in
  net.history <- stats :: net.history;
  stats

(* ---- Anti-Entropy ---- *)

let anti_entropy net =
  (* each node syncs with one random neighbor *)
  let count = ref 0 in
  Hashtbl.iter (fun _ nd ->
    if nd.active then begin
      let reachable = List.filter (fun nid ->
        let t = Hashtbl.find net.nodes nid in
        t.active && same_partition net nd.id nid
      ) nd.neighbors in
      match pick_random reachable with
      | None -> ()
      | Some tid ->
        let target = Hashtbl.find net.nodes tid in
        (* bidirectional sync *)
        Hashtbl.iter (fun rid (r, rd) ->
          if not (Hashtbl.mem target.rumors rid) then begin
            Hashtbl.replace target.rumors rid (r, rd);
            incr count
          end
        ) nd.rumors;
        Hashtbl.iter (fun rid (r, rd) ->
          if not (Hashtbl.mem nd.rumors rid) then begin
            Hashtbl.replace nd.rumors rid (r, rd);
            incr count
          end
        ) target.rumors
    end
  ) net.nodes;
  Printf.printf "  Anti-entropy: %d rumor transfers in round %d\n"
    !count net.round

(* ---- Autonomous Protocol Advisor ---- *)

let advise_protocol net =
  let n = Hashtbl.length net.nodes in
  let has_partitions = net.partitions <> [] in
  let avg_degree = if n = 0 then 0.0 else
    let total = Hashtbl.fold (fun _ nd a ->
      a + List.length nd.neighbors) net.nodes 0 in
    float_of_int total /. float_of_int n in
  let coverage = match net.history with
    | s :: _ -> s.rs_coverage | [] -> 0.0 in
  Printf.printf "\n=== Protocol Advisor (round %d) ===\n" net.round;
  Printf.printf "  Network: %d nodes, avg degree %.1f, %s topology\n"
    n avg_degree (topology_to_string net.topology);
  Printf.printf "  Current strategy: %s, fanout: %d, coverage: %.1f%%\n"
    (strategy_to_string net.strategy) net.fanout (coverage *. 100.0);
  if has_partitions then
    Printf.printf "  ⚠ Network partitioned (%d partitions)\n"
      (List.length net.partitions);
  (* recommendations *)
  let rec_strategy =
    if has_partitions then PushPull
    else if avg_degree < 3.0 then PushPull
    else if coverage < 0.5 then Push
    else if coverage > 0.9 then Pull
    else PushPull in
  let rec_fanout =
    if n <= 10 then 2
    else if n <= 50 then 3
    else let lg = log (float_of_int n) /. log 2.0 in
      max 2 (int_of_float (ceil lg)) in
  Printf.printf "  Recommendation:\n";
  if rec_strategy <> net.strategy then
    Printf.printf "    → Switch to %s (better for current conditions)\n"
      (strategy_to_string rec_strategy)
  else
    Printf.printf "    → Keep %s (good fit)\n"
      (strategy_to_string net.strategy);
  if rec_fanout <> net.fanout then
    Printf.printf "    → Adjust fanout to %d (optimal for %d nodes)\n"
      rec_fanout n;
  if has_partitions then
    Printf.printf "    → Run anti-entropy after healing partitions\n";
  if coverage < 0.3 then
    Printf.printf "    → Consider injecting rumors at multiple nodes\n";
  Printf.printf "================================\n"

(* ---- Display ---- *)

let print_stats stats =
  Printf.printf "  Round %d: %d/%d informed (%.1f%% coverage), %d msgs sent, %d rumors\n"
    stats.rs_round stats.rs_informed stats.rs_total_nodes
    (stats.rs_coverage *. 100.0) stats.rs_msgs_sent
    stats.rs_unique_rumors

let print_convergence_chart net =
  Printf.printf "\n=== Convergence Chart ===\n";
  let history = List.rev net.history in
  List.iter (fun s ->
    let bar_len = int_of_float (s.rs_coverage *. 50.0) in
    let bar = String.make bar_len '#' in
    let empty = String.make (50 - bar_len) '.' in
    Printf.printf "  R%3d |%s%s| %5.1f%%\n"
      s.rs_round bar empty (s.rs_coverage *. 100.0)
  ) history;
  Printf.printf "=========================\n"

let print_node_detail net nid =
  match Hashtbl.find_opt net.nodes nid with
  | None -> Printf.printf "  Node %d not found\n" nid
  | Some nd ->
    Printf.printf "  Node %d: %s, %d neighbors, %d rumors, sent=%d recv=%d\n"
      nd.id (if nd.active then "active" else "DOWN")
      (List.length nd.neighbors) (Hashtbl.length nd.rumors)
      nd.msgs_sent nd.msgs_recv;
    Printf.printf "  Neighbors: [%s]\n"
      (String.concat ", " (List.map string_of_int nd.neighbors));
    if Hashtbl.length nd.rumors > 0 then begin
      Printf.printf "  Rumors:\n";
      Hashtbl.iter (fun rid (r, rd) ->
        Printf.printf "    #%d from node %d (round %d): \"%s\"\n"
          rid r.origin rd r.payload
      ) nd.rumors
    end

let print_network_summary net =
  let n = Hashtbl.length net.nodes in
  let active = Hashtbl.fold (fun _ nd a ->
    if nd.active then a + 1 else a) net.nodes 0 in
  let total_rumors = Hashtbl.fold (fun _ nd a ->
    a + Hashtbl.length nd.rumors) net.nodes 0 in
  Printf.printf "\n=== Network Summary ===\n";
  Printf.printf "  Nodes: %d (%d active), Topology: %s\n"
    n active (topology_to_string net.topology);
  Printf.printf "  Strategy: %s, Fanout: %d, Infection prob: %.2f\n"
    (strategy_to_string net.strategy) net.fanout net.infection_prob;
  Printf.printf "  Round: %d, Unique rumors: %d, Total rumor copies: %d\n"
    net.round net.next_rumor_id total_rumors;
  if net.partitions <> [] then begin
    Printf.printf "  Partitions:\n";
    List.iter (fun p ->
      Printf.printf "    Part %d: [%s] (since round %d)\n"
        p.part_id
        (String.concat ", " (List.map string_of_int p.members))
        p.created_round
    ) net.partitions
  end;
  Printf.printf "========================\n"

(* ---- Demos ---- *)

let demo_basic () =
  Printf.printf "\n╔══════════════════════════════════════╗\n";
  Printf.printf "║   Demo: Basic Push-Pull Gossip       ║\n";
  Printf.printf "╚══════════════════════════════════════╝\n\n";
  let net = create_network ~strategy:PushPull ~fanout:3 20 in
  let _ = inject_rumor net 0 "Hello, gossip network!" () in
  Printf.printf "\n  Running 10 rounds of push-pull gossip...\n\n";
  for _ = 1 to 10 do
    let s = run_round net in
    print_stats s;
    if s.rs_coverage >= 1.0 then
      Printf.printf "  ✓ Full convergence reached!\n"
  done;
  print_convergence_chart net

let demo_strategies () =
  Printf.printf "\n╔══════════════════════════════════════╗\n";
  Printf.printf "║   Demo: Strategy Comparison          ║\n";
  Printf.printf "╚══════════════════════════════════════╝\n\n";
  let strategies = [Push; Pull; PushPull] in
  List.iter (fun strat ->
    Printf.printf "--- %s ---\n" (strategy_to_string strat);
    let net = create_network ~strategy:strat ~fanout:3 30 in
    let _ = inject_rumor net 0 "Test rumor" () in
    let converged = ref false in
    for r = 1 to 15 do
      let s = run_round net in
      if r = 5 || r = 10 || r = 15 || s.rs_coverage >= 1.0 then
        print_stats s;
      if s.rs_coverage >= 1.0 && not !converged then begin
        Printf.printf "  ✓ Converged at round %d\n" r;
        converged := true
      end
    done;
    Printf.printf "\n"
  ) strategies

let demo_partition () =
  Printf.printf "\n╔══════════════════════════════════════╗\n";
  Printf.printf "║   Demo: Network Partition & Healing  ║\n";
  Printf.printf "╚══════════════════════════════════════╝\n\n";
  let net = create_network ~strategy:PushPull ~fanout:3 20 in
  let _ = inject_rumor net 0 "Pre-partition rumor" () in
  Printf.printf "\n  Phase 1: Gossip before partition...\n";
  for _ = 1 to 5 do
    let s = run_round net in
    print_stats s
  done;
  Printf.printf "\n  Phase 2: Creating partition...\n";
  let group_a = List.init 10 Fun.id in
  let group_b = List.init 10 (fun i -> i + 10) in
  let _ = create_partition net group_a in
  let _ = create_partition net group_b in
  let _ = inject_rumor net 15 "Post-partition rumor (group B only)" () in
  for _ = 1 to 5 do
    let s = run_round net in
    print_stats s
  done;
  Printf.printf "\n  Phase 3: Healing partitions...\n";
  heal_partitions net;
  anti_entropy net;
  for _ = 1 to 5 do
    let s = run_round net in
    print_stats s
  done;
  print_convergence_chart net

let demo_topologies () =
  Printf.printf "\n╔══════════════════════════════════════╗\n";
  Printf.printf "║   Demo: Topology Comparison          ║\n";
  Printf.printf "╚══════════════════════════════════════╝\n\n";
  let topos = [FullMesh; Ring; RandomGraph 0.3] in
  List.iter (fun topo ->
    Printf.printf "--- %s ---\n" (topology_to_string topo);
    let net = create_network ~strategy:PushPull ~fanout:3 ~topology:topo 25 in
    let _ = inject_rumor net 0 "Topology test" () in
    for r = 1 to 15 do
      let s = run_round net in
      if r = 5 || r = 10 || r = 15 || s.rs_coverage >= 1.0 then
        print_stats s
    done;
    Printf.printf "\n"
  ) topos

let demo_advisor () =
  Printf.printf "\n╔══════════════════════════════════════╗\n";
  Printf.printf "║   Demo: Autonomous Protocol Advisor  ║\n";
  Printf.printf "╚══════════════════════════════════════╝\n\n";
  let net = create_network ~strategy:Push ~fanout:2
      ~topology:(RandomGraph 0.2) 40 in
  let _ = inject_rumor net 0 "Advisor test" () in
  for _ = 1 to 5 do
    let _ = run_round net in ()
  done;
  advise_protocol net;
  Printf.printf "\n  Applying recommendations...\n";
  net.strategy <- PushPull;
  net.fanout <- 6;
  for _ = 1 to 10 do
    let _ = run_round net in ()
  done;
  advise_protocol net

(* ---- REPL ---- *)

let print_help () =
  Printf.printf "\n=== Gossip Protocol Simulator ===\n";
  Printf.printf "Commands:\n";
  Printf.printf "  new <n> [full|ring|random <p>]  Create network with n nodes\n";
  Printf.printf "  strategy <push|pull|pushpull>   Set gossip strategy\n";
  Printf.printf "  fanout <n>                      Set fanout\n";
  Printf.printf "  prob <f>                        Set infection probability\n";
  Printf.printf "  inject <node> <message>         Inject rumor at node\n";
  Printf.printf "  inject <node> <msg> ttl=<n>     Inject with TTL\n";
  Printf.printf "  round [n]                       Run n rounds (default 1)\n";
  Printf.printf "  anti-entropy                    Run anti-entropy repair\n";
  Printf.printf "  partition <id,id,...> <id,...>   Create 2 partitions\n";
  Printf.printf "  heal                            Heal all partitions\n";
  Printf.printf "  kill <node>                     Take node offline\n";
  Printf.printf "  revive <node>                   Bring node back online\n";
  Printf.printf "  node <id>                       Show node details\n";
  Printf.printf "  status                          Network summary\n";
  Printf.printf "  chart                           Convergence chart\n";
  Printf.printf "  advise                          Protocol advisor\n";
  Printf.printf "  demo <basic|strategies|partition|topologies|advisor>\n";
  Printf.printf "  help                            This message\n";
  Printf.printf "  quit                            Exit\n";
  Printf.printf "==================================\n\n"

let parse_ids s =
  String.split_on_char ',' s
  |> List.filter_map (fun x ->
    let x = String.trim x in
    if x = "" then None else Some (int_of_string x))

let () =
  Printf.printf "╔══════════════════════════════════════════════════╗\n";
  Printf.printf "║      Gossip Protocol Simulator                  ║\n";
  Printf.printf "║  Epidemic information dissemination with        ║\n";
  Printf.printf "║  push/pull/push-pull, partitions, anti-entropy  ║\n";
  Printf.printf "╚══════════════════════════════════════════════════╝\n";
  print_help ();
  let net = ref (create_network ~strategy:PushPull ~fanout:3 20) in
  Printf.printf "Default network: 20 nodes, full-mesh, push-pull, fanout=3\n\n";
  let running = ref true in
  while !running do
    Printf.printf "> %!";
    let line = try Some (input_line stdin) with End_of_file -> None in
    match line with
    | None -> running := false
    | Some line ->
      let parts = String.split_on_char ' ' (String.trim line)
        |> List.filter (fun s -> s <> "") in
      match parts with
      | [] -> ()
      | ["quit"] | ["exit"] | ["q"] -> running := false
      | ["help"] | ["h"] | ["?"] -> print_help ()
      | "new" :: n_str :: rest ->
        (try
          let n = int_of_string n_str in
          let topo = match rest with
            | ["ring"] -> Ring
            | ["random"; p] -> RandomGraph (float_of_string p)
            | _ -> FullMesh in
          net := create_network ~strategy:(!net).strategy
              ~fanout:(!net).fanout ~prob:(!net).infection_prob
              ~topology:topo n;
          Printf.printf "  Created %d-node %s network\n" n
            (topology_to_string topo)
        with _ -> Printf.printf "  Usage: new <n> [full|ring|random <p>]\n")
      | ["strategy"; s] ->
        let strat = match s with
          | "push" -> Some Push | "pull" -> Some Pull
          | "pushpull" | "push-pull" -> Some PushPull
          | _ -> None in
        (match strat with
         | Some st ->
           (!net).strategy <- st;
           Printf.printf "  Strategy set to %s\n" (strategy_to_string st)
         | None -> Printf.printf "  Unknown strategy: %s\n" s)
      | ["fanout"; n] ->
        (try
          let f = int_of_string n in
          (!net).fanout <- f;
          Printf.printf "  Fanout set to %d\n" f
        with _ -> Printf.printf "  Usage: fanout <n>\n")
      | ["prob"; p] ->
        (try
          let f = float_of_string p in
          (!net).infection_prob <- f;
          Printf.printf "  Infection probability set to %.2f\n" f
        with _ -> Printf.printf "  Usage: prob <float>\n")
      | "inject" :: node_str :: rest ->
        (try
          let nid = int_of_string node_str in
          let msg_parts = ref [] in
          let ttl = ref 0 in
          List.iter (fun part ->
            if String.length part > 4 && String.sub part 0 4 = "ttl=" then
              ttl := int_of_string (String.sub part 4 (String.length part - 4))
            else
              msg_parts := part :: !msg_parts
          ) rest;
          let msg = String.concat " " (List.rev !msg_parts) in
          let msg = if msg = "" then "rumor" else msg in
          let _ = inject_rumor !net nid msg ~ttl:!ttl () in ()
        with _ -> Printf.printf "  Usage: inject <node> <message> [ttl=<n>]\n")
      | "round" :: rest ->
        let n = match rest with
          | [s] -> (try int_of_string s with _ -> 1)
          | _ -> 1 in
        for _ = 1 to n do
          let s = run_round !net in
          print_stats s
        done
      | ["anti-entropy"] | ["ae"] -> anti_entropy !net
      | ["partition"; a; b] ->
        (try
          let ga = parse_ids a and gb = parse_ids b in
          let _ = create_partition !net ga in
          let _ = create_partition !net gb in ()
        with _ -> Printf.printf "  Usage: partition <id,id,...> <id,...>\n")
      | ["heal"] -> heal_partitions !net
      | ["kill"; n] ->
        (try
          let nid = int_of_string n in
          let nd = Hashtbl.find (!net).nodes nid in
          nd.active <- false;
          Printf.printf "  Node %d taken offline\n" nid
        with _ -> Printf.printf "  Usage: kill <node_id>\n")
      | ["revive"; n] ->
        (try
          let nid = int_of_string n in
          let nd = Hashtbl.find (!net).nodes nid in
          nd.active <- true;
          Printf.printf "  Node %d back online\n" nid
        with _ -> Printf.printf "  Usage: revive <node_id>\n")
      | ["node"; n] ->
        (try
          let nid = int_of_string n in
          print_node_detail !net nid
        with _ -> Printf.printf "  Usage: node <id>\n")
      | ["status"] | ["s"] -> print_network_summary !net
      | ["chart"] | ["c"] -> print_convergence_chart !net
      | ["advise"] | ["a"] -> advise_protocol !net
      | ["demo"; "basic"] -> demo_basic ()
      | ["demo"; "strategies"] -> demo_strategies ()
      | ["demo"; "partition"] -> demo_partition ()
      | ["demo"; "topologies"] -> demo_topologies ()
      | ["demo"; "advisor"] -> demo_advisor ()
      | ["demo"] ->
        Printf.printf "  Demos: basic, strategies, partition, topologies, advisor\n"
      | _ -> Printf.printf "  Unknown command. Type 'help' for usage.\n"
  done;
  Printf.printf "\nGoodbye!\n"
