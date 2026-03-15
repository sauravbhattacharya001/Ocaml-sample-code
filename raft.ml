(* raft.ml — Raft Consensus Algorithm
 *
 * A simulation of the Raft distributed consensus protocol.
 * Implements leader election, log replication, and commitment
 * with a deterministic in-memory message-passing network.
 *
 * Usage:
 *   ocamlfind ocamlopt -package unix -linkpkg raft.ml -o raft && ./raft
 *   ocamlfind ocamlc  -package unix -linkpkg raft.ml -o raft && ./raft
 *
 * Features:
 *   - Full leader election with randomized timeouts
 *   - Log replication with AppendEntries RPCs
 *   - Commitment via majority quorum
 *   - Network partitioning simulation
 *   - Step-by-step execution for learning
 *)

(* ---- Types ---- *)

type node_id = int

type role = Follower | Candidate | Leader

type log_entry = {
  term  : int;
  index : int;
  command : string;
}

type append_entries_req = {
  ae_term          : int;
  ae_leader_id     : node_id;
  ae_prev_log_idx  : int;
  ae_prev_log_term : int;
  ae_entries       : log_entry list;
  ae_leader_commit : int;
}

type append_entries_resp = {
  aer_term    : int;
  aer_success : bool;
  aer_node_id : node_id;
  aer_match_index : int;
}

type request_vote_req = {
  rv_term           : int;
  rv_candidate_id   : node_id;
  rv_last_log_idx   : int;
  rv_last_log_term  : int;
}

type request_vote_resp = {
  rvr_term         : int;
  rvr_vote_granted : bool;
  rvr_node_id      : node_id;
}

type message =
  | AppendEntriesReq  of node_id * append_entries_req
  | AppendEntriesResp of node_id * append_entries_resp
  | RequestVoteReq    of node_id * request_vote_req
  | RequestVoteResp   of node_id * request_vote_resp

type node_state = {
  id             : node_id;
  mutable role   : role;
  mutable term   : int;
  mutable voted_for : node_id option;
  mutable log    : log_entry list;  (* reverse order, head = newest *)
  mutable commit_index : int;
  mutable last_applied : int;

  (* Leader state *)
  mutable next_index  : (node_id * int) list;
  mutable match_index : (node_id * int) list;

  (* Election timer *)
  mutable election_timeout  : int;  (* ticks until election *)
  mutable ticks_since_heard : int;

  (* Votes received *)
  mutable votes_received : node_id list;
}

(* ---- Helpers ---- *)

let log_length node = List.length node.log

let last_log_index node = log_length node

let last_log_term node =
  match node.log with
  | [] -> 0
  | e :: _ -> e.term

let get_log_entry node idx =
  (* log is in reverse order: head = last entry *)
  let len = List.length node.log in
  if idx < 1 || idx > len then None
  else Some (List.nth node.log (len - idx))

let get_log_term node idx =
  match get_log_entry node idx with
  | None -> 0
  | Some e -> e.term

let role_to_string = function
  | Follower -> "Follower"
  | Candidate -> "Candidate"
  | Leader -> "Leader"

(* ---- Node creation ---- *)

let make_node id num_nodes =
  let _ = num_nodes in
  {
    id;
    role = Follower;
    term = 0;
    voted_for = None;
    log = [];
    commit_index = 0;
    last_applied = 0;
    next_index = [];
    match_index = [];
    election_timeout = 5 + (id * 3) mod 7;  (* deterministic but varied *)
    ticks_since_heard = 0;
    votes_received = [];
  }

(* ---- Become leader ---- *)

let become_leader node all_ids =
  node.role <- Leader;
  let next = last_log_index node + 1 in
  node.next_index <- List.filter_map (fun nid ->
    if nid = node.id then None else Some (nid, next)
  ) all_ids;
  node.match_index <- List.filter_map (fun nid ->
    if nid = node.id then None else Some (nid, 0)
  ) all_ids;
  node.ticks_since_heard <- 0

(* ---- Step down ---- *)

let step_down node new_term =
  node.term <- new_term;
  node.role <- Follower;
  node.voted_for <- None;
  node.ticks_since_heard <- 0

(* ---- Advance commit index (leader) ---- *)

let advance_commit_index node majority =
  (* Find the highest N such that a majority of matchIndex[i] >= N
     and log[N].term == currentTerm *)
  let max_idx = last_log_index node in
  let rec try_n n =
    if n < 1 then ()
    else begin
      let count = List.fold_left (fun acc (_nid, mi) ->
        if mi >= n then acc + 1 else acc
      ) 1 node.match_index in  (* +1 for self *)
      if count >= majority && get_log_term node n = node.term then
        node.commit_index <- max node.commit_index n
      else
        try_n (n - 1)
    end
  in
  try_n max_idx

(* ---- Handle RequestVote ---- *)

let handle_request_vote node req =
  let grant =
    if req.rv_term < node.term then false
    else begin
      if req.rv_term > node.term then
        step_down node req.rv_term;
      match node.voted_for with
      | Some v when v <> req.rv_candidate_id -> false
      | _ ->
        (* Check log is at least as up-to-date *)
        let my_last_term = last_log_term node in
        let my_last_idx = last_log_index node in
        let ok =
          req.rv_last_log_term > my_last_term ||
          (req.rv_last_log_term = my_last_term && req.rv_last_log_idx >= my_last_idx)
        in
        if ok then begin
          node.voted_for <- Some req.rv_candidate_id;
          node.ticks_since_heard <- 0
        end;
        ok
    end
  in
  { rvr_term = node.term; rvr_vote_granted = grant; rvr_node_id = node.id }

(* ---- Handle RequestVote Response ---- *)

let handle_request_vote_resp node resp all_ids majority =
  let msgs = ref [] in
  if resp.rvr_term > node.term then
    step_down node resp.rvr_term
  else if node.role = Candidate && resp.rvr_vote_granted then begin
    if not (List.mem resp.rvr_node_id node.votes_received) then
      node.votes_received <- resp.rvr_node_id :: node.votes_received;
    if List.length node.votes_received >= majority then begin
      become_leader node all_ids;
      Printf.printf "  [Node %d] Won election for term %d!\n" node.id node.term;
      (* Send initial empty AppendEntries (heartbeat) *)
      List.iter (fun (nid, _) ->
        let prev_idx = last_log_index node in
        let req = {
          ae_term = node.term;
          ae_leader_id = node.id;
          ae_prev_log_idx = prev_idx;
          ae_prev_log_term = get_log_term node prev_idx;
          ae_entries = [];
          ae_leader_commit = node.commit_index;
        } in
        msgs := AppendEntriesReq (nid, req) :: !msgs
      ) node.next_index
    end
  end;
  !msgs

(* ---- Handle AppendEntries ---- *)

let handle_append_entries node req =
  if req.ae_term < node.term then
    { aer_term = node.term; aer_success = false;
      aer_node_id = node.id; aer_match_index = 0 }
  else begin
    if req.ae_term > node.term then
      step_down node req.ae_term
    else begin
      node.role <- Follower;  (* recognize leader *)
      node.ticks_since_heard <- 0
    end;
    (* Check prev log entry matches *)
    if req.ae_prev_log_idx > 0 then begin
      let prev_term = get_log_term node req.ae_prev_log_idx in
      if prev_term <> req.ae_prev_log_term then
        { aer_term = node.term; aer_success = false;
          aer_node_id = node.id; aer_match_index = 0 }
      else begin
        (* Append new entries (truncate conflicts) *)
        let keep = req.ae_prev_log_idx in
        let len = List.length node.log in
        let trimmed = if keep < len then
          let rev = List.rev node.log in
          List.rev (List.filteri (fun i _ -> i < keep) rev)
        else node.log in
        let new_entries = req.ae_entries in
        node.log <- trimmed @ new_entries;
        let new_match = last_log_index node in
        if req.ae_leader_commit > node.commit_index then
          node.commit_index <- min req.ae_leader_commit new_match;
        { aer_term = node.term; aer_success = true;
          aer_node_id = node.id; aer_match_index = new_match }
      end
    end else begin
      (* prev_log_idx = 0 means starting from scratch *)
      node.log <- req.ae_entries;
      let new_match = last_log_index node in
      if req.ae_leader_commit > node.commit_index then
        node.commit_index <- min req.ae_leader_commit new_match;
      { aer_term = node.term; aer_success = true;
        aer_node_id = node.id; aer_match_index = new_match }
    end
  end

(* ---- Handle AppendEntries Response (leader) ---- *)

let handle_append_entries_resp node resp majority =
  let msgs = ref [] in
  if resp.aer_term > node.term then
    step_down node resp.aer_term
  else if node.role = Leader then begin
    if resp.aer_success then begin
      node.match_index <- List.map (fun (nid, mi) ->
        if nid = resp.aer_node_id then (nid, max mi resp.aer_match_index)
        else (nid, mi)
      ) node.match_index;
      node.next_index <- List.map (fun (nid, ni) ->
        if nid = resp.aer_node_id then (nid, resp.aer_match_index + 1)
        else (nid, ni)
      ) node.next_index;
      advance_commit_index node majority
    end else begin
      (* Decrement nextIndex and retry *)
      node.next_index <- List.map (fun (nid, ni) ->
        if nid = resp.aer_node_id then (nid, max 1 (ni - 1))
        else (nid, ni)
      ) node.next_index;
      let ni = List.assoc resp.aer_node_id node.next_index in
      let prev_idx = ni - 1 in
      let entries_to_send =
        List.filteri (fun i _ -> i >= ni - 1) node.log
      in
      let req = {
        ae_term = node.term;
        ae_leader_id = node.id;
        ae_prev_log_idx = prev_idx;
        ae_prev_log_term = get_log_term node prev_idx;
        ae_entries = entries_to_send;
        ae_leader_commit = node.commit_index;
      } in
      msgs := AppendEntriesReq (resp.aer_node_id, req) :: !msgs
    end
  end;
  !msgs

(* ---- Cluster simulation ---- *)

type cluster = {
  nodes    : node_state array;
  num      : int;
  majority : int;
  all_ids  : node_id list;
  mutable msg_queue : message list;
  mutable partitioned : (node_id * node_id) list;  (* blocked pairs *)
  mutable tick : int;
}

let make_cluster n =
  let nodes = Array.init n (fun i -> make_node i n) in
  {
    nodes;
    num = n;
    majority = n / 2 + 1;
    all_ids = List.init n Fun.id;
    msg_queue = [];
    partitioned = [];
    tick = 0;
  }

let is_partitioned cluster a b =
  List.exists (fun (x, y) ->
    (x = a && y = b) || (x = b && y = a)
  ) cluster.partitioned

let enqueue cluster msg =
  cluster.msg_queue <- cluster.msg_queue @ [msg]

let dest_of = function
  | AppendEntriesReq  (dst, _) -> dst
  | AppendEntriesResp (dst, _) -> dst
  | RequestVoteReq    (dst, _) -> dst
  | RequestVoteResp   (dst, _) -> dst

let src_of = function
  | AppendEntriesReq  (_, r) -> r.ae_leader_id
  | AppendEntriesResp (_, r) -> r.aer_node_id
  | RequestVoteReq    (_, r) -> r.rv_candidate_id
  | RequestVoteResp   (_, r) -> r.rvr_node_id

(* ---- Tick: election timer + heartbeats ---- *)

let tick_node cluster node =
  match node.role with
  | Leader ->
    (* Send heartbeats *)
    List.iter (fun (nid, ni) ->
      if not (is_partitioned cluster node.id nid) then begin
        let prev_idx = ni - 1 in
        let entries =
          List.filteri (fun i _ -> i >= ni - 1) node.log
        in
        let req = {
          ae_term = node.term;
          ae_leader_id = node.id;
          ae_prev_log_idx = prev_idx;
          ae_prev_log_term = get_log_term node prev_idx;
          ae_entries = entries;
          ae_leader_commit = node.commit_index;
        } in
        enqueue cluster (AppendEntriesReq (nid, req))
      end
    ) node.next_index

  | Follower | Candidate ->
    node.ticks_since_heard <- node.ticks_since_heard + 1;
    if node.ticks_since_heard >= node.election_timeout then begin
      (* Start election *)
      node.term <- node.term + 1;
      node.role <- Candidate;
      node.voted_for <- Some node.id;
      node.votes_received <- [node.id];
      node.ticks_since_heard <- 0;
      (* Randomize next timeout *)
      node.election_timeout <- 4 + (node.id + node.term * 3) mod 5;
      Printf.printf "  [Node %d] Starting election for term %d\n" node.id node.term;
      List.iter (fun nid ->
        if nid <> node.id && not (is_partitioned cluster node.id nid) then begin
          let req = {
            rv_term = node.term;
            rv_candidate_id = node.id;
            rv_last_log_idx = last_log_index node;
            rv_last_log_term = last_log_term node;
          } in
          enqueue cluster (RequestVoteReq (nid, req))
        end
      ) cluster.all_ids
    end

(* ---- Process one message ---- *)

let process_message cluster msg =
  let dst = dest_of msg in
  let src = src_of msg in
  if is_partitioned cluster src dst then ()
  else begin
    let node = cluster.nodes.(dst) in
    match msg with
    | RequestVoteReq (_, req) ->
      let resp = handle_request_vote node req in
      enqueue cluster (RequestVoteResp (src, resp))

    | RequestVoteResp (_, resp) ->
      let msgs = handle_request_vote_resp node resp cluster.all_ids cluster.majority in
      List.iter (enqueue cluster) msgs

    | AppendEntriesReq (_, req) ->
      let resp = handle_append_entries node req in
      enqueue cluster (AppendEntriesResp (src, resp))

    | AppendEntriesResp (_, resp) ->
      let msgs = handle_append_entries_resp node resp cluster.majority in
      List.iter (enqueue cluster) msgs
  end

(* ---- Run one tick ---- *)

let run_tick cluster =
  cluster.tick <- cluster.tick + 1;
  Printf.printf "\n=== Tick %d ===\n" cluster.tick;
  Array.iter (tick_node cluster) cluster.nodes;
  (* Process all queued messages *)
  let msgs = cluster.msg_queue in
  cluster.msg_queue <- [];
  List.iter (process_message cluster) msgs

(* ---- Client request (submit command to leader) ---- *)

let client_request cluster cmd =
  let leader = Array.to_list cluster.nodes |>
    List.find_opt (fun n -> n.role = Leader)
  in
  match leader with
  | None ->
    Printf.printf "  [Client] No leader available, request '%s' rejected\n" cmd;
    false
  | Some node ->
    let entry = {
      term = node.term;
      index = last_log_index node + 1;
      command = cmd;
    } in
    node.log <- entry :: node.log;
    (* Update own match_index *)
    Printf.printf "  [Client] Submitted '%s' to leader (Node %d)\n" cmd node.id;
    true

(* ---- Print cluster state ---- *)

let print_state cluster =
  Printf.printf "\n--- Cluster State (tick %d) ---\n" cluster.tick;
  Array.iter (fun n ->
    Printf.printf "  Node %d: %s  term=%d  log=%d  commit=%d"
      n.id (role_to_string n.role) n.term (log_length n) n.commit_index;
    (match n.voted_for with
     | Some v -> Printf.printf "  voted=%d" v
     | None -> ());
    if n.role = Leader then
      Printf.printf "  [LEADER]";
    Printf.printf "\n"
  ) cluster.nodes;
  Printf.printf "  Messages in flight: %d\n" (List.length cluster.msg_queue)

(* ---- Demo scenario ---- *)

let () =
  Printf.printf "╔══════════════════════════════════════════╗\n";
  Printf.printf "║    Raft Consensus Algorithm in OCaml     ║\n";
  Printf.printf "║    5-node cluster simulation             ║\n";
  Printf.printf "╚══════════════════════════════════════════╝\n";

  let cluster = make_cluster 5 in

  (* Phase 1: Leader election *)
  Printf.printf "\n▶ Phase 1: Leader Election\n";
  Printf.printf "  Running ticks until a leader is elected...\n";
  let elected = ref false in
  for _ = 1 to 20 do
    if not !elected then begin
      run_tick cluster;
      if Array.exists (fun n -> n.role = Leader) cluster.nodes then
        elected := true
    end
  done;
  print_state cluster;

  (* Phase 2: Log replication *)
  Printf.printf "\n▶ Phase 2: Log Replication\n";
  Printf.printf "  Submitting client commands...\n";
  let _ = client_request cluster "SET x = 1" in
  let _ = client_request cluster "SET y = 2" in
  for _ = 1 to 5 do run_tick cluster done;
  let _ = client_request cluster "SET z = x + y" in
  for _ = 1 to 5 do run_tick cluster done;
  print_state cluster;

  (* Show committed log *)
  Printf.printf "\n  Committed log entries:\n";
  let leader = Array.to_list cluster.nodes |>
    List.find (fun n -> n.role = Leader) in
  List.rev leader.log |> List.iter (fun e ->
    let status = if e.index <= leader.commit_index then "✓" else "…" in
    Printf.printf "    %s [%d] term=%d: %s\n" status e.index e.term e.command
  );

  (* Phase 3: Network partition *)
  Printf.printf "\n▶ Phase 3: Network Partition\n";
  Printf.printf "  Isolating the leader (Node %d) from the cluster...\n" leader.id;
  List.iter (fun nid ->
    if nid <> leader.id then
      cluster.partitioned <- (leader.id, nid) :: cluster.partitioned
  ) cluster.all_ids;

  for _ = 1 to 15 do run_tick cluster done;
  print_state cluster;

  (* Try to write during partition *)
  Printf.printf "\n  Attempting write to old leader (should fail to commit):\n";
  let _ = client_request cluster "SET w = 99" in
  for _ = 1 to 3 do run_tick cluster done;

  (* New leader should exist *)
  let new_leader = Array.to_list cluster.nodes |>
    List.find_opt (fun n -> n.role = Leader && n.id <> leader.id) in
  (match new_leader with
   | Some nl ->
     Printf.printf "  New leader elected: Node %d (term %d)\n" nl.id nl.term
   | None ->
     Printf.printf "  No new leader yet (may need more ticks)\n");

  (* Phase 4: Heal partition *)
  Printf.printf "\n▶ Phase 4: Healing Partition\n";
  cluster.partitioned <- [];
  for _ = 1 to 10 do run_tick cluster done;
  print_state cluster;

  (* Final: verify all nodes converged *)
  Printf.printf "\n▶ Final: Convergence Check\n";
  let terms = Array.map (fun n -> n.term) cluster.nodes in
  let commits = Array.map (fun n -> n.commit_index) cluster.nodes in
  let max_term = Array.fold_left max 0 terms in
  let min_commit = Array.fold_left min max_int commits in
  Printf.printf "  Max term: %d\n" max_term;
  Printf.printf "  Min commit index: %d (all nodes committed at least this far)\n" min_commit;
  let leaders = Array.to_list cluster.nodes |>
    List.filter (fun n -> n.role = Leader) in
  Printf.printf "  Active leaders: %d\n" (List.length leaders);
  if List.length leaders = 1 then
    Printf.printf "  ✓ Single leader — consensus achieved!\n"
  else
    Printf.printf "  ⚠ Multiple or no leaders — split brain or still converging\n";

  Printf.printf "\n════════════════════════════════════════════\n";
  Printf.printf "  Raft simulation complete.\n";
  Printf.printf "════════════════════════════════════════════\n"
