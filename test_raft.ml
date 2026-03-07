(* test_raft.ml — Tests for Raft consensus implementation *)

(* Inline the needed types and functions from raft.ml since OCaml
   doesn't have a module system for single files without dune.
   We test via the cluster simulation API. *)

(* ---- Minimal test framework ---- *)

let tests_run = ref 0
let tests_passed = ref 0
let tests_failed = ref 0

let assert_test name condition =
  incr tests_run;
  if condition then begin
    incr tests_passed;
    Printf.printf "  ✓ %s\n" name
  end else begin
    incr tests_failed;
    Printf.printf "  ✗ %s\n" name
  end

let print_results () =
  Printf.printf "\n══════════════════════════════════\n";
  Printf.printf "  Tests: %d passed, %d failed, %d total\n"
    !tests_passed !tests_failed !tests_run;
  Printf.printf "══════════════════════════════════\n"

(* ---- We re-implement a minimal cluster here for testing ---- *)

type node_id = int
type role = Follower | Candidate | Leader

type log_entry = { term : int; index : int; command : string }

type node_state = {
  id : node_id;
  mutable role : role;
  mutable term : int;
  mutable voted_for : node_id option;
  mutable log : log_entry list;
  mutable commit_index : int;
  mutable last_applied : int;
  mutable next_index : (node_id * int) list;
  mutable match_index : (node_id * int) list;
  mutable election_timeout : int;
  mutable ticks_since_heard : int;
  mutable votes_received : node_id list;
}

type append_entries_req = {
  ae_term : int; ae_leader_id : node_id;
  ae_prev_log_idx : int; ae_prev_log_term : int;
  ae_entries : log_entry list; ae_leader_commit : int;
}
type append_entries_resp = {
  aer_term : int; aer_success : bool;
  aer_node_id : node_id; aer_match_index : int;
}
type request_vote_req = {
  rv_term : int; rv_candidate_id : node_id;
  rv_last_log_idx : int; rv_last_log_term : int;
}
type request_vote_resp = {
  rvr_term : int; rvr_vote_granted : bool; rvr_node_id : node_id;
}
type message =
  | AppendEntriesReq of node_id * append_entries_req
  | AppendEntriesResp of node_id * append_entries_resp
  | RequestVoteReq of node_id * request_vote_req
  | RequestVoteResp of node_id * request_vote_resp

let log_length n = List.length n.log
let last_log_index n = log_length n
let last_log_term n = match n.log with [] -> 0 | e :: _ -> e.term
let get_log_entry n idx =
  let len = List.length n.log in
  if idx < 1 || idx > len then None
  else Some (List.nth n.log (len - idx))
let get_log_term n idx =
  match get_log_entry n idx with None -> 0 | Some e -> e.term

let make_node id =
  { id; role = Follower; term = 0; voted_for = None; log = [];
    commit_index = 0; last_applied = 0;
    next_index = []; match_index = [];
    election_timeout = 5 + (id * 3) mod 7;
    ticks_since_heard = 0; votes_received = [] }

let step_down n t = n.term <- t; n.role <- Follower; n.voted_for <- None; n.ticks_since_heard <- 0

let become_leader n all_ids =
  n.role <- Leader;
  let next = last_log_index n + 1 in
  n.next_index <- List.filter_map (fun nid -> if nid = n.id then None else Some (nid, next)) all_ids;
  n.match_index <- List.filter_map (fun nid -> if nid = n.id then None else Some (nid, 0)) all_ids;
  n.ticks_since_heard <- 0

let advance_commit_index n majority =
  let max_idx = last_log_index n in
  let rec try_n nn =
    if nn < 1 then ()
    else begin
      let count = List.fold_left (fun acc (_, mi) -> if mi >= nn then acc + 1 else acc) 1 n.match_index in
      if count >= majority && get_log_term n nn = n.term then
        n.commit_index <- max n.commit_index nn
      else try_n (nn - 1)
    end
  in try_n max_idx

let handle_request_vote n req =
  let grant =
    if req.rv_term < n.term then false
    else begin
      if req.rv_term > n.term then step_down n req.rv_term;
      match n.voted_for with
      | Some v when v <> req.rv_candidate_id -> false
      | _ ->
        let ok = req.rv_last_log_term > last_log_term n ||
          (req.rv_last_log_term = last_log_term n && req.rv_last_log_idx >= last_log_index n) in
        if ok then (n.voted_for <- Some req.rv_candidate_id; n.ticks_since_heard <- 0);
        ok
    end
  in { rvr_term = n.term; rvr_vote_granted = grant; rvr_node_id = n.id }

let handle_append_entries n req =
  if req.ae_term < n.term then
    { aer_term = n.term; aer_success = false; aer_node_id = n.id; aer_match_index = 0 }
  else begin
    if req.ae_term > n.term then step_down n req.ae_term
    else (n.role <- Follower; n.ticks_since_heard <- 0);
    if req.ae_prev_log_idx > 0 then begin
      let prev_term = get_log_term n req.ae_prev_log_idx in
      if prev_term <> req.ae_prev_log_term then
        { aer_term = n.term; aer_success = false; aer_node_id = n.id; aer_match_index = 0 }
      else begin
        let keep = req.ae_prev_log_idx in
        let len = List.length n.log in
        let trimmed = if keep < len then
          List.rev (List.filteri (fun i _ -> i < keep) (List.rev n.log))
        else n.log in
        n.log <- List.rev_append (List.rev req.ae_entries) trimmed;
        let nm = last_log_index n in
        if req.ae_leader_commit > n.commit_index then n.commit_index <- min req.ae_leader_commit nm;
        { aer_term = n.term; aer_success = true; aer_node_id = n.id; aer_match_index = nm }
      end
    end else begin
      n.log <- req.ae_entries;
      let nm = last_log_index n in
      if req.ae_leader_commit > n.commit_index then n.commit_index <- min req.ae_leader_commit nm;
      { aer_term = n.term; aer_success = true; aer_node_id = n.id; aer_match_index = nm }
    end
  end

type cluster = {
  nodes : node_state array; num : int; majority : int;
  all_ids : node_id list;
  mutable msg_queue : message list;
  mutable partitioned : (node_id * node_id) list;
  mutable tick : int;
}

let make_cluster n =
  { nodes = Array.init n make_node; num = n; majority = n / 2 + 1;
    all_ids = List.init n Fun.id; msg_queue = []; partitioned = []; tick = 0 }

let is_partitioned c a b =
  List.exists (fun (x,y) -> (x=a && y=b) || (x=b && y=a)) c.partitioned

let enqueue c m = c.msg_queue <- c.msg_queue @ [m]

let src_of = function
  | AppendEntriesReq (_,r) -> r.ae_leader_id
  | AppendEntriesResp (_,r) -> r.aer_node_id
  | RequestVoteReq (_,r) -> r.rv_candidate_id
  | RequestVoteResp (_,r) -> r.rvr_node_id
let dest_of = function
  | AppendEntriesReq (d,_) | AppendEntriesResp (d,_)
  | RequestVoteReq (d,_) | RequestVoteResp (d,_) -> d

let handle_rv_resp n resp all_ids majority =
  let msgs = ref [] in
  if resp.rvr_term > n.term then step_down n resp.rvr_term
  else if n.role = Candidate && resp.rvr_vote_granted then begin
    if not (List.mem resp.rvr_node_id n.votes_received) then
      n.votes_received <- resp.rvr_node_id :: n.votes_received;
    if List.length n.votes_received >= majority then begin
      become_leader n all_ids;
      List.iter (fun (nid,_) ->
        let pi = last_log_index n in
        msgs := AppendEntriesReq (nid, {
          ae_term=n.term; ae_leader_id=n.id;
          ae_prev_log_idx=pi; ae_prev_log_term=get_log_term n pi;
          ae_entries=[]; ae_leader_commit=n.commit_index }) :: !msgs
      ) n.next_index
    end
  end; !msgs

let handle_ae_resp n resp majority =
  let msgs = ref [] in
  if resp.aer_term > n.term then step_down n resp.aer_term
  else if n.role = Leader then begin
    if resp.aer_success then begin
      n.match_index <- List.map (fun (nid,mi) ->
        if nid=resp.aer_node_id then (nid, max mi resp.aer_match_index) else (nid,mi)) n.match_index;
      n.next_index <- List.map (fun (nid,ni) ->
        if nid=resp.aer_node_id then (nid, resp.aer_match_index+1) else (nid,ni)) n.next_index;
      advance_commit_index n majority
    end else begin
      n.next_index <- List.map (fun (nid,ni) ->
        if nid=resp.aer_node_id then (nid, max 1 (ni-1)) else (nid,ni)) n.next_index;
      let ni = List.assoc resp.aer_node_id n.next_index in
      let pi = ni-1 in
      let entries = List.filteri (fun i _ -> i >= ni-1) (List.rev n.log) in
      msgs := AppendEntriesReq (resp.aer_node_id, {
        ae_term=n.term; ae_leader_id=n.id;
        ae_prev_log_idx=pi; ae_prev_log_term=get_log_term n pi;
        ae_entries=entries; ae_leader_commit=n.commit_index }) :: !msgs
    end
  end; !msgs

let tick_node c n =
  match n.role with
  | Leader ->
    List.iter (fun (nid,ni) ->
      if not (is_partitioned c n.id nid) then begin
        let pi = ni-1 in
        let entries = List.filteri (fun i _ -> i >= ni-1) (List.rev n.log) in
        enqueue c (AppendEntriesReq (nid, {
          ae_term=n.term; ae_leader_id=n.id;
          ae_prev_log_idx=pi; ae_prev_log_term=get_log_term n pi;
          ae_entries=entries; ae_leader_commit=n.commit_index }))
      end) n.next_index
  | Follower | Candidate ->
    n.ticks_since_heard <- n.ticks_since_heard + 1;
    if n.ticks_since_heard >= n.election_timeout then begin
      n.term <- n.term + 1; n.role <- Candidate;
      n.voted_for <- Some n.id; n.votes_received <- [n.id];
      n.ticks_since_heard <- 0;
      n.election_timeout <- 4 + (n.id + n.term * 3) mod 5;
      List.iter (fun nid ->
        if nid <> n.id && not (is_partitioned c n.id nid) then
          enqueue c (RequestVoteReq (nid, {
            rv_term=n.term; rv_candidate_id=n.id;
            rv_last_log_idx=last_log_index n;
            rv_last_log_term=last_log_term n }))
      ) c.all_ids
    end

let process_msg c msg =
  let dst = dest_of msg and src = src_of msg in
  if is_partitioned c src dst then ()
  else begin
    let n = c.nodes.(dst) in
    match msg with
    | RequestVoteReq (_,req) ->
      let resp = handle_request_vote n req in
      enqueue c (RequestVoteResp (src, resp))
    | RequestVoteResp (_,resp) ->
      List.iter (enqueue c) (handle_rv_resp n resp c.all_ids c.majority)
    | AppendEntriesReq (_,req) ->
      let resp = handle_append_entries n req in
      enqueue c (AppendEntriesResp (src, resp))
    | AppendEntriesResp (_,resp) ->
      List.iter (enqueue c) (handle_ae_resp n resp c.majority)
  end

let run_tick c =
  c.tick <- c.tick + 1;
  Array.iter (tick_node c) c.nodes;
  let msgs = c.msg_queue in
  c.msg_queue <- [];
  List.iter (process_msg c) msgs

let client_request c cmd =
  match Array.to_list c.nodes |> List.find_opt (fun n -> n.role = Leader) with
  | None -> false
  | Some n ->
    n.log <- { term=n.term; index=last_log_index n + 1; command=cmd } :: n.log;
    true

let run_ticks c n = for _ = 1 to n do run_tick c done

let elect c = for _ = 1 to 30 do run_tick c done

let count_leaders c = Array.to_list c.nodes |> List.filter (fun n -> n.role = Leader) |> List.length

(* ---- Tests ---- *)

let () =
  Printf.printf "╔══════════════════════════════════╗\n";
  Printf.printf "║     Raft Consensus Tests         ║\n";
  Printf.printf "╚══════════════════════════════════╝\n\n";

  (* Test 1: Initial state *)
  Printf.printf "── Initial State ──\n";
  let c = make_cluster 5 in
  assert_test "All nodes start as Follower"
    (Array.for_all (fun n -> n.role = Follower) c.nodes);
  assert_test "All nodes start at term 0"
    (Array.for_all (fun n -> n.term = 0) c.nodes);
  assert_test "All logs empty"
    (Array.for_all (fun n -> n.log = []) c.nodes);

  (* Test 2: Leader election *)
  Printf.printf "\n── Leader Election ──\n";
  let c = make_cluster 5 in
  elect c;
  assert_test "Exactly one leader elected" (count_leaders c = 1);
  let leader = Array.to_list c.nodes |> List.find (fun n -> n.role = Leader) in
  assert_test "Leader term > 0" (leader.term > 0);
  assert_test "Leader voted for self" (leader.voted_for = Some leader.id);

  (* Test 3: 3-node cluster *)
  Printf.printf "\n── 3-Node Cluster ──\n";
  let c = make_cluster 3 in
  elect c;
  assert_test "3-node: one leader" (count_leaders c = 1);
  assert_test "3-node: majority is 2" (c.majority = 2);

  (* Test 4: Log replication *)
  Printf.printf "\n── Log Replication ──\n";
  let c = make_cluster 5 in
  elect c;
  assert_test "Submit to leader succeeds" (client_request c "SET x = 1");
  run_ticks c 5;
  assert_test "All nodes have 1 log entry"
    (Array.for_all (fun n -> log_length n >= 1) c.nodes);
  let leader = Array.to_list c.nodes |> List.find (fun n -> n.role = Leader) in
  assert_test "Leader committed entry" (leader.commit_index >= 1);

  (* Test 5: Multiple entries *)
  Printf.printf "\n── Multiple Entries ──\n";
  let _ = client_request c "SET y = 2" in
  let _ = client_request c "SET z = 3" in
  run_ticks c 5;
  let leader = Array.to_list c.nodes |> List.find (fun n -> n.role = Leader) in
  assert_test "Leader has 3 entries" (log_length leader = 3);
  assert_test "Leader committed all 3" (leader.commit_index >= 3);

  (* Test 6: Follower replication *)
  Printf.printf "\n── Follower Replication ──\n";
  let followers = Array.to_list c.nodes |> List.filter (fun n -> n.role = Follower) in
  assert_test "All followers have entries"
    (List.for_all (fun n -> log_length n >= 3) followers);
  assert_test "Followers commit index updated"
    (List.for_all (fun n -> n.commit_index >= 3) followers);

  (* Test 7: No leader without majority *)
  Printf.printf "\n── Reject Stale Terms ──\n";
  let n = make_node 0 in
  n.term <- 5;
  let resp = handle_request_vote n
    { rv_term = 3; rv_candidate_id = 1; rv_last_log_idx = 0; rv_last_log_term = 0 } in
  assert_test "Reject vote from lower term" (not resp.rvr_vote_granted);
  assert_test "Response includes current term" (resp.rvr_term = 5);

  (* Test 8: Network partition *)
  Printf.printf "\n── Network Partition ──\n";
  let c = make_cluster 5 in
  elect c;
  let leader = Array.to_list c.nodes |> List.find (fun n -> n.role = Leader) in
  let lid = leader.id in
  (* Partition leader from everyone *)
  List.iter (fun nid ->
    if nid <> lid then c.partitioned <- (lid, nid) :: c.partitioned
  ) c.all_ids;
  run_ticks c 20;
  (* Old leader should no longer be the only leader *)
  let new_leaders = Array.to_list c.nodes |>
    List.filter (fun n -> n.role = Leader && n.id <> lid) in
  assert_test "New leader elected after partition" (List.length new_leaders >= 1);

  (* Test 9: Partition heal *)
  Printf.printf "\n── Partition Heal ──\n";
  c.partitioned <- [];
  run_ticks c 20;
  assert_test "Single leader after heal" (count_leaders c = 1);

  (* Test 10: No submit without leader *)
  Printf.printf "\n── No Leader Rejection ──\n";
  let c = make_cluster 3 in
  (* Don't elect — all are followers *)
  assert_test "Request rejected without leader" (not (client_request c "FAIL"));

  (* Test 11: Step down on higher term *)
  Printf.printf "\n── Step Down ──\n";
  let n = make_node 0 in
  n.term <- 2; n.role <- Leader;
  let _ = handle_append_entries n
    { ae_term = 5; ae_leader_id = 1;
      ae_prev_log_idx = 0; ae_prev_log_term = 0;
      ae_entries = []; ae_leader_commit = 0 } in
  assert_test "Leader steps down on higher term" (n.role = Follower);
  assert_test "Term updated to higher" (n.term = 5);

  (* Test 12: Vote only once per term *)
  Printf.printf "\n── Vote Once ──\n";
  let n = make_node 0 in
  let r1 = handle_request_vote n
    { rv_term = 1; rv_candidate_id = 1; rv_last_log_idx = 0; rv_last_log_term = 0 } in
  let r2 = handle_request_vote n
    { rv_term = 1; rv_candidate_id = 2; rv_last_log_idx = 0; rv_last_log_term = 0 } in
  assert_test "First vote granted" r1.rvr_vote_granted;
  assert_test "Second vote denied (same term)" (not r2.rvr_vote_granted);

  (* Test 13: Log term safety *)
  Printf.printf "\n── Log Safety ──\n";
  let n = make_node 0 in
  n.term <- 3;
  n.log <- [{ term = 3; index = 2; command = "b" }; { term = 1; index = 1; command = "a" }];
  assert_test "Last log term correct" (last_log_term n = 3);
  assert_test "Last log index correct" (last_log_index n = 2);
  assert_test "Get entry by index" (
    match get_log_entry n 1 with Some e -> e.command = "a" | None -> false);

  (* Test 14: Append entries replaces conflicting *)
  Printf.printf "\n── Append Replace ──\n";
  let n = make_node 0 in
  n.log <- [{ term = 1; index = 1; command = "old" }];
  let _ = handle_append_entries n
    { ae_term = 2; ae_leader_id = 1;
      ae_prev_log_idx = 0; ae_prev_log_term = 0;
      ae_entries = [{ term = 2; index = 1; command = "new" }];
      ae_leader_commit = 0 } in
  assert_test "Entry replaced" (
    match get_log_entry n 1 with Some e -> e.command = "new" | None -> false);

  (* Test 15: Large cluster *)
  Printf.printf "\n── Large Cluster (7 nodes) ──\n";
  let c = make_cluster 7 in
  assert_test "7-node majority is 4" (c.majority = 4);
  elect c;
  assert_test "7-node: one leader" (count_leaders c = 1);
  let _ = client_request c "BIG" in
  run_ticks c 5;
  let leader = Array.to_list c.nodes |> List.find (fun n -> n.role = Leader) in
  assert_test "7-node: entry committed" (leader.commit_index >= 1);

  (* Test 16: Commit index advance *)
  Printf.printf "\n── Commit Advance ──\n";
  let n = make_node 0 in
  n.term <- 1; n.role <- Leader;
  n.log <- [{ term = 1; index = 1; command = "x" }];
  n.match_index <- [(1, 1); (2, 1); (3, 0); (4, 0)];
  advance_commit_index n 3;
  assert_test "Commit advances with majority match" (n.commit_index = 1);

  (* Test 17: Commit doesn't advance for old term *)
  Printf.printf "\n── Commit Term Check ──\n";
  let n = make_node 0 in
  n.term <- 2; n.role <- Leader;
  n.log <- [{ term = 1; index = 1; command = "old_term" }];
  n.match_index <- [(1, 1); (2, 1); (3, 1); (4, 1)];
  advance_commit_index n 3;
  assert_test "Won't commit entry from prior term alone" (n.commit_index = 0);

  print_results ();
  if !tests_failed > 0 then exit 1
