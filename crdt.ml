(* Conflict-free Replicated Data Types (CRDTs) *)
(* Demonstrates: distributed systems, eventual consistency, lattice theory,
   merge semilattices, commutative/associative/idempotent operations,
   algebraic data types, higher-order functions, modular design *)

(* CRDTs are data structures that can be replicated across multiple nodes
   and updated independently without coordination.  Every replica can
   apply updates locally.  When replicas exchange state, they *merge*
   using a deterministic join operation that satisfies three properties:

   1. Commutative:   merge(A, B) = merge(B, A)
   2. Associative:   merge(merge(A, B), C) = merge(A, merge(B, C))
   3. Idempotent:    merge(A, A) = A

   These three properties guarantee that replicas *always converge* to
   the same state regardless of message ordering, duplication, or delays.
   This is called Strong Eventual Consistency (SEC).

   CRDTs come in two flavors:
   - State-based (CvRDTs): replicas send full state; merge computes join
   - Operation-based (CmRDTs): replicas broadcast operations

   This module implements state-based CRDTs, which are simpler to reason
   about and don't require reliable broadcast.

   Contrast with STM (stm.ml): STM provides *strong consistency* via
   optimistic transactions that abort on conflict.  CRDTs provide
   *eventual consistency* with *no aborts* — every operation succeeds
   locally and convergence is guaranteed mathematically. *)


(* ═══════════════════════════════════════════════════════════════════
   §1  G-Counter (Grow-only Counter)
   ═══════════════════════════════════════════════════════════════════ *)

(* The simplest CRDT.  Each replica maintains its own count.
   The global value is the sum of all replica counts.
   Merge takes the pointwise maximum. *)

module GCounter = struct
  (* Map from replica ID to that replica's count *)
  type t = (string * int) list

  let create () : t = []

  (* Increment the counter for a specific replica *)
  let increment (replica : string) (amount : int) (c : t) : t =
    if amount < 0 then invalid_arg "GCounter: amount must be non-negative";
    let current = try List.assoc replica c with Not_found -> 0 in
    let updated = current + amount in
    (replica, updated) :: (List.filter (fun (k, _) -> k <> replica) c)

  (* Query the global counter value (sum of all replicas) *)
  let value (c : t) : int =
    List.fold_left (fun acc (_, v) -> acc + v) 0 c

  (* Merge two G-Counters: pointwise maximum *)
  let merge (a : t) (b : t) : t =
    let all_keys =
      let ka = List.map fst a and kb = List.map fst b in
      List.sort_uniq String.compare (ka @ kb)
    in
    List.map (fun k ->
      let va = try List.assoc k a with Not_found -> 0 in
      let vb = try List.assoc k b with Not_found -> 0 in
      (k, max va vb)
    ) all_keys

  (* Check if a <= b in the lattice (pointwise <=) *)
  let leq (a : t) (b : t) : bool =
    List.for_all (fun (k, va) ->
      let vb = try List.assoc k b with Not_found -> 0 in
      va <= vb
    ) a
end


(* ═══════════════════════════════════════════════════════════════════
   §2  PN-Counter (Positive-Negative Counter)
   ═══════════════════════════════════════════════════════════════════ *)

(* Supports both increment and decrement by maintaining two G-Counters:
   one for increments (P) and one for decrements (N).
   Value = sum(P) - sum(N).  Merge is applied independently to each. *)

module PNCounter = struct
  type t = {
    p : GCounter.t;  (* positive increments *)
    n : GCounter.t;  (* negative increments / decrements *)
  }

  let create () : t = { p = GCounter.create (); n = GCounter.create () }

  let increment (replica : string) (amount : int) (c : t) : t =
    { c with p = GCounter.increment replica amount c.p }

  let decrement (replica : string) (amount : int) (c : t) : t =
    { c with n = GCounter.increment replica amount c.n }

  let value (c : t) : int =
    GCounter.value c.p - GCounter.value c.n

  let merge (a : t) (b : t) : t =
    { p = GCounter.merge a.p b.p;
      n = GCounter.merge a.n b.n }

  let leq (a : t) (b : t) : bool =
    GCounter.leq a.p b.p && GCounter.leq a.n b.n
end


(* ═══════════════════════════════════════════════════════════════════
   §3  G-Set (Grow-only Set)
   ═══════════════════════════════════════════════════════════════════ *)

(* Elements can only be added, never removed.
   Merge is set union — trivially commutative, associative, idempotent. *)

module GSet = struct
  type t = string list  (* sorted, deduplicated *)

  let create () : t = []

  let add (elem : string) (s : t) : t =
    if List.mem elem s then s
    else List.sort_uniq String.compare (elem :: s)

  let contains (elem : string) (s : t) : bool =
    List.mem elem s

  let elements (s : t) : string list = s

  let size (s : t) : int = List.length s

  let merge (a : t) (b : t) : t =
    List.sort_uniq String.compare (a @ b)

  let leq (a : t) (b : t) : bool =
    List.for_all (fun x -> List.mem x b) a
end


(* ═══════════════════════════════════════════════════════════════════
   §4  OR-Set (Observed-Remove Set)
   ═══════════════════════════════════════════════════════════════════ *)

(* The OR-Set solves the "add-remove" conflict:
   - Each add generates a unique tag (replica + sequence number)
   - Remove only removes the tags *currently observed*
   - On merge, an element is present if any tag survives

   This means concurrent add+remove keeps the element (add wins),
   which is the most intuitive semantic for users. *)

module ORSet = struct
  (* A tag uniquely identifies an add operation *)
  type tag = string * int  (* (replica_id, sequence_number) *)

  (* Each element maps to its set of active tags *)
  type entry = {
    element : string;
    tags    : tag list;
  }

  type t = {
    entries   : entry list;
    sequences : (string * int) list;  (* replica → next sequence number *)
  }

  let create () : t = { entries = []; sequences = [] }

  let _next_seq (replica : string) (s : t) : int * t =
    let current = try List.assoc replica s.sequences with Not_found -> 0 in
    let next = current + 1 in
    let seqs = (replica, next) :: List.filter (fun (k, _) -> k <> replica) s.sequences in
    (next, { s with sequences = seqs })

  let add (replica : string) (elem : string) (s : t) : t =
    let (seq, s') = _next_seq replica s in
    let new_tag = (replica, seq) in
    let found = ref false in
    let entries = List.map (fun e ->
      if e.element = elem then begin
        found := true;
        { e with tags = new_tag :: e.tags }
      end else e
    ) s'.entries in
    let entries =
      if !found then entries
      else { element = elem; tags = [new_tag] } :: entries
    in
    { s' with entries }

  let remove (elem : string) (s : t) : t =
    (* Remove all currently-observed tags for this element *)
    let entries = List.filter (fun e -> e.element <> elem) s.entries in
    { s with entries }

  let contains (elem : string) (s : t) : bool =
    List.exists (fun e -> e.element = elem && e.tags <> []) s.entries

  let elements (s : t) : string list =
    List.filter_map (fun e ->
      if e.tags <> [] then Some e.element else None
    ) s.entries
    |> List.sort_uniq String.compare

  let size (s : t) : int = List.length (elements s)

  let merge (a : t) (b : t) : t =
    (* For each element, the surviving tags are the union of tags from
       both sides, minus tags that were explicitly removed (i.e., tags
       that appear in neither side's entry means they were removed). *)
    let all_elems =
      let ea = List.map (fun e -> e.element) a.entries in
      let eb = List.map (fun e -> e.element) b.entries in
      List.sort_uniq String.compare (ea @ eb)
    in
    let find_tags elem entries =
      match List.find_opt (fun e -> e.element = elem) entries with
      | Some e -> e.tags
      | None -> []
    in
    let tag_eq (r1, s1) (r2, s2) = r1 = r2 && s1 = s2 in
    let tag_mem t lst = List.exists (tag_eq t) lst in
    let tag_union ta tb =
      let from_b = List.filter (fun t -> not (tag_mem t ta)) tb in
      ta @ from_b
    in
    let entries = List.filter_map (fun elem ->
      let ta = find_tags elem a.entries in
      let tb = find_tags elem b.entries in
      (* A tag survives if it's in the union and wasn't removed by either side.
         Since we only track *active* tags, the union of active tags is correct:
         a tag absent from a.entries was either never added or removed by a. *)
      let merged_tags = tag_union ta tb in
      if merged_tags = [] then None
      else Some { element = elem; tags = merged_tags }
    ) all_elems in
    let merge_seqs sa sb =
      let all_reps =
        let ra = List.map fst sa and rb = List.map fst sb in
        List.sort_uniq String.compare (ra @ rb)
      in
      List.map (fun r ->
        let va = try List.assoc r sa with Not_found -> 0 in
        let vb = try List.assoc r sb with Not_found -> 0 in
        (r, max va vb)
      ) all_reps
    in
    { entries; sequences = merge_seqs a.sequences b.sequences }

  let leq (a : t) (b : t) : bool =
    List.for_all (fun ea ->
      match List.find_opt (fun eb -> eb.element = ea.element) b.entries with
      | None -> ea.tags = []
      | Some eb ->
        let tag_eq (r1, s1) (r2, s2) = r1 = r2 && s1 = s2 in
        List.for_all (fun t -> List.exists (tag_eq t) eb.tags) ea.tags
    ) a.entries
end


(* ═══════════════════════════════════════════════════════════════════
   §5  LWW-Register (Last-Writer-Wins Register)
   ═══════════════════════════════════════════════════════════════════ *)

(* A register holding a single value.  Concurrent writes are resolved
   by timestamp — the most recent write wins.  Simple but effective
   when a total order on timestamps exists. *)

module LWWRegister = struct
  type t = {
    value     : string;
    timestamp : float;
    replica   : string;  (* tiebreaker when timestamps match *)
  }

  let create (value : string) (timestamp : float) (replica : string) : t =
    { value; timestamp; replica }

  let write (value : string) (timestamp : float) (replica : string) (r : t) : t =
    if timestamp > r.timestamp then { value; timestamp; replica }
    else if timestamp = r.timestamp && replica > r.replica then
      { value; timestamp; replica }
    else r

  let read (r : t) : string = r.value

  let merge (a : t) (b : t) : t =
    if a.timestamp > b.timestamp then a
    else if b.timestamp > a.timestamp then b
    else if a.replica >= b.replica then a  (* tiebreaker: lexicographic *)
    else b

  let leq (a : t) (b : t) : bool =
    a.timestamp <= b.timestamp
end


(* ═══════════════════════════════════════════════════════════════════
   §6  MV-Register (Multi-Value Register)
   ═══════════════════════════════════════════════════════════════════ *)

(* Unlike LWW-Register, the MV-Register preserves ALL concurrent
   writes, letting the application resolve conflicts.  This is how
   Amazon's Dynamo handles conflicting writes ("siblings").

   Uses vector clocks to detect causality vs concurrency. *)

module MVRegister = struct
  (* Vector clock: replica → logical timestamp *)
  type vclock = (string * int) list

  type versioned_value = {
    value : string;
    clock : vclock;
  }

  type t = versioned_value list  (* list of concurrent values *)

  let _vc_get (replica : string) (vc : vclock) : int =
    try List.assoc replica vc with Not_found -> 0

  let _vc_increment (replica : string) (vc : vclock) : vclock =
    let current = _vc_get replica vc in
    (replica, current + 1) :: List.filter (fun (k, _) -> k <> replica) vc

  (* vc1 <= vc2: every component of vc1 is <= the corresponding in vc2 *)
  let _vc_leq (vc1 : vclock) (vc2 : vclock) : bool =
    let all_keys =
      List.sort_uniq String.compare
        (List.map fst vc1 @ List.map fst vc2)
    in
    List.for_all (fun k ->
      _vc_get k vc1 <= _vc_get k vc2
    ) all_keys

  (* Merge two vector clocks: pointwise maximum *)
  let _vc_merge (vc1 : vclock) (vc2 : vclock) : vclock =
    let all_keys =
      List.sort_uniq String.compare
        (List.map fst vc1 @ List.map fst vc2)
    in
    List.map (fun k ->
      (k, max (_vc_get k vc1) (_vc_get k vc2))
    ) all_keys

  let create (value : string) (replica : string) : t =
    [{ value; clock = [(replica, 1)] }]

  let write (value : string) (replica : string) (r : t) : t =
    (* Merge all existing clocks, then increment for this replica *)
    let merged_clock = List.fold_left (fun acc vv ->
      _vc_merge acc vv.clock
    ) [] r in
    let new_clock = _vc_increment replica merged_clock in
    [{ value; clock = new_clock }]

  let read (r : t) : string list =
    List.map (fun vv -> vv.value) r

  let merge (a : t) (b : t) : t =
    (* Keep values that are not dominated by any value on the other side.
       A value v1 is dominated by v2 if v1.clock <= v2.clock. *)
    let not_dominated_by vv others =
      not (List.exists (fun other ->
        _vc_leq vv.clock other.clock && vv.clock <> other.clock
      ) others)
    in
    let from_a = List.filter (fun vv -> not_dominated_by vv b) a in
    let from_b = List.filter (fun vv -> not_dominated_by vv a) b in
    (* Deduplicate by value+clock *)
    let all = from_a @ from_b in
    let rec dedup = function
      | [] -> []
      | x :: rest ->
        if List.exists (fun y ->
          y.value = x.value && _vc_leq x.clock y.clock && _vc_leq y.clock x.clock
        ) rest then dedup rest
        else x :: dedup rest
    in
    dedup all
end


(* ═══════════════════════════════════════════════════════════════════
   §7  Convergence Testing & Demonstration
   ═══════════════════════════════════════════════════════════════════ *)

(* Verify the CRDT laws: commutativity, associativity, idempotency.
   Then demonstrate realistic multi-replica scenarios. *)

let () =
  let passed = ref 0 in
  let failed = ref 0 in
  let test name f =
    try
      f ();
      incr passed;
      Printf.printf "  ✓ %s\n" name
    with ex ->
      incr failed;
      Printf.printf "  ✗ %s: %s\n" name (Printexc.to_string ex)
  in
  let assert_eq a b msg =
    if a <> b then failwith (Printf.sprintf "%s: expected %s, got %s"
      msg (string_of_int a) (string_of_int b))
  in
  let assert_true b msg = if not b then failwith msg in
  let assert_str_eq a b msg =
    if a <> b then failwith (Printf.sprintf "%s: expected '%s', got '%s'" msg a b)
  in

  Printf.printf "\n══════════════════════════════════════════\n";
  Printf.printf "  CRDTs — Conflict-free Replicated Data Types\n";
  Printf.printf "══════════════════════════════════════════\n\n";

  (* ── G-Counter Tests ── *)
  Printf.printf "§1 G-Counter\n";

  test "increment and query" (fun () ->
    let c = GCounter.create ()
      |> GCounter.increment "A" 3
      |> GCounter.increment "B" 5
    in
    assert_eq (GCounter.value c) 8 "value"
  );

  test "merge takes pointwise max" (fun () ->
    let a = GCounter.create ()
      |> GCounter.increment "A" 10
      |> GCounter.increment "B" 3
    in
    let b = GCounter.create ()
      |> GCounter.increment "A" 5
      |> GCounter.increment "B" 7
    in
    let m = GCounter.merge a b in
    assert_eq (GCounter.value m) 17 "merge value"  (* max(10,5) + max(3,7) *)
  );

  test "commutativity" (fun () ->
    let a = GCounter.create () |> GCounter.increment "X" 4 in
    let b = GCounter.create () |> GCounter.increment "Y" 6 in
    let ab = GCounter.merge a b in
    let ba = GCounter.merge b a in
    assert_eq (GCounter.value ab) (GCounter.value ba) "commutative"
  );

  test "idempotency" (fun () ->
    let a = GCounter.create () |> GCounter.increment "A" 5 in
    let aa = GCounter.merge a a in
    assert_eq (GCounter.value a) (GCounter.value aa) "idempotent"
  );

  test "lattice ordering" (fun () ->
    let a = GCounter.create () |> GCounter.increment "A" 3 in
    let b = a |> GCounter.increment "A" 2 in
    assert_true (GCounter.leq a b) "a <= b";
    assert_true (not (GCounter.leq b a)) "not b <= a"
  );

  test "rejects negative amount" (fun () ->
    let raised = try
      ignore (GCounter.increment "A" (-1) (GCounter.create ()));
      false
    with Invalid_argument _ -> true
    in
    assert_true raised "should reject negative"
  );

  (* ── PN-Counter Tests ── *)
  Printf.printf "\n§2 PN-Counter\n";

  test "increment and decrement" (fun () ->
    let c = PNCounter.create ()
      |> PNCounter.increment "A" 10
      |> PNCounter.decrement "A" 3
    in
    assert_eq (PNCounter.value c) 7 "value"
  );

  test "can go negative" (fun () ->
    let c = PNCounter.create ()
      |> PNCounter.increment "A" 2
      |> PNCounter.decrement "A" 5
    in
    assert_eq (PNCounter.value c) (-3) "negative value"
  );

  test "merge preserves both increments and decrements" (fun () ->
    let a = PNCounter.create ()
      |> PNCounter.increment "A" 10
      |> PNCounter.decrement "A" 2
    in
    let b = PNCounter.create ()
      |> PNCounter.increment "B" 5
      |> PNCounter.decrement "B" 1
    in
    let m = PNCounter.merge a b in
    assert_eq (PNCounter.value m) 12 "merged value"  (* (10+5) - (2+1) *)
  );

  test "concurrent increments and decrements" (fun () ->
    let a = PNCounter.create ()
      |> PNCounter.increment "A" 10
      |> PNCounter.decrement "A" 3
    in
    let b = PNCounter.create ()
      |> PNCounter.increment "A" 7
      |> PNCounter.decrement "A" 5
    in
    let m = PNCounter.merge a b in
    (* P: max(10,7)=10, N: max(3,5)=5 → value=5 *)
    assert_eq (PNCounter.value m) 5 "concurrent value"
  );

  test "commutativity" (fun () ->
    let a = PNCounter.create () |> PNCounter.increment "A" 4 in
    let b = PNCounter.create () |> PNCounter.decrement "B" 2 in
    assert_eq (PNCounter.value (PNCounter.merge a b))
              (PNCounter.value (PNCounter.merge b a)) "commutative"
  );

  (* ── G-Set Tests ── *)
  Printf.printf "\n§3 G-Set\n";

  test "add and query" (fun () ->
    let s = GSet.create ()
      |> GSet.add "apple"
      |> GSet.add "banana"
    in
    assert_true (GSet.contains "apple" s) "contains apple";
    assert_true (not (GSet.contains "cherry" s)) "not contains cherry";
    assert_eq (GSet.size s) 2 "size"
  );

  test "add is idempotent" (fun () ->
    let s = GSet.create ()
      |> GSet.add "x"
      |> GSet.add "x"
      |> GSet.add "x"
    in
    assert_eq (GSet.size s) 1 "duplicate add"
  );

  test "merge is union" (fun () ->
    let a = GSet.create () |> GSet.add "a" |> GSet.add "b" in
    let b = GSet.create () |> GSet.add "b" |> GSet.add "c" in
    let m = GSet.merge a b in
    assert_eq (GSet.size m) 3 "merged size";
    assert_true (GSet.contains "a" m) "has a";
    assert_true (GSet.contains "c" m) "has c"
  );

  test "lattice ordering" (fun () ->
    let a = GSet.create () |> GSet.add "x" in
    let b = a |> GSet.add "y" in
    assert_true (GSet.leq a b) "subset";
    assert_true (not (GSet.leq b a)) "not superset"
  );

  (* ── OR-Set Tests ── *)
  Printf.printf "\n§4 OR-Set (Observed-Remove)\n";

  test "add and remove" (fun () ->
    let s = ORSet.create ()
      |> ORSet.add "A" "x"
      |> ORSet.add "A" "y"
      |> ORSet.remove "x"
    in
    assert_true (not (ORSet.contains "x" s)) "x removed";
    assert_true (ORSet.contains "y" s) "y present"
  );

  test "concurrent add wins over remove" (fun () ->
    (* Replica A adds "x", replica B removes "x" concurrently.
       When merged, the add from A should win because B only
       removed the tags it had observed. *)
    let base = ORSet.create () |> ORSet.add "A" "x" in
    (* B sees x and removes it *)
    let b = ORSet.remove "x" base in
    (* A concurrently adds x again (new tag) *)
    let a = ORSet.add "A" "x" base in
    let merged = ORSet.merge a b in
    assert_true (ORSet.contains "x" merged) "add wins"
  );

  test "both-remove converges to empty" (fun () ->
    let base = ORSet.create () |> ORSet.add "A" "x" in
    let a = ORSet.remove "x" base in
    let b = ORSet.remove "x" base in
    let merged = ORSet.merge a b in
    assert_true (not (ORSet.contains "x" merged)) "both removed"
  );

  test "multi-replica convergence" (fun () ->
    let s1 = ORSet.create ()
      |> ORSet.add "A" "x"
      |> ORSet.add "A" "y"
    in
    let s2 = ORSet.create ()
      |> ORSet.add "B" "y"
      |> ORSet.add "B" "z"
    in
    let m = ORSet.merge s1 s2 in
    assert_eq (ORSet.size m) 3 "size after merge"
  );

  test "commutativity" (fun () ->
    let a = ORSet.create () |> ORSet.add "A" "p" in
    let b = ORSet.create () |> ORSet.add "B" "q" in
    let ab = ORSet.elements (ORSet.merge a b) in
    let ba = ORSet.elements (ORSet.merge b a) in
    assert_true (ab = ba) "commutative"
  );

  test "idempotency" (fun () ->
    let a = ORSet.create () |> ORSet.add "A" "x" |> ORSet.add "A" "y" in
    let aa = ORSet.merge a a in
    let elems_a = ORSet.elements a in
    let elems_aa = ORSet.elements aa in
    assert_true (elems_a = elems_aa) "idempotent"
  );

  (* ── LWW-Register Tests ── *)
  Printf.printf "\n§5 LWW-Register\n";

  test "latest write wins" (fun () ->
    let r = LWWRegister.create "old" 1.0 "A"
      |> LWWRegister.write "new" 2.0 "A"
    in
    assert_str_eq (LWWRegister.read r) "new" "latest write"
  );

  test "earlier write ignored" (fun () ->
    let r = LWWRegister.create "current" 5.0 "A"
      |> LWWRegister.write "stale" 3.0 "B"
    in
    assert_str_eq (LWWRegister.read r) "current" "stale ignored"
  );

  test "merge picks latest" (fun () ->
    let a = LWWRegister.create "val_a" 10.0 "A" in
    let b = LWWRegister.create "val_b" 20.0 "B" in
    let m = LWWRegister.merge a b in
    assert_str_eq (LWWRegister.read m) "val_b" "merge picks B"
  );

  test "tiebreaker on equal timestamp" (fun () ->
    let a = LWWRegister.create "val_a" 5.0 "A" in
    let b = LWWRegister.create "val_b" 5.0 "B" in
    let m = LWWRegister.merge a b in
    (* B > A lexicographically, so B wins *)
    assert_str_eq (LWWRegister.read m) "val_b" "tiebreaker"
  );

  test "commutativity" (fun () ->
    let a = LWWRegister.create "x" 1.0 "A" in
    let b = LWWRegister.create "y" 2.0 "B" in
    assert_str_eq (LWWRegister.read (LWWRegister.merge a b))
                  (LWWRegister.read (LWWRegister.merge b a))
                  "commutative"
  );

  (* ── MV-Register Tests ── *)
  Printf.printf "\n§6 MV-Register\n";

  test "single write" (fun () ->
    let r = MVRegister.create "hello" "A" in
    let vals = MVRegister.read r in
    assert_eq (List.length vals) 1 "one value";
    assert_str_eq (List.hd vals) "hello" "value"
  );

  test "sequential writes resolve to latest" (fun () ->
    let r = MVRegister.create "v1" "A"
      |> MVRegister.write "v2" "A"
      |> MVRegister.write "v3" "A"
    in
    let vals = MVRegister.read r in
    assert_eq (List.length vals) 1 "one value";
    assert_str_eq (List.hd vals) "v3" "latest"
  );

  test "concurrent writes produce siblings" (fun () ->
    (* A and B both write independently *)
    let base = MVRegister.create "origin" "A" in
    let a = MVRegister.write "from_A" "A" base in
    let b = MVRegister.write "from_B" "B" base in
    let m = MVRegister.merge a b in
    let vals = List.sort String.compare (MVRegister.read m) in
    assert_eq (List.length vals) 2 "two siblings";
    assert_str_eq (List.nth vals 0) "from_A" "sibling A";
    assert_str_eq (List.nth vals 1) "from_B" "sibling B"
  );

  test "resolving siblings" (fun () ->
    let base = MVRegister.create "origin" "A" in
    let a = MVRegister.write "from_A" "A" base in
    let b = MVRegister.write "from_B" "B" base in
    let m = MVRegister.merge a b in
    (* Application resolves by writing a new value *)
    let resolved = MVRegister.write "resolved" "A" m in
    let vals = MVRegister.read resolved in
    assert_eq (List.length vals) 1 "resolved to one";
    assert_str_eq (List.hd vals) "resolved" "resolved value"
  );

  test "commutativity" (fun () ->
    let a = MVRegister.create "x" "A" in
    let b = MVRegister.create "y" "B" in
    let ab = List.sort String.compare (MVRegister.read (MVRegister.merge a b)) in
    let ba = List.sort String.compare (MVRegister.read (MVRegister.merge b a)) in
    assert_true (ab = ba) "commutative"
  );

  (* ── Multi-replica scenario ── *)
  Printf.printf "\n§7 Multi-Replica Scenario\n";

  test "shopping cart with OR-Set (3 replicas)" (fun () ->
    (* Three replicas of a shopping cart *)
    let cart_a = ORSet.create ()
      |> ORSet.add "phone" "milk"
      |> ORSet.add "phone" "eggs"
      |> ORSet.add "phone" "bread"
    in
    let cart_b = ORSet.create ()
      |> ORSet.add "tablet" "milk"
      |> ORSet.add "tablet" "butter"
    in
    let cart_c = ORSet.create ()
      |> ORSet.add "laptop" "eggs"
      |> ORSet.add "laptop" "cheese"
    in
    (* Phone removes milk before syncing *)
    let cart_a' = ORSet.remove "milk" cart_a in
    (* Merge all three *)
    let merged = ORSet.merge (ORSet.merge cart_a' cart_b) cart_c in
    (* milk was removed by phone but concurrently added by tablet → present *)
    assert_true (ORSet.contains "milk" merged) "milk: add wins";
    assert_true (ORSet.contains "eggs" merged) "eggs present";
    assert_true (ORSet.contains "bread" merged) "bread present";
    assert_true (ORSet.contains "butter" merged) "butter present";
    assert_true (ORSet.contains "cheese" merged) "cheese present";
    assert_eq (ORSet.size merged) 5 "total items"
  );

  test "collaborative counter (3 replicas)" (fun () ->
    (* Three servers tracking page views independently *)
    let server_a = PNCounter.create ()
      |> PNCounter.increment "us-east" 1000
      |> PNCounter.decrement "us-east" 50  (* corrections *)
    in
    let server_b = PNCounter.create ()
      |> PNCounter.increment "us-west" 800
    in
    let server_c = PNCounter.create ()
      |> PNCounter.increment "eu" 1200
      |> PNCounter.decrement "eu" 100
    in
    let total = PNCounter.merge (PNCounter.merge server_a server_b) server_c in
    assert_eq (PNCounter.value total) 2850 "global count"
  );

  test "convergence regardless of merge order" (fun () ->
    let a = GCounter.create () |> GCounter.increment "A" 5 in
    let b = GCounter.create () |> GCounter.increment "B" 3 in
    let c = GCounter.create () |> GCounter.increment "C" 7 in
    let abc = GCounter.merge (GCounter.merge a b) c in
    let bca = GCounter.merge (GCounter.merge b c) a in
    let cab = GCounter.merge (GCounter.merge c a) b in
    let cba = GCounter.merge c (GCounter.merge b a) in
    assert_eq (GCounter.value abc) 15 "abc";
    assert_eq (GCounter.value bca) 15 "bca";
    assert_eq (GCounter.value cab) 15 "cab";
    assert_eq (GCounter.value cba) 15 "cba"
  );

  test "LWW-Register multi-replica sync" (fun () ->
    let r1 = LWWRegister.create "init" 0.0 "A" in
    let r2 = LWWRegister.write "update_1" 1.0 "A" r1 in
    let r3 = LWWRegister.write "update_2" 2.0 "B" r1 in  (* concurrent *)
    let m12 = LWWRegister.merge r2 r3 in
    let m21 = LWWRegister.merge r3 r2 in
    assert_str_eq (LWWRegister.read m12) (LWWRegister.read m21) "convergent"
  );

  (* ── Vector Clock Tests ── *)
  Printf.printf "\n§8 Vector Clock Properties\n";

  test "causal ordering detected" (fun () ->
    let r1 = MVRegister.create "v1" "A" in
    let r2 = MVRegister.write "v2" "A" r1 in
    (* r2 causally follows r1, so merging keeps only r2 *)
    let m = MVRegister.merge r1 r2 in
    let vals = MVRegister.read m in
    assert_eq (List.length vals) 1 "causal: one value";
    assert_str_eq (List.hd vals) "v2" "causal: latest"
  );

  test "three-way concurrent produces three siblings" (fun () ->
    let base = MVRegister.create "origin" "seed" in
    let a = MVRegister.write "A_val" "A" base in
    let b = MVRegister.write "B_val" "B" base in
    let c = MVRegister.write "C_val" "C" base in
    let m = MVRegister.merge (MVRegister.merge a b) c in
    let vals = List.sort String.compare (MVRegister.read m) in
    assert_eq (List.length vals) 3 "three siblings";
    assert_str_eq (List.nth vals 0) "A_val" "A";
    assert_str_eq (List.nth vals 1) "B_val" "B";
    assert_str_eq (List.nth vals 2) "C_val" "C"
  );

  test "resolve then diverge again" (fun () ->
    let base = MVRegister.create "origin" "seed" in
    let a = MVRegister.write "A" "nodeA" base in
    let b = MVRegister.write "B" "nodeB" base in
    (* Merge → siblings *)
    let m = MVRegister.merge a b in
    assert_eq (List.length (MVRegister.read m)) 2 "2 siblings";
    (* Resolve *)
    let resolved = MVRegister.write "resolved" "nodeA" m in
    assert_eq (List.length (MVRegister.read resolved)) 1 "resolved";
    (* Diverge again *)
    let d1 = MVRegister.write "split1" "nodeA" resolved in
    let d2 = MVRegister.write "split2" "nodeB" resolved in
    let m2 = MVRegister.merge d1 d2 in
    assert_eq (List.length (MVRegister.read m2)) 2 "diverged again"
  );

  (* ── Summary ── *)
  Printf.printf "\n══════════════════════════════════════════\n";
  Printf.printf "  Results: %d passed, %d failed\n" !passed !failed;
  Printf.printf "══════════════════════════════════════════\n";
  if !failed > 0 then exit 1
