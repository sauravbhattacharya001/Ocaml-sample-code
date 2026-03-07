(* Software Transactional Memory (STM) *)
(* Demonstrates: mutable state management, transaction isolation, composable
   concurrency, optimistic concurrency control, conflict detection, retry/orElse,
   monadic composition, algebraic data types, higher-order functions *)

(* Software Transactional Memory (STM) is a concurrency control mechanism
   that replaces locks with *transactions*.  Each transaction sees a
   consistent snapshot of shared state.  When it tries to commit, the
   runtime checks whether any variable it read has been modified by
   another transaction.  If so, it rolls back and retries automatically.

   Key advantages over locks:
   - Composable: two STM actions can be combined into one atomic block
   - Deadlock-free: no ordering discipline required
   - Optimistic: reads are cheap, conflicts are detected at commit time

   This is a *single-threaded simulation* that faithfully models the
   semantics of STM (snapshots, validation, retry, orElse) without
   requiring OCaml's threads or multicore runtime.  The focus is on
   understanding the *algorithm*, not the OS plumbing. *)

(* ═══════════════════════════════════════════════════════════════════
   §1  Transactional Variables (TVars)
   ═══════════════════════════════════════════════════════════════════ *)

(* A TVar holds a versioned value.  Every write bumps the version,
   which is how the commit protocol detects conflicts. *)

type 'a tvar = {
  mutable value   : 'a;
  mutable version : int;
  id              : int;
}

let next_tvar_id = ref 0

let new_tvar (v : 'a) : 'a tvar =
  let id = !next_tvar_id in
  incr next_tvar_id;
  { value = v; version = 0; id }

let read_tvar_raw (tv : 'a tvar) : 'a = tv.value

let write_tvar_raw (tv : 'a tvar) (v : 'a) : unit =
  tv.value <- v;
  tv.version <- tv.version + 1


(* ═══════════════════════════════════════════════════════════════════
   §2  Transaction Log
   ═══════════════════════════════════════════════════════════════════ *)

(* During a transaction we record every read and write in a log.
   Reads record the version at the time of reading.  Writes are
   buffered and only applied on successful commit.

   We use an existential wrapper so that the log can hold entries
   for TVars of different types in one list. *)

type read_entry  = Read : 'a tvar * int -> read_entry
type write_entry = Write : 'a tvar * 'a -> write_entry

type tx_log = {
  mutable reads  : read_entry list;
  mutable writes : write_entry list;
}

let empty_log () : tx_log = { reads = []; writes = [] }


(* ═══════════════════════════════════════════════════════════════════
   §3  STM Monad
   ═══════════════════════════════════════════════════════════════════ *)

(* An STM action is a function from a transaction log to a result.
   This is essentially the State monad over the tx_log.

   Three possible outcomes:
   - Success: produced a value (may or may not commit)
   - Retry:   the transaction wants to block until some TVar changes
   - OrElse:  used internally by the choice combinator                *)

type 'a stm_result =
  | Success of 'a
  | Retry

type 'a stm = tx_log -> 'a stm_result

(* Monadic return — wraps a pure value in a transaction *)
let stm_return (x : 'a) : 'a stm =
  fun _log -> Success x

(* Monadic bind — sequence two STM actions *)
let stm_bind (m : 'a stm) (f : 'a -> 'b stm) : 'b stm =
  fun log ->
    match m log with
    | Success a -> f a log
    | Retry     -> Retry

(* Map — apply a pure function inside a transaction *)
let stm_map (f : 'a -> 'b) (m : 'a stm) : 'b stm =
  stm_bind m (fun x -> stm_return (f x))

(* Sequence — run two STM actions, keep the second result *)
let stm_seq (m1 : 'a stm) (m2 : 'b stm) : 'b stm =
  stm_bind m1 (fun _ -> m2)

(* Read a TVar inside a transaction.  Records the read in the log
   so the commit protocol can validate it later.

   If this TVar was already written in this transaction, we return
   the buffered value (read-your-writes consistency). *)
let read_tvar (tv : 'a tvar) : 'a stm =
  fun log ->
    (* Check if we already wrote to this TVar in this transaction *)
    let rec find_write = function
      | [] -> None
      | Write (tv', v) :: rest ->
        if tv'.id = tv.id then
          (* Obj.magic is safe here because the IDs match, so the
             types are the same.  This is the standard GADT existential
             pattern in OCaml. *)
          Some (Obj.magic v : 'a)
        else
          find_write rest
    in
    match find_write log.writes with
    | Some v -> Success v
    | None ->
      let v = tv.value in
      log.reads <- Read (tv, tv.version) :: log.reads;
      Success v

(* Write to a TVar inside a transaction.  The write is buffered
   in the log and only applied on successful commit. *)
let write_tvar (tv : 'a tvar) (v : 'a) : unit stm =
  fun log ->
    (* Replace any previous write to this TVar *)
    let writes' = List.filter
      (fun (Write (tv', _)) -> tv'.id <> tv.id)
      log.writes
    in
    log.writes <- Write (tv, v) :: writes';
    Success ()

(* Modify a TVar: read then write *)
let modify_tvar (tv : 'a tvar) (f : 'a -> 'a) : unit stm =
  stm_bind (read_tvar tv) (fun v -> write_tvar tv (f v))


(* ═══════════════════════════════════════════════════════════════════
   §4  Retry and OrElse
   ═══════════════════════════════════════════════════════════════════ *)

(* retry signals that the current transaction cannot proceed until
   some TVar it has read changes.  In a real runtime this would
   block the thread; here we just return the Retry result. *)
let stm_retry : 'a stm = fun _log -> Retry

(* orElse composes two STM actions with a fallback.  If the first
   retries, the second is tried with a fresh log.  If both retry,
   the combined action retries.

   This is the key to *composable* blocking: you can say
   "try to withdraw from account A, or else try account B". *)
let stm_or_else (m1 : 'a stm) (m2 : 'a stm) : 'a stm =
  fun log ->
    (* Save the current log state *)
    let saved_reads  = log.reads in
    let saved_writes = log.writes in
    match m1 log with
    | Success v -> Success v
    | Retry ->
      (* Restore log and try alternative *)
      log.reads  <- saved_reads;
      log.writes <- saved_writes;
      m2 log

(* Guard: retry unless a condition holds *)
let stm_guard (cond : bool) : unit stm =
  if cond then stm_return () else stm_retry

(* Check: evaluate a predicate on a TVar, retry if false *)
let stm_check (tv : 'a tvar) (pred : 'a -> bool) : unit stm =
  stm_bind (read_tvar tv) (fun v -> stm_guard (pred v))


(* ═══════════════════════════════════════════════════════════════════
   §5  Commit Protocol
   ═══════════════════════════════════════════════════════════════════ *)

(* The commit protocol validates that every TVar we read still has
   the same version.  If so, we apply all buffered writes atomically.
   If not, the transaction is invalid and must be retried.

   This is *optimistic concurrency control* — we optimistically
   assume no conflicts and check at the end, rather than locking
   upfront.  *)

type commit_result =
  | Committed
  | Conflict
  | Blocked   (* retry was requested *)

let validate_reads (log : tx_log) : bool =
  List.for_all
    (fun (Read (tv, ver)) -> tv.version = ver)
    log.reads

let apply_writes (log : tx_log) : unit =
  List.iter
    (fun (Write (tv, v)) ->
       tv.value <- Obj.magic v;
       tv.version <- tv.version + 1)
    log.writes

let commit (log : tx_log) : commit_result =
  if validate_reads log then begin
    apply_writes log;
    Committed
  end else
    Conflict


(* ═══════════════════════════════════════════════════════════════════
   §6  Atomic Execution
   ═══════════════════════════════════════════════════════════════════ *)

(* atomically runs an STM action, retrying on conflicts.
   In a real system, retries would back off or wait for notifications.
   Here we retry immediately with a bounded retry count to prevent
   infinite loops in the single-threaded simulation. *)

type 'a atomic_result =
  | Value of 'a
  | Retried           (* transaction requested retry/block *)
  | ConflictAborted   (* too many conflicts *)

let max_retries = 1000

let atomically (action : 'a stm) : 'a atomic_result =
  let rec attempt n =
    if n > max_retries then ConflictAborted
    else begin
      let log = empty_log () in
      match action log with
      | Retry   -> Retried
      | Success v ->
        match commit log with
        | Committed -> Value v
        | Conflict  -> attempt (n + 1)
        | Blocked   -> Retried
    end
  in
  attempt 0

(* Convenience: atomically or raise *)
exception Stm_retry
exception Stm_conflict

let atomically_exn (action : 'a stm) : 'a =
  match atomically action with
  | Value v        -> v
  | Retried        -> raise Stm_retry
  | ConflictAborted -> raise Stm_conflict


(* ═══════════════════════════════════════════════════════════════════
   §7  Composable Data Structures
   ═══════════════════════════════════════════════════════════════════ *)

(* The power of STM: we can build lock-free data structures that
   compose.  Transfer between two accounts is just read + write on
   two TVars — the STM runtime handles atomicity. *)

(* -- TVar-backed counter -- *)

let new_counter (init : int) = new_tvar init

let increment (c : int tvar) : unit stm =
  modify_tvar c (fun n -> n + 1)

let decrement (c : int tvar) : unit stm =
  modify_tvar c (fun n -> n - 1)

let get_counter (c : int tvar) : int stm = read_tvar c

(* -- TVar-backed bounded channel -- *)

type 'a channel = {
  buffer   : 'a list tvar;
  capacity : int;
}

let new_channel (cap : int) : 'a channel =
  { buffer = new_tvar []; capacity = max 1 cap }

(* Send: add to channel, retry if full *)
let send (ch : 'a channel) (v : 'a) : unit stm =
  stm_bind (read_tvar ch.buffer) (fun buf ->
    if List.length buf >= ch.capacity then
      stm_retry
    else
      write_tvar ch.buffer (buf @ [v]))

(* Receive: take from channel, retry if empty *)
let receive (ch : 'a channel) : 'a stm =
  stm_bind (read_tvar ch.buffer) (fun buf ->
    match buf with
    | []      -> stm_retry
    | x :: xs -> stm_seq (write_tvar ch.buffer xs) (stm_return x))

(* Try receive: non-blocking variant *)
let try_receive (ch : 'a channel) : 'a option stm =
  stm_or_else
    (stm_map (fun v -> Some v) (receive ch))
    (stm_return None)

(* -- TVar-backed mutable map (association list) -- *)

type ('k, 'v) tmap = ('k * 'v) list tvar

let new_tmap () : ('k, 'v) tmap = new_tvar []

let tmap_get (m : ('k, 'v) tmap) (k : 'k) : 'v option stm =
  stm_map (fun pairs -> List.assoc_opt k pairs) (read_tvar m)

let tmap_put (m : ('k, 'v) tmap) (k : 'k) (v : 'v) : unit stm =
  stm_bind (read_tvar m) (fun pairs ->
    let pairs' = (k, v) :: List.filter (fun (k', _) -> k' <> k) pairs in
    write_tvar m pairs')

let tmap_delete (m : ('k, 'v) tmap) (k : 'k) : unit stm =
  modify_tvar m (fun pairs -> List.filter (fun (k', _) -> k' <> k) pairs)

let tmap_size (m : ('k, 'v) tmap) : int stm =
  stm_map List.length (read_tvar m)

(* -- Bank account (classic STM example) -- *)

type account = {
  name    : string;
  balance : int tvar;
}

let new_account (name : string) (initial : int) : account =
  { name; balance = new_tvar initial }

let deposit (acc : account) (amount : int) : unit stm =
  stm_bind (read_tvar acc.balance) (fun bal ->
    write_tvar acc.balance (bal + amount))

let withdraw (acc : account) (amount : int) : unit stm =
  stm_bind (read_tvar acc.balance) (fun bal ->
    if bal >= amount then
      write_tvar acc.balance (bal - amount)
    else
      stm_retry)

(* Transfer: atomic move between accounts.  This is the canonical
   STM example — it's two operations that must happen together.
   With locks you'd need to worry about ordering; with STM it just works. *)
let transfer (from_acc : account) (to_acc : account) (amount : int) : unit stm =
  stm_bind (withdraw from_acc amount) (fun () ->
    deposit to_acc amount)

let get_balance (acc : account) : int stm = read_tvar acc.balance

(* Withdraw from either account (whichever has funds) *)
let withdraw_from_either (a1 : account) (a2 : account) (amount : int) : string stm =
  stm_or_else
    (stm_seq (withdraw a1 amount) (stm_return a1.name))
    (stm_seq (withdraw a2 amount) (stm_return a2.name))


(* ═══════════════════════════════════════════════════════════════════
   §8  Transaction Statistics
   ═══════════════════════════════════════════════════════════════════ *)

(* Track how transactions behave — useful for understanding
   contention and retry patterns. *)

type stm_stats = {
  mutable commits   : int;
  mutable conflicts : int;
  mutable retries   : int;
}

let global_stats = { commits = 0; conflicts = 0; retries = 0 }

let reset_stats () =
  global_stats.commits   <- 0;
  global_stats.conflicts <- 0;
  global_stats.retries   <- 0

let atomically_tracked (action : 'a stm) : 'a atomic_result =
  let rec attempt n =
    if n > max_retries then begin
      global_stats.conflicts <- global_stats.conflicts + 1;
      ConflictAborted
    end else begin
      let log = empty_log () in
      match action log with
      | Retry ->
        global_stats.retries <- global_stats.retries + 1;
        Retried
      | Success v ->
        match commit log with
        | Committed ->
          global_stats.commits <- global_stats.commits + 1;
          Value v
        | Conflict ->
          global_stats.conflicts <- global_stats.conflicts + 1;
          attempt (n + 1)
        | Blocked ->
          global_stats.retries <- global_stats.retries + 1;
          Retried
    end
  in
  attempt 0

let get_stats () = (global_stats.commits, global_stats.conflicts, global_stats.retries)


(* ═══════════════════════════════════════════════════════════════════
   §9  Conflict Simulation
   ═══════════════════════════════════════════════════════════════════ *)

(* In a single-threaded model we can't have *real* concurrent
   conflicts, but we can simulate them by interleaving transaction
   steps manually.  This demonstrates what would happen if two
   transactions ran concurrently. *)

(* Simulate a conflict: snapshot, modify externally, then try to commit *)
let simulate_conflict (tv : 'a tvar) (tx_value : 'a) (external_value : 'a) : commit_result =
  let log = empty_log () in
  (* Transaction reads the TVar *)
  let _ = (read_tvar tv) log in
  (* Transaction writes a new value *)
  let _ = (write_tvar tv tx_value) log in
  (* External modification between read and commit *)
  write_tvar_raw tv external_value;
  (* Now try to commit — should detect conflict *)
  commit log

(* Run two transactions on the same TVar, second wins *)
let simulate_two_transactions (tv : int tvar) (f1 : int -> int) (f2 : int -> int) : int =
  (* Tx1 reads and prepares *)
  let log1 = empty_log () in
  let v1 = match (read_tvar tv) log1 with Success v -> v | _ -> 0 in
  let _ = (write_tvar tv (f1 v1)) log1 in
  (* Tx2 reads, prepares, and commits first *)
  let log2 = empty_log () in
  let v2 = match (read_tvar tv) log2 with Success v -> v | _ -> 0 in
  let _ = (write_tvar tv (f2 v2)) log2 in
  let _ = commit log2 in  (* Tx2 commits first *)
  (* Tx1 tries to commit — should conflict *)
  let result = commit log1 in
  (match result with Committed -> "ERROR" | _ -> "OK");
  tv.value


(* ═══════════════════════════════════════════════════════════════════
   §10  Demo
   ═══════════════════════════════════════════════════════════════════ *)

let () =
  Printf.printf "╔══════════════════════════════════════════════╗\n";
  Printf.printf "║   Software Transactional Memory (STM)        ║\n";
  Printf.printf "╠══════════════════════════════════════════════╣\n\n";

  (* --- Basic TVar operations --- *)
  Printf.printf "── §1: Basic TVar Operations ──\n\n";

  let x = new_tvar 42 in
  let result = atomically_exn (read_tvar x) in
  Printf.printf "  new_tvar 42, read → %d\n" result;

  atomically_exn (write_tvar x 100);
  Printf.printf "  write 100, read → %d\n" (atomically_exn (read_tvar x));

  atomically_exn (modify_tvar x (fun n -> n * 2));
  Printf.printf "  modify (*2), read → %d\n\n" (atomically_exn (read_tvar x));

  (* --- Bank transfer --- *)
  Printf.printf "── §2: Atomic Bank Transfer ──\n\n";

  let alice = new_account "Alice" 1000 in
  let bob   = new_account "Bob" 500 in
  Printf.printf "  Alice: %d, Bob: %d\n"
    (atomically_exn (get_balance alice))
    (atomically_exn (get_balance bob));

  atomically_exn (transfer alice bob 300);
  Printf.printf "  Transfer 300 Alice→Bob\n";
  Printf.printf "  Alice: %d, Bob: %d\n\n"
    (atomically_exn (get_balance alice))
    (atomically_exn (get_balance bob));

  (* --- OrElse --- *)
  Printf.printf "── §3: OrElse (Composable Choice) ──\n\n";

  let poor  = new_account "Poor" 10 in
  let rich  = new_account "Rich" 5000 in
  let source = atomically_exn (withdraw_from_either poor rich 100) in
  Printf.printf "  Withdraw 100 from Poor(10) or Rich(5000)\n";
  Printf.printf "  Withdrawn from: %s\n" source;
  Printf.printf "  Poor: %d, Rich: %d\n\n"
    (atomically_exn (get_balance poor))
    (atomically_exn (get_balance rich));

  (* --- Bounded channel --- *)
  Printf.printf "── §4: Bounded Channel ──\n\n";

  let ch = new_channel 3 in
  atomically_exn (send ch "hello");
  atomically_exn (send ch "world");
  atomically_exn (send ch "!");
  Printf.printf "  Sent 3 messages to channel (capacity 3)\n";
  (* Channel is full — send would retry *)
  let full_result = atomically (send ch "overflow") in
  Printf.printf "  Send to full channel: %s\n"
    (match full_result with Retried -> "blocked (retry)" | _ -> "unexpected");
  let msg = atomically_exn (receive ch) in
  Printf.printf "  Received: %s\n" msg;
  let msg2 = atomically_exn (try_receive ch) in
  Printf.printf "  Try receive: %s\n\n"
    (match msg2 with Some m -> m | None -> "empty");

  (* --- TMap --- *)
  Printf.printf "── §5: Transactional Map ──\n\n";

  let m = new_tmap () in
  atomically_exn (tmap_put m "x" 10);
  atomically_exn (tmap_put m "y" 20);
  let vx = atomically_exn (tmap_get m "x") in
  let sz = atomically_exn (tmap_size m) in
  Printf.printf "  put x=10, y=20\n";
  Printf.printf "  get x → %s, size → %d\n"
    (match vx with Some v -> string_of_int v | None -> "None") sz;
  atomically_exn (tmap_delete m "x");
  let sz2 = atomically_exn (tmap_size m) in
  Printf.printf "  delete x, size → %d\n\n" sz2;

  (* --- Conflict simulation --- *)
  Printf.printf "── §6: Conflict Detection ──\n\n";

  let cv = new_tvar 0 in
  let conflict_result = simulate_conflict cv 999 777 in
  Printf.printf "  Tx writes 999, external writes 777 before commit\n";
  Printf.printf "  Commit result: %s\n"
    (match conflict_result with
     | Committed -> "committed (unexpected!)"
     | Conflict  -> "CONFLICT detected ✓"
     | Blocked   -> "blocked");
  Printf.printf "  TVar value: %d (external write persisted)\n\n" cv.value;

  (* --- Two-transaction interleave --- *)
  Printf.printf "── §7: Interleaved Transactions ──\n\n";

  let tv = new_tvar 100 in
  let final = simulate_two_transactions tv (fun v -> v + 50) (fun v -> v * 2) in
  Printf.printf "  Initial: 100\n";
  Printf.printf "  Tx1: +50, Tx2: *2 (Tx2 commits first)\n";
  Printf.printf "  Final value: %d (Tx2 won: 100*2 = 200)\n\n" final;

  (* --- Statistics --- *)
  Printf.printf "── §8: Transaction Statistics ──\n\n";

  reset_stats ();
  let c = new_counter 0 in
  for _ = 1 to 100 do
    ignore (atomically_tracked (increment c))
  done;
  let (commits, conflicts, retries) = get_stats () in
  Printf.printf "  100 increments: %d commits, %d conflicts, %d retries\n"
    commits conflicts retries;
  Printf.printf "  Counter value: %d\n\n"
    (atomically_exn (get_counter c));

  Printf.printf "╚══════════════════════════════════════════════╝\n"
