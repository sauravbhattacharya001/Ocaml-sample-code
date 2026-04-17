(* memoize.ml — Memoization combinators for OCaml
 *
 * Demonstrates multiple memoization strategies:
 * 1. Basic hash-table memoization
 * 2. Recursive (fix-point) memoization for recursive functions
 * 3. LRU-bounded memoization with eviction
 * 4. Timed expiry memoization (TTL)
 * 5. Multi-argument memoization
 * 6. Memoization with cache statistics
 *
 * Educational: shows closures, mutation, modules, and functors in action.
 *)

(* ── 1. Basic memoize ──────────────────────────────────────────── *)

let memoize (f : 'a -> 'b) : 'a -> 'b =
  let cache = Hashtbl.create 16 in
  fun x ->
    match Hashtbl.find_opt cache x with
    | Some y -> y
    | None ->
      let y = f x in
      Hashtbl.replace cache x y;
      y

(* ── 2. Recursive memoize (open recursion / fix-point) ─────── *)
(* For functions like fibonacci that call themselves,
   pass the recursive call as a parameter so memoization
   intercepts every recursive invocation. *)

let memoize_rec (f : ('a -> 'b) -> 'a -> 'b) : 'a -> 'b =
  let cache = Hashtbl.create 16 in
  let rec go x =
    match Hashtbl.find_opt cache x with
    | Some y -> y
    | None ->
      let y = f go x in
      Hashtbl.replace cache x y;
      y
  in
  go

(* ── 3. LRU-bounded memoize ───────────────────────────────────── *)
(* Keeps at most [capacity] entries; evicts least-recently-used. *)

module LRU : sig
  type ('a, 'b) t
  val create : int -> ('a, 'b) t
  val find : ('a, 'b) t -> 'a -> 'b option
  val add : ('a, 'b) t -> 'a -> 'b -> unit
  val size : ('a, 'b) t -> int
  val capacity : ('a, 'b) t -> int
end = struct
  type ('a, 'b) entry = {
    key : 'a;
    mutable value : 'b;
    mutable prev : ('a, 'b) entry option;
    mutable next : ('a, 'b) entry option;
  }

  type ('a, 'b) t = {
    cap : int;
    tbl : ('a, ('a, 'b) entry) Hashtbl.t;
    mutable head : ('a, 'b) entry option;  (* most recent *)
    mutable tail : ('a, 'b) entry option;  (* least recent *)
  }

  let create cap =
    { cap; tbl = Hashtbl.create cap; head = None; tail = None }

  let size t = Hashtbl.length t.tbl
  let capacity t = t.cap

  let detach t e =
    (match e.prev with
     | Some p -> p.next <- e.next
     | None -> t.head <- e.next);
    (match e.next with
     | Some n -> n.prev <- e.prev
     | None -> t.tail <- e.prev);
    e.prev <- None;
    e.next <- None

  let push_front t e =
    e.prev <- None;
    e.next <- t.head;
    (match t.head with Some h -> h.prev <- Some e | None -> ());
    t.head <- Some e;
    if t.tail = None then t.tail <- Some e

  let evict_tail t =
    match t.tail with
    | None -> ()
    | Some e ->
      detach t e;
      Hashtbl.remove t.tbl e.key

  let find t key =
    match Hashtbl.find_opt t.tbl key with
    | None -> None
    | Some e ->
      detach t e;
      push_front t e;
      Some e.value

  let add t key value =
    match Hashtbl.find_opt t.tbl key with
    | Some e ->
      e.value <- value;
      detach t e;
      push_front t e
    | None ->
      if Hashtbl.length t.tbl >= t.cap then evict_tail t;
      let e = { key; value; prev = None; next = None } in
      Hashtbl.replace t.tbl key e;
      push_front t e
end

let memoize_lru ~capacity (f : 'a -> 'b) : 'a -> 'b =
  let cache = LRU.create capacity in
  fun x ->
    match LRU.find cache x with
    | Some y -> y
    | None ->
      let y = f x in
      LRU.add cache x y;
      y

(* ── 4. TTL (time-to-live) memoize ────────────────────────────── *)

let memoize_ttl ~ttl_sec (f : 'a -> 'b) : 'a -> 'b =
  let cache : ('a, 'b * float) Hashtbl.t = Hashtbl.create 16 in
  fun x ->
    let now = Unix.gettimeofday () in
    match Hashtbl.find_opt cache x with
    | Some (y, ts) when now -. ts < ttl_sec -> y
    | _ ->
      let y = f x in
      Hashtbl.replace cache x (y, now);
      y

(* ── 5. Two-argument memoize ──────────────────────────────────── *)

let memoize2 (f : 'a -> 'b -> 'c) : 'a -> 'b -> 'c =
  let cache = Hashtbl.create 16 in
  fun a b ->
    let key = (a, b) in
    match Hashtbl.find_opt cache key with
    | Some y -> y
    | None ->
      let y = f a b in
      Hashtbl.replace cache key y;
      y

(* Two-argument recursive memoize (open recursion / fix-point).
   Like [memoize_rec] but for functions of two arguments.  The
   user-supplied [f] receives a [self] callback that routes through
   the cache, ensuring every recursive sub-call is memoized. *)

let memoize2_rec (f : ('a -> 'b -> 'c) -> 'a -> 'b -> 'c) : 'a -> 'b -> 'c =
  let cache = Hashtbl.create 16 in
  let rec go a b =
    let key = (a, b) in
    match Hashtbl.find_opt cache key with
    | Some y -> y
    | None ->
      let y = f go a b in
      Hashtbl.replace cache key y;
      y
  in
  go

(* ── 6. Memoize with statistics ───────────────────────────────── *)

type stats = {
  mutable hits : int;
  mutable misses : int;
}

let memoize_stats (f : 'a -> 'b) : ('a -> 'b) * stats =
  let cache = Hashtbl.create 16 in
  let stats = { hits = 0; misses = 0 } in
  let memo x =
    match Hashtbl.find_opt cache x with
    | Some y ->
      stats.hits <- stats.hits + 1;
      y
    | None ->
      stats.misses <- stats.misses + 1;
      let y = f x in
      Hashtbl.replace cache x y;
      y
  in
  (memo, stats)

let hit_rate s =
  let total = s.hits + s.misses in
  if total = 0 then 0.0
  else float_of_int s.hits /. float_of_int total

(* ── 7. Cache clearing ────────────────────────────────────────── *)

let memoize_clearable (f : 'a -> 'b) : ('a -> 'b) * (unit -> unit) =
  let cache = Hashtbl.create 16 in
  let memo x =
    match Hashtbl.find_opt cache x with
    | Some y -> y
    | None ->
      let y = f x in
      Hashtbl.replace cache x y;
      y
  in
  let clear () = Hashtbl.clear cache in
  (memo, clear)

(* ══════════════════════════════════════════════════════════════════
 *  DEMOS
 * ══════════════════════════════════════════════════════════════════ *)

(* Fibonacci without memoize — exponential *)
let rec fib_slow n =
  if n <= 1 then n
  else fib_slow (n - 1) + fib_slow (n - 2)

(* Fibonacci with recursive memoize — linear *)
let fib_fast =
  memoize_rec (fun self n ->
    if n <= 1 then n
    else self (n - 1) + self (n - 2))

(* Collatz sequence length (memoized) *)
let collatz_len =
  memoize_rec (fun self n ->
    if n = 1 then 0
    else if n mod 2 = 0 then 1 + self (n / 2)
    else 1 + self (3 * n + 1))

(* Binomial coefficient C(n,k) — 2-arg recursive memoize.
   Uses [memoize2_rec] so that every recursive sub-call C(n-1,k-1)
   and C(n-1,k) hits the shared cache, giving O(n*k) time instead
   of the exponential cost of the naive recursion. *)
let binomial =
  memoize2_rec (fun self n k ->
    if k = 0 || k = n then 1
    else self (n - 1) (k - 1) + self (n - 1) k)

(* ── Demo runner ──────────────────────────────────────────────── *)

let () =
  Printf.printf "=== Memoization Combinators ===\n\n";

  (* 1. Recursive memoize: fibonacci *)
  Printf.printf "-- Fibonacci (recursive memoize) --\n";
  List.iter (fun n ->
    Printf.printf "  fib(%d) = %d\n" n (fib_fast n)
  ) [0; 1; 5; 10; 20; 30; 40; 50];
  print_newline ();

  (* 2. Stats-tracked memoize *)
  Printf.printf "-- Cache statistics --\n";
  let (square, stats) = memoize_stats (fun x -> x * x) in
  List.iter (fun x -> ignore (square x)) [1;2;3;2;1;4;3;2;1;5];
  Printf.printf "  Calls: %d hits, %d misses, %.0f%% hit rate\n"
    stats.hits stats.misses (hit_rate stats *. 100.0);
  print_newline ();

  (* 3. LRU-bounded memoize *)
  Printf.printf "-- LRU memoize (capacity=3) --\n";
  let lru_cube = memoize_lru ~capacity:3 (fun x ->
    Printf.printf "    [computing cube(%d)]\n" x;
    x * x * x
  ) in
  List.iter (fun x ->
    Printf.printf "  cube(%d) = %d\n" x (lru_cube x)
  ) [1; 2; 3; 1; 4; 2];
  (* After adding 4, key 3 was evicted (LRU). Re-requesting 2 recomputes
     because 2 was evicted when 4 was added (order: 1,2,3 -> use 1 -> 1,2,3
     -> add 4, evict 3 -> 4,1,2 -> request 2, it's still there) *)
  print_newline ();

  (* 4. Collatz lengths *)
  Printf.printf "-- Collatz sequence lengths --\n";
  List.iter (fun n ->
    Printf.printf "  collatz_len(%d) = %d\n" n (collatz_len n)
  ) [1; 7; 27; 100; 1000];
  print_newline ();

  (* 5. Binomial coefficients *)
  Printf.printf "-- Binomial coefficients --\n";
  List.iter (fun (n, k) ->
    Printf.printf "  C(%d,%d) = %d\n" n k (binomial n k)
  ) [(5,2); (10,3); (20,10); (15,7)];
  print_newline ();

  (* 6. Clearable memoize *)
  Printf.printf "-- Clearable memoize --\n";
  let (double, clear) = memoize_clearable (fun x ->
    Printf.printf "    [computing double(%d)]\n" x;
    x * 2
  ) in
  Printf.printf "  double(5) = %d\n" (double 5);
  Printf.printf "  double(5) = %d  (cached)\n" (double 5);
  clear ();
  Printf.printf "  (cache cleared)\n";
  Printf.printf "  double(5) = %d  (recomputed)\n" (double 5);

  Printf.printf "\nDone!\n"
