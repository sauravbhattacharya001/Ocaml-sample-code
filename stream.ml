(* Lazy streams — infinite/lazy sequences with on-demand evaluation *)
(* Demonstrates: lazy evaluation, thunks, coinductive data, memoization, *)
(* higher-order functions, infinite data structures, demand-driven computation *)

(* A stream is either empty or a cons cell with a head value and a *)
(* lazily-evaluated tail. OCaml's built-in `lazy` keyword provides *)
(* memoized thunks — the tail is computed at most once. *)
type 'a stream =
  | Nil
  | Cons of 'a * 'a stream Lazy.t

(* ── Constructors ──────────────────────────────────────────────── *)

(* The empty stream *)
let empty = Nil

(* A single-element stream *)
let singleton x = Cons (x, lazy Nil)

(* Cons a value onto a stream (strict tail) *)
let cons x s = Cons (x, lazy s)

(* Cons a value onto a lazily-evaluated tail *)
let cons_lazy x tail = Cons (x, tail)

(* Build a stream from a seed using an unfold function. *)
(* f returns None to end, or Some (value, next_seed) to continue. *)
(* This is the dual of fold — it produces structure instead of consuming it. *)
let rec unfold f seed =
  match f seed with
  | None -> Nil
  | Some (value, next_seed) ->
    Cons (value, lazy (unfold f next_seed))

(* Build a stream by repeatedly applying f to a seed: seed, f(seed), f(f(seed)), ... *)
let rec iterate f x =
  Cons (x, lazy (iterate f (f x)))

(* Build an infinite stream by repeating a single value *)
let rec repeat x =
  Cons (x, lazy (repeat x))

(* Cycle a non-empty list into an infinite stream: [1;2;3] → 1,2,3,1,2,3,... *)
let cycle lst =
  if lst = [] then invalid_arg "Stream.cycle: empty list";
  let rec go = function
    | [] -> go lst
    | x :: rest -> Cons (x, lazy (go rest))
  in
  go lst

(* Build a stream from a list (finite) *)
let rec of_list = function
  | [] -> Nil
  | x :: rest -> Cons (x, lazy (of_list rest))

(* Build a stream of integers from start (inclusive), stepping by step *)
let rec from ?(step=1) start =
  Cons (start, lazy (from ~step (start + step)))

(* Build a range [lo..hi] (inclusive, finite) *)
let range ?(step=1) lo hi =
  unfold (fun n -> if n > hi then None else Some (n, n + step)) lo

(* ── Observation / Deconstruction ──────────────────────────────── *)

(* Get the head of a stream. Raises Failure on empty. *)
let hd = function
  | Nil -> failwith "Stream.hd: empty stream"
  | Cons (x, _) -> x

(* Get the tail of a stream. Raises Failure on empty. *)
let tl = function
  | Nil -> failwith "Stream.tl: empty stream"
  | Cons (_, rest) -> Lazy.force rest

(* Safe head — returns option *)
let hd_opt = function
  | Nil -> None
  | Cons (x, _) -> Some x

(* Peek at the first element without consuming *)
let peek = hd_opt

(* Check if a stream is empty *)
let is_empty = function
  | Nil -> true
  | Cons _ -> false

(* Take the first n elements as a list — O(n) *)
let take n s =
  let rec aux n s acc =
    if n <= 0 then List.rev acc
    else match s with
      | Nil -> List.rev acc
      | Cons (x, rest) -> aux (n - 1) (Lazy.force rest) (x :: acc)
  in
  aux n s []

(* Take elements while a predicate holds — returns a list *)
let take_while pred s =
  let rec aux s acc =
    match s with
    | Nil -> List.rev acc
    | Cons (x, rest) ->
      if pred x then aux (Lazy.force rest) (x :: acc)
      else List.rev acc
  in
  aux s []

(* Drop the first n elements — O(n), returns a stream *)
let rec drop n s =
  if n <= 0 then s
  else match s with
    | Nil -> Nil
    | Cons (_, rest) -> drop (n - 1) (Lazy.force rest)

(* Drop elements while a predicate holds *)
let rec drop_while pred = function
  | Nil -> Nil
  | Cons (x, rest) as s ->
    if pred x then drop_while pred (Lazy.force rest)
    else s

(* Get the nth element (0-indexed). Raises Failure if out of range. *)
let nth n s =
  if n < 0 then invalid_arg "Stream.nth: negative index";
  let s' = drop n s in
  hd s'

(* Get the nth element as an option *)
let nth_opt n s =
  if n < 0 then None
  else
    let s' = drop n s in
    hd_opt s'

(* Convert a finite stream to a list — diverges on infinite streams! *)
let to_list s =
  let rec aux s acc =
    match s with
    | Nil -> List.rev acc
    | Cons (x, rest) -> aux (Lazy.force rest) (x :: acc)
  in
  aux s []

(* Length of a finite stream — diverges on infinite streams! *)
let length s =
  let rec aux s n =
    match s with
    | Nil -> n
    | Cons (_, rest) -> aux (Lazy.force rest) (n + 1)
  in
  aux s 0

(* ── Transformations ───────────────────────────────────────────── *)

(* Map a function over a stream (lazy — O(1) to construct) *)
let rec map f = function
  | Nil -> Nil
  | Cons (x, rest) ->
    Cons (f x, lazy (map f (Lazy.force rest)))

(* Map with index: f receives (index, element) *)
let mapi f s =
  let rec aux i = function
    | Nil -> Nil
    | Cons (x, rest) ->
      Cons (f i x, lazy (aux (i + 1) (Lazy.force rest)))
  in
  aux 0 s

(* Filter elements by a predicate (lazy) *)
let rec filter pred = function
  | Nil -> Nil
  | Cons (x, rest) ->
    if pred x then Cons (x, lazy (filter pred (Lazy.force rest)))
    else filter pred (Lazy.force rest)

(* Filter + map: keep elements where f returns Some *)
let rec filter_map f = function
  | Nil -> Nil
  | Cons (x, rest) ->
    match f x with
    | Some y -> Cons (y, lazy (filter_map f (Lazy.force rest)))
    | None -> filter_map f (Lazy.force rest)

(* Flat map: map then flatten — each element produces a finite list *)
let flat_map f s =
  let rec aux pending s =
    match pending with
    | x :: rest -> Cons (x, lazy (aux rest s))
    | [] ->
      match s with
      | Nil -> Nil
      | Cons (x, rest) -> aux (f x) (Lazy.force rest)
  in
  aux [] s

(* Scan (running fold) — produces a stream of intermediate accumulator values *)
let rec scan f init = function
  | Nil -> singleton init
  | Cons (x, rest) ->
    let acc = f init x in
    Cons (init, lazy (scan f acc (Lazy.force rest)))

(* ── Combining Streams ─────────────────────────────────────────── *)

(* Append two streams — first must be finite for second to be reached *)
let rec append s1 s2 =
  match s1 with
  | Nil -> s2
  | Cons (x, rest) ->
    Cons (x, lazy (append (Lazy.force rest) s2))

(* Interleave two streams: a1,b1,a2,b2,... *)
(* Fair merge — guaranteed to reach all elements of both streams *)
let rec interleave s1 s2 =
  match s1 with
  | Nil -> s2
  | Cons (x, rest) ->
    Cons (x, lazy (interleave s2 (Lazy.force rest)))

(* Zip two streams into pairs — stops at the shorter one *)
let rec zip s1 s2 =
  match s1, s2 with
  | Cons (a, rest1), Cons (b, rest2) ->
    Cons ((a, b), lazy (zip (Lazy.force rest1) (Lazy.force rest2)))
  | _ -> Nil

(* Zip with a combining function *)
let rec zip_with f s1 s2 =
  match s1, s2 with
  | Cons (a, rest1), Cons (b, rest2) ->
    Cons (f a b, lazy (zip_with f (Lazy.force rest1) (Lazy.force rest2)))
  | _ -> Nil

(* Unzip a stream of pairs into a pair of streams *)
let unzip s =
  (map fst s, map snd s)

(* ── Searching ─────────────────────────────────────────────────── *)

(* Find the first element satisfying a predicate. *)
(* WARNING: diverges if no such element exists in an infinite stream! *)
let rec find pred = function
  | Nil -> None
  | Cons (x, rest) ->
    if pred x then Some x
    else find pred (Lazy.force rest)

(* Check if any element satisfies a predicate (on a finite prefix). *)
(* For infinite streams, use with take/take_while first! *)
let exists pred s =
  find pred s <> None

(* Fold over a finite stream — diverges on infinite streams! *)
let fold f init s =
  let rec aux acc = function
    | Nil -> acc
    | Cons (x, rest) -> aux (f acc x) (Lazy.force rest)
  in
  aux init s

(* Iterate a side effect over a finite stream *)
let iter f s =
  let rec aux = function
    | Nil -> ()
    | Cons (x, rest) -> f x; aux (Lazy.force rest)
  in
  aux s

(* ── Classic Streams ───────────────────────────────────────────── *)

(* Natural numbers: 0, 1, 2, 3, ... *)
let nats = from 0

(* Positive integers: 1, 2, 3, ... *)
let naturals = from 1

(* Fibonacci sequence: 0, 1, 1, 2, 3, 5, 8, 13, ... *)
let fibs =
  let rec aux a b =
    Cons (a, lazy (aux b (a + b)))
  in
  aux 0 1

(* Powers of 2: 1, 2, 4, 8, 16, ... *)
let powers_of_2 = iterate (fun x -> x * 2) 1

(* Factorials: 1, 1, 2, 6, 24, 120, ... (0!, 1!, 2!, 3!, ...) *)
let factorials =
  let rec aux n fact =
    Cons (fact, lazy (aux (n + 1) (fact * (n + 1))))
  in
  aux 0 1

(* Triangular numbers: 0, 1, 3, 6, 10, 15, ... *)
let triangulars =
  mapi (fun i _ -> i * (i + 1) / 2) nats

(* Primes via incremental Sieve of Eratosthenes *)
(* sieve removes multiples lazily — elegant but not the fastest *)
let primes =
  let rec sieve = function
    | Nil -> Nil
    | Cons (p, rest) ->
      Cons (p, lazy (sieve (filter (fun n -> n mod p <> 0) (Lazy.force rest))))
  in
  sieve (from 2)

(* ── Pretty Printing ───────────────────────────────────────────── *)

(* Show the first n elements of a stream as a string *)
let show ?(n=10) to_string s =
  let elems = take n s in
  let parts = List.map to_string elems in
  let suffix = match drop n s with Nil -> "" | Cons _ -> "; ..." in
  "[" ^ String.concat "; " parts ^ suffix ^ "]"

(* Show an integer stream *)
let show_ints ?(n=10) s = show ~n string_of_int s

(* Utility: string of pair *)
let show_pairs ?(n=10) fa fb s =
  show ~n (fun (a, b) -> "(" ^ fa a ^ ", " ^ fb b ^ ")") s
