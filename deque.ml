(* deque.ml — Purely Functional Deque (Double-Ended Queue) *)
(* A persistent double-ended queue with amortised O(1) operations on
   both ends, based on the "Banker's Deque" from Okasaki's
   "Purely Functional Data Structures" (Chapter 8).

   A deque supports efficient insertion and removal at BOTH the front
   and back, unlike a queue (front-only removal) or stack (front-only
   everything).  This makes it ideal for:
   - Sliding window algorithms
   - BFS with priority at both ends (0-1 BFS)
   - Work-stealing schedulers
   - Editor undo/redo buffers
   - Any algorithm that needs to inspect or modify both ends

   Implementation: two lists (front and rear) with a *balance invariant*:
   neither list may be more than C times longer than the other plus 1.
   When the invariant is violated, we rebalance by splitting the longer
   list and reversing half onto the shorter.  The constant C = 3 gives
   good amortised bounds.

   The balance invariant ensures that both ends always have elements
   available without traversing the entire structure.  This is what
   upgrades the basic two-list queue (which only guarantees O(1) at
   one end) to O(1) amortised at BOTH ends.

   Complexity:
     push_front / push_back:   O(1) worst-case
     pop_front / pop_back:     O(1) amortised (O(n) during rebalance)
     peek_front / peek_back:   O(1) amortised
     length:                   O(1) worst-case
     is_empty:                 O(1) worst-case
     append:                   O(n)
     reverse:                  O(n)
     of_list / to_list:        O(n)
     map / filter / fold:      O(n)
     nth:                      O(n)

   All operations are pure — every mutating function returns a new
   deque, leaving the original unchanged.  Safe for backtracking,
   persistent data structures, and concurrent use.

   Usage:
     let d = Deque.empty in
     let d = Deque.push_back 1 d in
     let d = Deque.push_back 2 d in
     let d = Deque.push_front 0 d in
     Deque.to_list d                     (* [0; 1; 2] *)
     Deque.peek_front d                  (* Some 0 *)
     Deque.peek_back d                   (* Some 2 *)
     let (v, d') = Deque.pop_front d in  (* v = Some 0, d' = [1; 2] *)
     let (v, d') = Deque.pop_back d in   (* v = Some 2, d' = [0; 1] *)

     (* Sliding window: keep last 3 elements *)
     let d = Deque.of_list [1; 2; 3; 4; 5] in
     let d = Deque.drop_front 2 d in
     Deque.to_list d                     (* [3; 4; 5] *)

     (* Palindrome check using deque *)
     let is_palindrome lst =
       let d = Deque.of_list lst in
       let rec check d =
         if Deque.length d <= 1 then true
         else
           let (Some a, d) = Deque.pop_front d in
           let (Some b, d) = Deque.pop_back d in
           a = b && check d
       in check d
     (* is_palindrome [1;2;3;2;1]  => true *)
*)


(* ── Core type ─────────────────────────────────────────────── *)

(* The deque maintains:
   - front:      elements accessible from the front (head = front-most)
   - rear:       elements accessible from the back (head = back-most)
   - front_len:  length of front (cached to avoid recomputing)
   - rear_len:   length of rear (cached to avoid recomputing)

   Invariant: neither front_len nor rear_len exceeds
   C * (the other) + 1, where C = 3.  This ensures both
   lists have elements, so peek/pop at either end is O(1).

   When the invariant is broken (e.g., after many push_fronts),
   we split the longer list in half and reverse the second half
   onto the shorter list.
*)

module Deque : sig
  type 'a t

  (** The empty deque. *)
  val empty : 'a t

  (** Is the deque empty? O(1). *)
  val is_empty : 'a t -> bool

  (** Number of elements. O(1). *)
  val length : 'a t -> int

  (** Add an element to the front. O(1). *)
  val push_front : 'a -> 'a t -> 'a t

  (** Add an element to the back. O(1). *)
  val push_back : 'a -> 'a t -> 'a t

  (** View the front element. O(1) amortised. *)
  val peek_front : 'a t -> 'a option

  (** View the back element. O(1) amortised. *)
  val peek_back : 'a t -> 'a option

  (** Remove the front element. Returns (element option, new deque). O(1) amortised. *)
  val pop_front : 'a t -> 'a option * 'a t

  (** Remove the back element. Returns (element option, new deque). O(1) amortised. *)
  val pop_back : 'a t -> 'a option * 'a t

  (** Get the nth element (0-indexed, front-to-back). O(n). *)
  val nth : int -> 'a t -> 'a option

  (** Drop the first n elements from the front. O(n). *)
  val drop_front : int -> 'a t -> 'a t

  (** Drop the last n elements from the back. O(n). *)
  val drop_back : int -> 'a t -> 'a t

  (** Reverse the deque. O(1) — just swaps front and rear! *)
  val rev : 'a t -> 'a t

  (** Append two deques. O(n) where n = length of second deque. *)
  val append : 'a t -> 'a t -> 'a t

  (** Apply a function to every element. O(n). *)
  val map : ('a -> 'b) -> 'a t -> 'b t

  (** Keep only elements satisfying the predicate. O(n). *)
  val filter : ('a -> bool) -> 'a t -> 'a t

  (** Left fold, front to back. O(n). *)
  val fold_left : ('b -> 'a -> 'b) -> 'b -> 'a t -> 'b

  (** Right fold, back to front. O(n). *)
  val fold_right : ('a -> 'b -> 'b) -> 'a t -> 'b -> 'b

  (** Iterate a function over all elements, front to back. O(n). *)
  val iter : ('a -> unit) -> 'a t -> unit

  (** Do all elements satisfy the predicate? O(n). *)
  val for_all : ('a -> bool) -> 'a t -> bool

  (** Does any element satisfy the predicate? O(n). *)
  val exists : ('a -> bool) -> 'a t -> bool

  (** Find the first element satisfying the predicate. O(n). *)
  val find : ('a -> bool) -> 'a t -> 'a option

  (** Convert a list to a deque. O(n). *)
  val of_list : 'a list -> 'a t

  (** Convert a deque to a list, front to back. O(n). *)
  val to_list : 'a t -> 'a list

  (** Create a deque of a single element. O(1). *)
  val singleton : 'a -> 'a t

  (** Take the first n elements from the front. O(n). *)
  val take_front : int -> 'a t -> 'a t

  (** Take the last n elements from the back. O(n). *)
  val take_back : int -> 'a t -> 'a t

  (** Split the deque at position n. O(n). *)
  val split_at : int -> 'a t -> 'a t * 'a t

  (** Zip two deques element-wise. Stops at the shorter. O(min(m,n)). *)
  val zip : 'a t -> 'b t -> ('a * 'b) t

  (** Pretty-print using a custom element formatter. *)
  val to_string : ('a -> string) -> 'a t -> string

end = struct

  (* Balance constant: neither list may exceed C * other + 1 *)
  let balance_c = 3

  type 'a t = {
    front : 'a list;
    rear  : 'a list;
    flen  : int;
    rlen  : int;
  }

  let empty = { front = []; rear = []; flen = 0; rlen = 0 }

  let is_empty d = d.flen + d.rlen = 0

  let length d = d.flen + d.rlen

  (* ── Helpers ───────────────────────────────────────────── *)

  (* Split a list: take first n elements, return (first_n, rest) *)
  let rec split_list n lst acc =
    if n <= 0 then (List.rev acc, lst)
    else match lst with
      | []     -> (List.rev acc, [])
      | x :: xs -> split_list (n - 1) xs (x :: acc)

  (* Rebalance if the invariant is violated *)
  let check d =
    if d.flen > balance_c * d.rlen + 1 then begin
      (* Front is too long — move half to rear *)
      let half = (d.flen + d.rlen) / 2 in
      let keep = (d.flen + d.rlen) - half in
      let (new_front, excess) = split_list keep d.front [] in
      let new_rear = d.rear @ List.rev excess in
      { front = new_front; rear = new_rear;
        flen = keep; rlen = half }
    end
    else if d.rlen > balance_c * d.flen + 1 then begin
      (* Rear is too long — move half to front *)
      let half = (d.flen + d.rlen) / 2 in
      let keep = (d.flen + d.rlen) - half in
      let (new_rear, excess) = split_list keep d.rear [] in
      let new_front = d.front @ List.rev excess in
      { front = new_front; rear = new_rear;
        flen = half; rlen = keep }
    end
    else d

  (* ── Core operations ───────────────────────────────────── *)

  let push_front x d =
    check { d with front = x :: d.front; flen = d.flen + 1 }

  let push_back x d =
    check { d with rear = x :: d.rear; rlen = d.rlen + 1 }

  let peek_front d =
    match d.front with
    | x :: _ -> Some x
    | [] ->
      (* Front empty but rear may have elements *)
      match d.rear with
      | [x]  -> Some x
      | _    ->
        (* After rebalance, front should have elements *)
        let d' = check d in
        (match d'.front with x :: _ -> Some x | [] ->
          match d'.rear with x :: _ -> Some x | [] -> None)

  let peek_back d =
    match d.rear with
    | x :: _ -> Some x
    | [] ->
      match d.front with
      | [x]  -> Some x
      | _    ->
        let d' = check d in
        (match d'.rear with x :: _ -> Some x | [] ->
          match d'.front with x :: _ -> Some x | [] -> None)

  let pop_front d =
    if is_empty d then (None, empty)
    else
      match d.front with
      | x :: rest ->
        let d' = check { d with front = rest; flen = d.flen - 1 } in
        (Some x, d')
      | [] ->
        (* Front empty — rear must have elements *)
        match d.rear with
        | [x]  -> (Some x, empty)
        | _ ->
          (* Force rebalance first *)
          let d' = check d in
          (match d'.front with
           | x :: rest ->
             let d'' = check { d' with front = rest; flen = d'.flen - 1 } in
             (Some x, d'')
           | [] ->
             match d'.rear with
             | x :: rest ->
               (Some x, check { d' with rear = rest; rlen = d'.rlen - 1 })
             | [] -> (None, empty))

  let pop_back d =
    if is_empty d then (None, empty)
    else
      match d.rear with
      | x :: rest ->
        let d' = check { d with rear = rest; rlen = d.rlen - 1 } in
        (Some x, d')
      | [] ->
        match d.front with
        | [x]  -> (Some x, empty)
        | _ ->
          let d' = check d in
          (match d'.rear with
           | x :: rest ->
             let d'' = check { d' with rear = rest; rlen = d'.rlen - 1 } in
             (Some x, d'')
           | [] ->
             match d'.front with
             | x :: rest ->
               (Some x, check { d' with front = rest; flen = d'.flen - 1 })
             | [] -> (None, empty))

  let nth n d =
    if n < 0 || n >= length d then None
    else if n < d.flen then
      (* Element is in the front list *)
      let rec get i = function
        | [] -> None
        | x :: _ when i = 0 -> Some x
        | _ :: xs -> get (i - 1) xs
      in get n d.front
    else
      (* Element is in the rear list (reversed order) *)
      let rear_idx = d.rlen - 1 - (n - d.flen) in
      let rec get i = function
        | [] -> None
        | x :: _ when i = 0 -> Some x
        | _ :: xs -> get (i - 1) xs
      in get rear_idx d.rear

  let rec drop_front n d =
    if n <= 0 then d
    else
      let (_, d') = pop_front d in
      drop_front (n - 1) d'

  let rec drop_back n d =
    if n <= 0 then d
    else
      let (_, d') = pop_back d in
      drop_back (n - 1) d'

  let rev d =
    (* Swapping front and rear reverses the logical order — O(1)! *)
    { front = d.rear; rear = d.front; flen = d.rlen; rlen = d.flen }

  let to_list d =
    d.front @ List.rev d.rear

  let of_list lst =
    (* Split evenly between front and rear for good balance *)
    let n = List.length lst in
    let half = n / 2 in
    let (front_part, rear_part) = split_list half lst [] in
    check { front = front_part; rear = List.rev rear_part;
            flen = half; rlen = n - half }

  let singleton x =
    { front = [x]; rear = []; flen = 1; rlen = 0 }

  let append d1 d2 =
    (* Convert d2 to list and push each onto d1's back *)
    let lst2 = to_list d2 in
    List.fold_left (fun acc x -> push_back x acc) d1 lst2

  let map f d =
    of_list (List.map f (to_list d))

  let filter pred d =
    of_list (List.filter pred (to_list d))

  let fold_left f init d =
    let lst = to_list d in
    List.fold_left f init lst

  let fold_right f d init =
    let lst = to_list d in
    List.fold_right f lst init

  let iter f d =
    List.iter f (to_list d)

  let for_all pred d =
    List.for_all pred (to_list d)

  let exists pred d =
    List.exists pred (to_list d)

  let find pred d =
    List.find_opt pred (to_list d)

  let take_front n d =
    let lst = to_list d in
    let rec take i acc = function
      | _ when i <= 0 -> List.rev acc
      | [] -> List.rev acc
      | x :: xs -> take (i - 1) (x :: acc) xs
    in of_list (take n [] lst)

  let take_back n d =
    let lst = to_list d in
    let total = List.length lst in
    let skip = max 0 (total - n) in
    let rec drop i = function
      | [] -> []
      | _ :: xs when i > 0 -> drop (i - 1) xs
      | lst -> lst
    in of_list (drop skip lst)

  let split_at n d =
    let lst = to_list d in
    let (left, right) = split_list n lst [] in
    (of_list left, of_list right)

  let zip d1 d2 =
    let rec aux acc l1 l2 =
      match l1, l2 with
      | [], _ | _, [] -> List.rev acc
      | x :: xs, y :: ys -> aux ((x, y) :: acc) xs ys
    in of_list (aux [] (to_list d1) (to_list d2))

  let to_string fmt d =
    let elements = to_list d in
    let inner = String.concat "; " (List.map fmt elements) in
    "Deque[" ^ inner ^ "]"

end


(* ══════════════════════════════════════════════════════════════ *)
(* Interactive demo / test suite                                  *)
(* ══════════════════════════════════════════════════════════════ *)

let () =
  let passed = ref 0 in
  let failed = ref 0 in
  let test name f =
    if f () then (incr passed; Printf.printf "  ✓ %s\n" name)
    else (incr failed; Printf.printf "  ✗ %s\n" name)
  in

  Printf.printf "\n═══ Functional Deque (Banker's Deque) ═══\n\n";

  (* ── Basic operations ─────────────────────────────── *)

  Printf.printf "── Basic Operations ──\n";

  test "empty deque has length 0" (fun () ->
    Deque.length Deque.empty = 0);

  test "empty deque is_empty" (fun () ->
    Deque.is_empty Deque.empty);

  test "singleton has length 1" (fun () ->
    Deque.length (Deque.singleton 42) = 1);

  test "singleton peek_front" (fun () ->
    Deque.peek_front (Deque.singleton 42) = Some 42);

  test "singleton peek_back" (fun () ->
    Deque.peek_back (Deque.singleton 42) = Some 42);

  (* ── Push operations ──────────────────────────────── *)

  Printf.printf "\n── Push Operations ──\n";

  test "push_front increases length" (fun () ->
    let d = Deque.push_front 1 Deque.empty in
    Deque.length d = 1);

  test "push_back increases length" (fun () ->
    let d = Deque.push_back 1 Deque.empty in
    Deque.length d = 1);

  test "push_front then peek_front" (fun () ->
    let d = Deque.push_front 1 Deque.empty in
    let d = Deque.push_front 2 d in
    Deque.peek_front d = Some 2);

  test "push_back then peek_back" (fun () ->
    let d = Deque.push_back 1 Deque.empty in
    let d = Deque.push_back 2 d in
    Deque.peek_back d = Some 2);

  test "push_front preserves order" (fun () ->
    let d = Deque.push_front 3 Deque.empty in
    let d = Deque.push_front 2 d in
    let d = Deque.push_front 1 d in
    Deque.to_list d = [1; 2; 3]);

  test "push_back preserves order" (fun () ->
    let d = Deque.push_back 1 Deque.empty in
    let d = Deque.push_back 2 d in
    let d = Deque.push_back 3 d in
    Deque.to_list d = [1; 2; 3]);

  test "mixed push_front and push_back" (fun () ->
    let d = Deque.push_back 2 Deque.empty in
    let d = Deque.push_front 1 d in
    let d = Deque.push_back 3 d in
    let d = Deque.push_front 0 d in
    Deque.to_list d = [0; 1; 2; 3]);

  (* ── Pop operations ───────────────────────────────── *)

  Printf.printf "\n── Pop Operations ──\n";

  test "pop_front from empty" (fun () ->
    let (v, _) = Deque.pop_front Deque.empty in
    v = None);

  test "pop_back from empty" (fun () ->
    let (v, _) = Deque.pop_back Deque.empty in
    v = None);

  test "pop_front returns front element" (fun () ->
    let d = Deque.of_list [1; 2; 3] in
    let (v, _) = Deque.pop_front d in
    v = Some 1);

  test "pop_back returns back element" (fun () ->
    let d = Deque.of_list [1; 2; 3] in
    let (v, _) = Deque.pop_back d in
    v = Some 3);

  test "pop_front decreases length" (fun () ->
    let d = Deque.of_list [1; 2; 3] in
    let (_, d') = Deque.pop_front d in
    Deque.length d' = 2);

  test "pop_front preserves remaining" (fun () ->
    let d = Deque.of_list [1; 2; 3] in
    let (_, d') = Deque.pop_front d in
    Deque.to_list d' = [2; 3]);

  test "pop_back preserves remaining" (fun () ->
    let d = Deque.of_list [1; 2; 3] in
    let (_, d') = Deque.pop_back d in
    Deque.to_list d' = [1; 2]);

  test "alternating pop_front and pop_back" (fun () ->
    let d = Deque.of_list [1; 2; 3; 4] in
    let (a, d) = Deque.pop_front d in
    let (b, d) = Deque.pop_back d in
    let (c, d) = Deque.pop_front d in
    let (e, _) = Deque.pop_back d in
    a = Some 1 && b = Some 4 && c = Some 2 && e = Some 3);

  test "pop_front from singleton" (fun () ->
    let d = Deque.singleton 42 in
    let (v, d') = Deque.pop_front d in
    v = Some 42 && Deque.is_empty d');

  test "pop_back from singleton" (fun () ->
    let d = Deque.singleton 42 in
    let (v, d') = Deque.pop_back d in
    v = Some 42 && Deque.is_empty d');

  (* ── Persistence ──────────────────────────────────── *)

  Printf.printf "\n── Persistence ──\n";

  test "push_front doesn't modify original" (fun () ->
    let d1 = Deque.of_list [1; 2; 3] in
    let _d2 = Deque.push_front 0 d1 in
    Deque.to_list d1 = [1; 2; 3]);

  test "pop_front doesn't modify original" (fun () ->
    let d1 = Deque.of_list [1; 2; 3] in
    let (_, _d2) = Deque.pop_front d1 in
    Deque.to_list d1 = [1; 2; 3]);

  test "multiple versions coexist" (fun () ->
    let d0 = Deque.of_list [1; 2; 3] in
    let d1 = Deque.push_front 0 d0 in
    let d2 = Deque.push_back 4 d0 in
    Deque.to_list d0 = [1; 2; 3] &&
    Deque.to_list d1 = [0; 1; 2; 3] &&
    Deque.to_list d2 = [1; 2; 3; 4]);

  (* ── Conversion ───────────────────────────────────── *)

  Printf.printf "\n── Conversion ──\n";

  test "of_list then to_list is identity" (fun () ->
    let lst = [1; 2; 3; 4; 5] in
    Deque.to_list (Deque.of_list lst) = lst);

  test "of_list empty" (fun () ->
    Deque.is_empty (Deque.of_list []));

  test "of_list singleton" (fun () ->
    Deque.to_list (Deque.of_list [42]) = [42]);

  test "to_string" (fun () ->
    let d = Deque.of_list [1; 2; 3] in
    Deque.to_string string_of_int d = "Deque[1; 2; 3]");

  (* ── nth ──────────────────────────────────────────── *)

  Printf.printf "\n── Random Access ──\n";

  test "nth first element" (fun () ->
    let d = Deque.of_list [10; 20; 30] in
    Deque.nth 0 d = Some 10);

  test "nth last element" (fun () ->
    let d = Deque.of_list [10; 20; 30] in
    Deque.nth 2 d = Some 30);

  test "nth middle element" (fun () ->
    let d = Deque.of_list [10; 20; 30] in
    Deque.nth 1 d = Some 20);

  test "nth out of bounds" (fun () ->
    let d = Deque.of_list [1; 2; 3] in
    Deque.nth 5 d = None);

  test "nth negative" (fun () ->
    let d = Deque.of_list [1; 2; 3] in
    Deque.nth (-1) d = None);

  (* ── Reverse ──────────────────────────────────────── *)

  Printf.printf "\n── Reverse ──\n";

  test "rev reverses elements" (fun () ->
    let d = Deque.of_list [1; 2; 3; 4; 5] in
    Deque.to_list (Deque.rev d) = [5; 4; 3; 2; 1]);

  test "rev of empty" (fun () ->
    Deque.is_empty (Deque.rev Deque.empty));

  test "rev of singleton" (fun () ->
    Deque.to_list (Deque.rev (Deque.singleton 42)) = [42]);

  test "double rev is identity" (fun () ->
    let d = Deque.of_list [1; 2; 3] in
    Deque.to_list (Deque.rev (Deque.rev d)) = [1; 2; 3]);

  (* ── Append ───────────────────────────────────────── *)

  Printf.printf "\n── Append ──\n";

  test "append two deques" (fun () ->
    let d1 = Deque.of_list [1; 2; 3] in
    let d2 = Deque.of_list [4; 5; 6] in
    Deque.to_list (Deque.append d1 d2) = [1; 2; 3; 4; 5; 6]);

  test "append with empty" (fun () ->
    let d = Deque.of_list [1; 2; 3] in
    Deque.to_list (Deque.append d Deque.empty) = [1; 2; 3] &&
    Deque.to_list (Deque.append Deque.empty d) = [1; 2; 3]);

  (* ── Map / Filter / Fold ──────────────────────────── *)

  Printf.printf "\n── Higher-Order Operations ──\n";

  test "map doubles elements" (fun () ->
    let d = Deque.of_list [1; 2; 3; 4; 5] in
    Deque.to_list (Deque.map (fun x -> x * 2) d) = [2; 4; 6; 8; 10]);

  test "filter keeps evens" (fun () ->
    let d = Deque.of_list [1; 2; 3; 4; 5; 6] in
    Deque.to_list (Deque.filter (fun x -> x mod 2 = 0) d) = [2; 4; 6]);

  test "filter removes all" (fun () ->
    let d = Deque.of_list [1; 3; 5] in
    Deque.is_empty (Deque.filter (fun x -> x mod 2 = 0) d));

  test "fold_left sum" (fun () ->
    let d = Deque.of_list [1; 2; 3; 4; 5] in
    Deque.fold_left (+) 0 d = 15);

  test "fold_right builds list" (fun () ->
    let d = Deque.of_list [1; 2; 3] in
    Deque.fold_right (fun x acc -> x :: acc) d [] = [1; 2; 3]);

  test "iter visits all elements" (fun () ->
    let d = Deque.of_list [1; 2; 3] in
    let sum = ref 0 in
    Deque.iter (fun x -> sum := !sum + x) d;
    !sum = 6);

  test "for_all positive" (fun () ->
    let d = Deque.of_list [2; 4; 6] in
    Deque.for_all (fun x -> x mod 2 = 0) d);

  test "for_all negative" (fun () ->
    let d = Deque.of_list [2; 3; 6] in
    not (Deque.for_all (fun x -> x mod 2 = 0) d));

  test "exists positive" (fun () ->
    let d = Deque.of_list [1; 2; 3] in
    Deque.exists (fun x -> x = 2) d);

  test "exists negative" (fun () ->
    let d = Deque.of_list [1; 2; 3] in
    not (Deque.exists (fun x -> x = 5) d));

  test "find existing" (fun () ->
    let d = Deque.of_list [1; 2; 3; 4; 5] in
    Deque.find (fun x -> x > 3) d = Some 4);

  test "find missing" (fun () ->
    let d = Deque.of_list [1; 2; 3] in
    Deque.find (fun x -> x > 10) d = None);

  (* ── Take / Drop / Split ──────────────────────────── *)

  Printf.printf "\n── Take / Drop / Split ──\n";

  test "take_front 3" (fun () ->
    let d = Deque.of_list [1; 2; 3; 4; 5] in
    Deque.to_list (Deque.take_front 3 d) = [1; 2; 3]);

  test "take_back 3" (fun () ->
    let d = Deque.of_list [1; 2; 3; 4; 5] in
    Deque.to_list (Deque.take_back 3 d) = [3; 4; 5]);

  test "drop_front 2" (fun () ->
    let d = Deque.of_list [1; 2; 3; 4; 5] in
    Deque.to_list (Deque.drop_front 2 d) = [3; 4; 5]);

  test "drop_back 2" (fun () ->
    let d = Deque.of_list [1; 2; 3; 4; 5] in
    Deque.to_list (Deque.drop_back 2 d) = [1; 2; 3]);

  test "split_at 2" (fun () ->
    let d = Deque.of_list [1; 2; 3; 4; 5] in
    let (left, right) = Deque.split_at 2 d in
    Deque.to_list left = [1; 2] &&
    Deque.to_list right = [3; 4; 5]);

  test "split_at 0" (fun () ->
    let d = Deque.of_list [1; 2; 3] in
    let (left, right) = Deque.split_at 0 d in
    Deque.is_empty left &&
    Deque.to_list right = [1; 2; 3]);

  (* ── Zip ──────────────────────────────────────────── *)

  Printf.printf "\n── Zip ──\n";

  test "zip equal length" (fun () ->
    let d1 = Deque.of_list [1; 2; 3] in
    let d2 = Deque.of_list ["a"; "b"; "c"] in
    Deque.to_list (Deque.zip d1 d2) = [(1, "a"); (2, "b"); (3, "c")]);

  test "zip different lengths" (fun () ->
    let d1 = Deque.of_list [1; 2; 3; 4] in
    let d2 = Deque.of_list ["a"; "b"] in
    Deque.to_list (Deque.zip d1 d2) = [(1, "a"); (2, "b")]);

  (* ── Stress / balance ─────────────────────────────── *)

  Printf.printf "\n── Stress & Balance ──\n";

  test "100 push_fronts maintain correct order" (fun () ->
    let d = ref Deque.empty in
    for i = 99 downto 0 do
      d := Deque.push_front i !d
    done;
    let lst = Deque.to_list !d in
    lst = List.init 100 Fun.id);

  test "100 push_backs maintain correct order" (fun () ->
    let d = ref Deque.empty in
    for i = 0 to 99 do
      d := Deque.push_back i !d
    done;
    let lst = Deque.to_list !d in
    lst = List.init 100 Fun.id);

  test "alternating 50 front / 50 back" (fun () ->
    let d = ref Deque.empty in
    for i = 0 to 49 do
      d := Deque.push_back (50 + i) !d;
      d := Deque.push_front (49 - i) !d
    done;
    Deque.to_list !d = List.init 100 Fun.id);

  test "drain from front gives sorted" (fun () ->
    let d = Deque.of_list (List.init 50 Fun.id) in
    let result = ref [] in
    let d = ref d in
    while not (Deque.is_empty !d) do
      let (v, d') = Deque.pop_front !d in
      (match v with Some x -> result := x :: !result | None -> ());
      d := d'
    done;
    List.rev !result = List.init 50 Fun.id);

  test "drain from back gives reverse sorted" (fun () ->
    let d = Deque.of_list (List.init 50 Fun.id) in
    let result = ref [] in
    let d = ref d in
    while not (Deque.is_empty !d) do
      let (v, d') = Deque.pop_back !d in
      (match v with Some x -> result := x :: !result | None -> ());
      d := d'
    done;
    !result = List.init 50 Fun.id);

  (* ── Palindrome demo ──────────────────────────────── *)

  Printf.printf "\n── Palindrome Checker (Application Demo) ──\n";

  let is_palindrome lst =
    let d = ref (Deque.of_list lst) in
    let result = ref true in
    while Deque.length !d > 1 && !result do
      let (a, d') = Deque.pop_front !d in
      let (b, d'') = Deque.pop_back d' in
      (match a, b with
       | Some x, Some y -> if x <> y then result := false
       | _ -> result := false);
      d := d''
    done;
    !result
  in

  test "palindrome [1;2;3;2;1]" (fun () ->
    is_palindrome [1; 2; 3; 2; 1]);

  test "palindrome [1;2;2;1]" (fun () ->
    is_palindrome [1; 2; 2; 1]);

  test "not palindrome [1;2;3]" (fun () ->
    not (is_palindrome [1; 2; 3]));

  test "palindrome singleton" (fun () ->
    is_palindrome [42]);

  test "palindrome empty" (fun () ->
    is_palindrome []);

  (* ── Sliding window demo ──────────────────────────── *)

  Printf.printf "\n── Sliding Window Max (Application Demo) ──\n";

  (* Classic sliding window maximum using a monotone deque *)
  let sliding_window_max arr k =
    let n = Array.length arr in
    if n = 0 || k <= 0 then [||]
    else begin
      let result = Array.make (max 1 (n - k + 1)) 0 in
      let dq = ref Deque.empty in  (* stores indices *)
      for i = 0 to n - 1 do
        (* Remove elements outside the window *)
        (match Deque.peek_front !dq with
         | Some idx when idx <= i - k ->
           let (_, dq') = Deque.pop_front !dq in
           dq := dq'
         | _ -> ());
        (* Remove elements smaller than current from back *)
        let continue = ref true in
        while !continue do
          match Deque.peek_back !dq with
          | Some idx when arr.(idx) <= arr.(i) ->
            let (_, dq') = Deque.pop_back !dq in
            dq := dq'
          | _ -> continue := false
        done;
        dq := Deque.push_back i !dq;
        if i >= k - 1 then
          match Deque.peek_front !dq with
          | Some idx -> result.(i - k + 1) <- arr.(idx)
          | None -> ()
      done;
      result
    end
  in

  test "sliding window max [1;3;-1;-3;5;3;6;7] k=3" (fun () ->
    let result = sliding_window_max [|1;3;-1;-3;5;3;6;7|] 3 in
    result = [|3;3;5;5;6;7|]);

  test "sliding window max k=1" (fun () ->
    let result = sliding_window_max [|5;2;8;1|] 1 in
    result = [|5;2;8;1|]);

  test "sliding window max k=n" (fun () ->
    let result = sliding_window_max [|2;5;1;8;3|] 5 in
    result = [|8|]);

  (* ── Summary ──────────────────────────────────────── *)

  Printf.printf "\n═══════════════════════════════════════════\n";
  Printf.printf "  Total: %d passed, %d failed\n" !passed !failed;
  Printf.printf "═══════════════════════════════════════════\n";

  if !failed > 0 then exit 1
