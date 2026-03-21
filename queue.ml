(* queue.ml — Purely Functional Queue (Banker's Queue) *)
(* A persistent FIFO queue with amortised O(1) enqueue and dequeue,
   implemented using the classic two-list technique from Okasaki's
   "Purely Functional Data Structures".

   The key insight: maintain two lists — a *front* list for dequeue
   and a *rear* list (stored in reverse) for enqueue.  When the front
   is exhausted, reverse the rear and make it the new front.  This
   reversal costs O(n), but happens infrequently enough that each
   operation is amortised O(1).

   All operations are pure — every mutating function returns a new
   queue, leaving the original unchanged.  This makes the queue safe
   for backtracking, undo, and concurrent use.

   Complexity:
     enqueue:     O(1) worst-case
     dequeue:     O(1) amortised (O(n) worst-case during rotation)
     peek:        O(1) amortised
     length:      O(1) worst-case
     is_empty:    O(1) worst-case
     of_list:     O(n)
     to_list:     O(n)
     append:      O(n) where n = length of second queue
     map / filter / fold: O(n)

   Usage:
     let q = Queue.empty in
     let q = Queue.enqueue 1 q in
     let q = Queue.enqueue 2 q in
     let q = Queue.enqueue 3 q in
     Queue.peek q                    (* Some 1 *)
     let (v, q') = Queue.dequeue q   (* v = Some 1, q' has [2; 3] *)
     Queue.to_list q'                (* [2; 3] *)
     Queue.length q'                 (* 2 *)

     (* Batch operations *)
     let q = Queue.of_list [1; 2; 3; 4; 5] in
     let q = Queue.map (fun x -> x * 2) q in
     Queue.to_list q                 (* [2; 4; 6; 8; 10] *)

     let q = Queue.filter (fun x -> x > 4) q in
     Queue.to_list q                 (* [6; 8; 10] *)

     let sum = Queue.fold_left (+) 0 q in
     sum                             (* 24 *)

     (* Queue is persistent — old versions are still valid *)
     let q1 = Queue.of_list [1; 2; 3] in
     let q2 = Queue.enqueue 4 q1 in
     Queue.to_list q1                (* [1; 2; 3] — unchanged *)
     Queue.to_list q2                (* [1; 2; 3; 4] *)
*)


(* ── Core type ─────────────────────────────────────────────── *)

(* The queue stores:
   - front: elements ready to dequeue (head = next out)
   - rear:  elements recently enqueued (stored in reverse)
   - len:   cached length for O(1) access

   Invariant: if front is empty, rear must also be empty.
   This is maintained by [check], which reverses rear into front
   when front runs out. *)

type 'a t = {
  front : 'a list;
  rear  : 'a list;
  len   : int;
}


(* ── Internal helper ───────────────────────────────────────── *)

(* Restore the invariant: front must be non-empty unless the
   queue is truly empty.  Called after any operation that might
   empty the front list. *)
let check q =
  match q.front with
  | [] -> { front = List.rev q.rear; rear = []; len = q.len }
  | _  -> q


(* ── Constructors ──────────────────────────────────────────── *)

(* The empty queue. *)
let empty = { front = []; rear = []; len = 0 }

(* Create a singleton queue containing one element. *)
let singleton x = { front = [x]; rear = []; len = 1 }

(* Build a queue from a list.  The first element of the list
   will be the first to dequeue (FIFO order preserved). *)
let of_list lst = { front = lst; rear = []; len = List.length lst }


(* ── Queries ───────────────────────────────────────────────── *)

(* Is the queue empty? *)
let is_empty q = q.len = 0

(* Number of elements in the queue. O(1). *)
let length q = q.len

(* Look at the front element without removing it.
   Returns None for an empty queue. *)
let peek q =
  match q.front with
  | x :: _ -> Some x
  | []     ->
    (* Invariant says rear is also empty here *)
    match q.rear with
    | [] -> None
    | _  ->
      (* Shouldn't happen if check is applied, but handle gracefully *)
      let q' = check q in
      (match q'.front with x :: _ -> Some x | [] -> None)

(* Like peek but raises an exception on empty queue. *)
let peek_exn q =
  match peek q with
  | Some x -> x
  | None   -> failwith "Queue.peek_exn: empty queue"


(* ── Core operations ───────────────────────────────────────── *)

(* Add an element to the back of the queue. O(1). *)
let enqueue x q =
  check { q with rear = x :: q.rear; len = q.len + 1 }

(* Remove and return the front element.
   Returns (Some value, remaining_queue) or (None, empty_queue). *)
let dequeue q =
  match q.front with
  | x :: rest ->
    let q' = check { front = rest; rear = q.rear; len = q.len - 1 } in
    (Some x, q')
  | [] ->
    (* Queue is empty (by invariant, rear is also empty) *)
    (None, q)

(* Like dequeue but raises on empty queue.
   Returns (value, remaining_queue). *)
let dequeue_exn q =
  match dequeue q with
  | (Some x, q') -> (x, q')
  | (None, _)    -> failwith "Queue.dequeue_exn: empty queue"


(* ── Bulk operations ───────────────────────────────────────── *)

(* Convert the queue to a list in FIFO order. O(n). *)
let to_list q = q.front @ List.rev q.rear

(* Append all elements of q2 to the back of q1. *)
let append q1 q2 =
  let elems = to_list q2 in
  List.fold_left (fun acc x -> enqueue x acc) q1 elems

(* Enqueue multiple elements at once (in list order). *)
let enqueue_all xs q =
  List.fold_left (fun acc x -> enqueue x acc) q xs


(* ── Internal iteration ─────────────────────────────────────── *)

(* Iterate over elements in FIFO order without allocating an
   intermediate list.  Walks front left-to-right, then rear
   right-to-left (i.e. reversed, which is the enqueue order). *)
let iter_internal f q =
  List.iter f q.front;
  List.iter f (List.rev q.rear)

(* Left fold in FIFO order without allocating an intermediate list. *)
let fold_internal f init q =
  let acc = List.fold_left f init q.front in
  List.fold_left f acc (List.rev q.rear)

(* Short-circuit search in FIFO order: applies [f] to each element
   and returns the first [Some _] result, or [None] if exhausted.
   Avoids materializing the full element list. *)
let rec find_map_list f = function
  | [] -> None
  | x :: rest ->
    match f x with
    | Some _ as hit -> hit
    | None -> find_map_list f rest

let find_map_internal f q =
  match find_map_list f q.front with
  | Some _ as hit -> hit
  | None -> find_map_list f (List.rev q.rear)

(* ── Higher-order operations ───────────────────────────────── *)

(* Apply a function to every element, preserving order.
   Builds the result directly from front/rear without to_list. *)
let map f q =
  let front = List.map f q.front in
  let rear = List.map f q.rear in
  { front; rear; len = q.len }

(* Keep only elements satisfying the predicate.
   Filters front and rear independently, then normalises. *)
let filter pred q =
  let front = List.filter pred q.front in
  let rear = List.filter pred q.rear in
  let len = List.length front + List.length rear in
  check { front; rear; len }

(* Left fold over elements in FIFO order. O(n), no intermediate list. *)
let fold_left f init q =
  fold_internal f init q

(* Right fold over elements in FIFO order. *)
let fold_right f q init =
  let acc = List.fold_right f (List.rev q.rear) init in
  List.fold_right f q.front acc

(* Check whether any element satisfies the predicate.
   Short-circuits on first match — no intermediate list. *)
let exists pred q =
  find_map_internal (fun x -> if pred x then Some () else None) q <> None

(* Check whether all elements satisfy the predicate.
   Short-circuits on first failure — no intermediate list. *)
let for_all pred q =
  find_map_internal (fun x -> if not (pred x) then Some () else None) q = None

(* Find the first element satisfying the predicate.
   Short-circuits — no intermediate list. *)
let find_opt pred q =
  find_map_internal (fun x -> if pred x then Some x else None) q

(* Iterate a side-effecting function over all elements.
   No intermediate list. *)
let iter f q =
  iter_internal f q


(* ── Dequeue utilities ─────────────────────────────────────── *)

(* Dequeue up to n elements from the front.
   Returns (dequeued_list, remaining_queue).
   Materializes once and splits, instead of calling dequeue in a loop
   which triggers repeated check/rebalance. *)
let dequeue_n n q =
  if n <= 0 then ([], q)
  else
    let elems = to_list q in
    let rec split_at acc k = function
      | rest when k <= 0 -> (List.rev acc, rest)
      | [] -> (List.rev acc, [])
      | x :: rest -> split_at (x :: acc) (k - 1) rest
    in
    let (taken, remaining) = split_at [] (min n q.len) elems in
    (taken, of_list remaining)

(* Drop up to n elements from the front. *)
let drop n q =
  let (_, q') = dequeue_n n q in
  q'

(* Take up to n elements from the front without removing them. *)
let take n q =
  let (elems, _) = dequeue_n n q in
  elems


(* ── Reversal and rotation ─────────────────────────────────── *)

(* Reverse the queue (last becomes first). *)
let rev q = of_list (List.rev (to_list q))

(* Rotate the queue: move the front element to the back.
   rotate [1;2;3] → [2;3;1] *)
let rotate q =
  match dequeue q with
  | (Some x, q') -> enqueue x q'
  | (None, q')   -> q'

(* Rotate n times. *)
let rotate_n n q =
  let n = n mod (max 1 q.len) in
  let rec go q count =
    if count <= 0 then q
    else go (rotate q) (count - 1)
  in
  go q n


(* ── Comparison and search ─────────────────────────────────── *)

(* Two queues are equal if they contain the same elements in order.
   Iterates front then rear of each queue in lockstep, avoiding
   intermediate list allocation. *)
let equal eq q1 q2 =
  if q1.len <> q2.len then false
  else
    (* Materialise only when lengths match — unavoidable for
       element-wise comparison across split representations. *)
    List.for_all2 eq (to_list q1) (to_list q2)

(* Check if the queue contains an element (using structural equality).
   Short-circuits — no intermediate list. *)
let mem x q =
  find_map_internal (fun y -> if y = x then Some () else None) q <> None

(* Return the element at position i (0-indexed from front).
   Walks front then rear without materializing a combined list. *)
let nth q i =
  if i < 0 || i >= q.len then None
  else
    let front_len = List.length q.front in
    if i < front_len then Some (List.nth q.front i)
    else
      (* Element is in the rear; rear is stored reversed, so index
         into (List.rev rear) at position (i - front_len). *)
      let rear_idx = i - front_len in
      let rear_len = List.length q.rear in
      Some (List.nth q.rear (rear_len - 1 - rear_idx))


(* ── Pretty printing ──────────────────────────────────────── *)

(* Convert queue to string using a per-element formatter. *)
let to_string f q =
  let elems = to_list q in
  "<" ^ String.concat ", " (List.map f elems) ^ ">"

(* Specialised for int queues. *)
let to_string_int q = to_string string_of_int q


(* ── Demo ──────────────────────────────────────────────────── *)

let () =
  Printf.printf "=== Purely Functional Queue (Banker's Queue) ===\n\n";

  (* Basic operations *)
  let q = empty in
  Printf.printf "Empty queue: %s (length=%d)\n" (to_string_int q) (length q);

  let q = enqueue 1 q in
  let q = enqueue 2 q in
  let q = enqueue 3 q in
  let q = enqueue 4 q in
  let q = enqueue 5 q in
  Printf.printf "After enqueue 1..5: %s (length=%d)\n" (to_string_int q) (length q);

  let v = peek q in
  Printf.printf "Peek: %s\n" (match v with Some x -> string_of_int x | None -> "empty");

  let (v, q2) = dequeue_exn q in
  Printf.printf "Dequeue: got %d, remaining: %s\n" v (to_string_int q2);

  let (v, q3) = dequeue_exn q2 in
  Printf.printf "Dequeue: got %d, remaining: %s\n" v (to_string_int q3);

  (* Persistence demo *)
  Printf.printf "\n--- Persistence ---\n";
  let orig = of_list [10; 20; 30] in
  let modified = enqueue 40 orig in
  Printf.printf "Original:  %s\n" (to_string_int orig);
  Printf.printf "Modified:  %s\n" (to_string_int modified);
  Printf.printf "Original unchanged? %b\n" (length orig = 3);

  (* Batch operations *)
  Printf.printf "\n--- Batch Operations ---\n";
  let q = of_list [1; 2; 3; 4; 5; 6; 7; 8; 9; 10] in
  let doubled = map (fun x -> x * 2) q in
  Printf.printf "Doubled: %s\n" (to_string_int doubled);

  let evens = filter (fun x -> x mod 2 = 0) q in
  Printf.printf "Evens:   %s\n" (to_string_int evens);

  let sum = fold_left (+) 0 q in
  Printf.printf "Sum:     %d\n" sum;

  (* Dequeue N *)
  Printf.printf "\n--- Dequeue N ---\n";
  let (batch, rest) = dequeue_n 3 q in
  Printf.printf "Dequeued 3: %s\n" (String.concat ", " (List.map string_of_int batch));
  Printf.printf "Remaining:  %s\n" (to_string_int rest);

  (* Rotation *)
  Printf.printf "\n--- Rotation ---\n";
  let q = of_list [1; 2; 3; 4; 5] in
  Printf.printf "Original:   %s\n" (to_string_int q);
  Printf.printf "Rotate 1:   %s\n" (to_string_int (rotate q));
  Printf.printf "Rotate 3:   %s\n" (to_string_int (rotate_n 3 q));

  (* Reversal *)
  Printf.printf "\n--- Reversal ---\n";
  let q = of_list [1; 2; 3; 4; 5] in
  Printf.printf "Original:  %s\n" (to_string_int q);
  Printf.printf "Reversed:  %s\n" (to_string_int (rev q));

  (* Append *)
  Printf.printf "\n--- Append ---\n";
  let q1 = of_list [1; 2; 3] in
  let q2 = of_list [4; 5; 6] in
  let combined = append q1 q2 in
  Printf.printf "%s ++ %s = %s\n" (to_string_int q1) (to_string_int q2) (to_string_int combined);

  (* Search *)
  Printf.printf "\n--- Search ---\n";
  let q = of_list [10; 20; 30; 40; 50] in
  Printf.printf "Contains 30? %b\n" (mem 30 q);
  Printf.printf "Contains 99? %b\n" (mem 99 q);
  Printf.printf "Any > 40?    %b\n" (exists (fun x -> x > 40) q);
  Printf.printf "All > 0?     %b\n" (for_all (fun x -> x > 0) q);
  Printf.printf "Find even:   %s\n"
    (match find_opt (fun x -> x mod 2 = 0) q with
     | Some x -> string_of_int x
     | None -> "none");
  Printf.printf "Element at index 2: %s\n"
    (match nth q 2 with Some x -> string_of_int x | None -> "none");

  Printf.printf "\n✅ Functional Queue demo complete!\n"
