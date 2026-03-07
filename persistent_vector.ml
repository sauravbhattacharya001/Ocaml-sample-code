(* Persistent Vector — Clojure-Style Immutable Array with Structural Sharing *)
(* Demonstrates: polymorphism, recursive algebraic data types, bit manipulation,
   persistent (immutable) data structures, structural sharing, tail optimization,
   higher-order functions, amortized complexity analysis *)

(* A persistent vector provides:
   - O(log32 n) random access (get)
   - O(log32 n) functional update (set — returns new vector, original unchanged)
   - O(1) amortized append (push_back via tail buffer)
   - O(1) length
   - Structural sharing: modified vectors share most of their tree with originals

   Internally it's a wide branching trie (branching factor 32) indexed by
   position bits. The rightmost "tail" chunk is stored separately for fast
   appends. This is the same design used by Clojure's PersistentVector
   and Scala's immutable.Vector.

   Branching factor of 32 means:
   - Trees are very shallow (depth 7 handles 32^7 = 34 billion elements)
   - Cache-friendly array nodes (32 elements fit in ~256 bytes)
   - "Effectively O(1)" for all practical sizes *)

(* --- Constants --- *)
let bits = 5                  (* log2(branching_factor) *)
let branching = 1 lsl bits    (* 32 *)
let mask = branching - 1      (* 0x1F = 31 *)

(* --- Trie node --- *)
(* Internal nodes hold an array of children; leaves hold an array of values.
   We represent both with a polymorphic variant to keep it clean. *)
type 'a node =
  | Leaf of 'a array
  | Internal of 'a node array

(* --- The vector --- *)
type 'a t = {
  cnt    : int;         (* total element count *)
  shift  : int;         (* bits of depth: 5 for 1 level, 10 for 2, etc. *)
  root   : 'a node;     (* trie root *)
  tail   : 'a array;    (* rightmost partial chunk, not yet in the trie *)
}

(* --- Helpers --- *)

(* How many elements are stored in the trie (everything except the tail) *)
let tail_offset v =
  if v.cnt < branching then 0
  else ((v.cnt - 1) lsr bits) lsl bits

(* Copy an array and set one element — pure functional update *)
let array_set a i x =
  let a' = Array.copy a in
  a'.(i) <- x;
  a'

(* Copy an array and append one element *)
let array_push a x =
  let n = Array.length a in
  let a' = Array.make (n + 1) x in
  Array.blit a 0 a' 0 n;
  a'

(* --- Empty vector --- *)
let empty : 'a t = {
  cnt = 0;
  shift = bits;
  root = Internal [||];
  tail = [||];
}

(* --- Length --- *)
let length v = v.cnt

(* --- Get: O(log32 n) --- *)
(* Walk down the trie using 5-bit chunks of the index *)
let get v i =
  if i < 0 || i >= v.cnt then
    invalid_arg (Printf.sprintf "Persistent_vector.get: index %d out of bounds (length %d)" i v.cnt)
  else if i >= tail_offset v then
    (* It's in the tail *)
    v.tail.(i land mask)
  else begin
    (* Walk the trie *)
    let node = ref v.root in
    let level = ref v.shift in
    while !level > 0 do
      (match !node with
       | Internal children ->
         node := children.((i lsr !level) land mask)
       | Leaf _ ->
         failwith "Persistent_vector.get: unexpected Leaf in trie interior");
      level := !level - bits
    done;
    match !node with
    | Leaf arr -> arr.(i land mask)
    | Internal _ -> failwith "Persistent_vector.get: expected Leaf at bottom"
  end

(* --- Set: O(log32 n), returns new vector --- *)
let set v i x =
  if i < 0 || i >= v.cnt then
    invalid_arg (Printf.sprintf "Persistent_vector.set: index %d out of bounds (length %d)" i v.cnt)
  else if i >= tail_offset v then
    (* Update in the tail *)
    { v with tail = array_set v.tail (i land mask) x }
  else begin
    (* Functionally update the trie path *)
    let rec do_set node level =
      if level = 0 then
        match node with
        | Leaf arr -> Leaf (array_set arr (i land mask) x)
        | Internal _ -> failwith "Persistent_vector.set: expected Leaf at level 0"
      else
        match node with
        | Internal children ->
          let sub_idx = (i lsr level) land mask in
          Internal (array_set children sub_idx (do_set children.(sub_idx) (level - bits)))
        | Leaf _ -> failwith "Persistent_vector.set: expected Internal above level 0"
    in
    { v with root = do_set v.root v.shift }
  end

(* --- Push_back: amortized O(1) --- *)
(* If the tail has room, just extend it.
   Otherwise, push the full tail into the trie and start a new tail. *)
let push_back v x =
  if Array.length v.tail < branching then
    (* Room in tail — just append *)
    { v with cnt = v.cnt + 1; tail = array_push v.tail x }
  else begin
    (* Tail is full: push it into the trie *)
    let tail_node = Leaf v.tail in
    let rec push_tail node level =
      if level = bits then
        (* Bottom internal level: insert the leaf *)
        match node with
        | Internal children -> Internal (array_push children tail_node)
        | Leaf _ -> failwith "push_tail: expected Internal"
      else
        match node with
        | Internal children ->
          let sub_idx = ((v.cnt - 1) lsr level) land mask in
          if sub_idx < Array.length children then
            (* Path exists — recurse *)
            Internal (array_set children sub_idx
                       (push_tail children.(sub_idx) (level - bits)))
          else
            (* New path needed *)
            Internal (array_push children (new_path (level - bits) tail_node))
        | Leaf _ -> failwith "push_tail: expected Internal"
    and new_path level node =
      if level = 0 then node
      else Internal [| new_path (level - bits) node |]
    in
    (* Check if we need to grow the tree depth *)
    let overflow = (v.cnt lsr bits) > (1 lsl v.shift) in
    if overflow then
      (* Root overflow: create new root with old root + new path *)
      let new_root = Internal [|
        v.root;
        new_path (v.shift) tail_node
      |] in
      { cnt = v.cnt + 1; shift = v.shift + bits; root = new_root; tail = [| x |] }
    else
      { cnt = v.cnt + 1; shift = v.shift; root = push_tail v.root v.shift; tail = [| x |] }
  end

(* --- Pop_back: O(log32 n) --- *)
(* Remove the last element. Returns the new vector and the removed element. *)
let pop_back v =
  if v.cnt = 0 then
    invalid_arg "Persistent_vector.pop_back: empty vector"
  else if v.cnt = 1 then
    (empty, v.tail.(0))
  else if Array.length v.tail > 1 then
    (* Just shrink the tail *)
    let x = v.tail.(Array.length v.tail - 1) in
    let tail' = Array.sub v.tail 0 (Array.length v.tail - 1) in
    ({ v with cnt = v.cnt - 1; tail = tail' }, x)
  else begin
    (* Tail has exactly 1 element — need to pull last leaf from trie *)
    let x = v.tail.(0) in
    (* Find the new tail: the rightmost leaf in the trie *)
    let new_tail_idx = v.cnt - 2 in  (* last element of new vector *)
    let rec find_leaf node level =
      if level = 0 then
        match node with
        | Leaf arr -> arr
        | Internal _ -> failwith "pop_back: expected Leaf"
      else
        match node with
        | Internal children ->
          find_leaf children.((new_tail_idx lsr level) land mask) (level - bits)
        | Leaf _ -> failwith "pop_back: expected Internal"
    in
    let new_tail = find_leaf v.root v.shift in
    (* Remove the rightmost path from the trie *)
    let rec pop_trie node level =
      if level = bits then
        match node with
        | Internal children ->
          if Array.length children = 1 then None
          else Some (Internal (Array.sub children 0 (Array.length children - 1)))
        | Leaf _ -> failwith "pop_trie: expected Internal"
      else
        match node with
        | Internal children ->
          let sub_idx = ((v.cnt - 2) lsr level) land mask in
          match pop_trie children.(sub_idx) (level - bits) with
          | None ->
            if Array.length children = 1 then None
            else Some (Internal (Array.sub children 0 (Array.length children - 1)))
          | Some child' ->
            Some (Internal (array_set children sub_idx child'))
        | Leaf _ -> failwith "pop_trie: expected Internal"
    in
    let root', shift' =
      match pop_trie v.root v.shift with
      | None -> (Internal [||], bits)
      | Some (Internal [| single |]) when v.shift > bits ->
        (* Root has single child — lower the tree *)
        (single, v.shift - bits)
      | Some r -> (r, v.shift)
    in
    ({ cnt = v.cnt - 1; shift = shift'; root = root'; tail = new_tail }, x)
  end

(* --- Convenience constructors --- *)

(* Build from a list *)
let of_list lst =
  List.fold_left push_back empty lst

(* Build from an array *)
let of_array arr =
  Array.fold_left push_back empty arr

(* Convert to list *)
let to_list v =
  let acc = ref [] in
  for i = v.cnt - 1 downto 0 do
    acc := get v i :: !acc
  done;
  !acc

(* Convert to array *)
let to_array v =
  if v.cnt = 0 then [||]
  else
    let a = Array.make v.cnt (get v 0) in
    for i = 1 to v.cnt - 1 do
      a.(i) <- get v i
    done;
    a

(* --- Higher-order operations --- *)

(* Map: apply f to every element, return new vector *)
let map f v =
  let rec map_node = function
    | Leaf arr -> Leaf (Array.map f arr)
    | Internal children -> Internal (Array.map map_node children)
  in
  { v with root = map_node v.root; tail = Array.map f v.tail }

(* Fold left over all elements in order *)
let fold_left f init v =
  let acc = ref init in
  for i = 0 to v.cnt - 1 do
    acc := f !acc (get v i)
  done;
  !acc

(* Fold right over all elements *)
let fold_right f v init =
  let acc = ref init in
  for i = v.cnt - 1 downto 0 do
    acc := f (get v i) !acc
  done;
  !acc

(* Iterate over elements *)
let iter f v =
  for i = 0 to v.cnt - 1 do
    f (get v i)
  done

(* Iterate with index *)
let iteri f v =
  for i = 0 to v.cnt - 1 do
    f i (get v i)
  done

(* Filter elements *)
let filter pred v =
  fold_left (fun acc x -> if pred x then push_back acc x else acc) empty v

(* Check if any element satisfies predicate *)
let exists pred v =
  let found = ref false in
  let i = ref 0 in
  while not !found && !i < v.cnt do
    if pred (get v !i) then found := true;
    incr i
  done;
  !found

(* Check if all elements satisfy predicate *)
let for_all pred v =
  let ok = ref true in
  let i = ref 0 in
  while !ok && !i < v.cnt do
    if not (pred (get v !i)) then ok := false;
    incr i
  done;
  !ok

(* Find first element satisfying predicate *)
let find_opt pred v =
  let result = ref None in
  let i = ref 0 in
  while !result = None && !i < v.cnt do
    let x = get v !i in
    if pred x then result := Some x;
    incr i
  done;
  !result

(* --- Slicing --- *)

(* Extract a sub-vector from index [start] to [stop) *)
let sub v start stop =
  if start < 0 || stop > v.cnt || start > stop then
    invalid_arg (Printf.sprintf "Persistent_vector.sub: invalid range [%d, %d) for length %d" start stop v.cnt);
  let result = ref empty in
  for i = start to stop - 1 do
    result := push_back !result (get v i)
  done;
  !result

(* Concatenate two vectors *)
let append v1 v2 =
  let result = ref v1 in
  for i = 0 to v2.cnt - 1 do
    result := push_back !result (get v2 i)
  done;
  !result

(* Reverse a vector *)
let rev v =
  let result = ref empty in
  for i = v.cnt - 1 downto 0 do
    result := push_back !result (get v i)
  done;
  !result

(* --- Equality and comparison --- *)

let equal eq v1 v2 =
  if v1.cnt <> v2.cnt then false
  else
    let ok = ref true in
    let i = ref 0 in
    while !ok && !i < v1.cnt do
      if not (eq (get v1 !i) (get v2 !i)) then ok := false;
      incr i
    done;
    !ok

(* --- Pretty printing --- *)

let pp pp_elem v =
  Printf.printf "[|";
  for i = 0 to v.cnt - 1 do
    if i > 0 then Printf.printf "; ";
    pp_elem (get v i)
  done;
  Printf.printf "|]"

let pp_int v = pp (Printf.printf "%d") v
let pp_string v = pp (Printf.printf "%S") v

(* --- Transient (batch mutation optimization) --- *)
(* For bulk operations, a transient allows in-place mutation of a copy,
   then "freezes" back into a persistent vector. This avoids creating
   intermediate path copies during batch inserts. *)

type 'a transient = {
  mutable t_cnt   : int;
  mutable t_shift : int;
  mutable t_root  : 'a node;
  mutable t_tail  : 'a array;
  mutable t_tail_len : int;
  mutable frozen  : bool;
}

let transient_of v =
  let tail_copy = Array.make branching (Obj.magic 0) in
  Array.blit v.tail 0 tail_copy 0 (Array.length v.tail);
  { t_cnt = v.cnt;
    t_shift = v.shift;
    t_root = v.root;  (* shares structure — will copy-on-write *)
    t_tail = tail_copy;
    t_tail_len = Array.length v.tail;
    frozen = false }

let transient_push t x =
  if t.frozen then failwith "Persistent_vector: transient is frozen";
  if t.t_tail_len < branching then begin
    t.t_tail.(t.t_tail_len) <- x;
    t.t_tail_len <- t.t_tail_len + 1;
    t.t_cnt <- t.t_cnt + 1
  end else begin
    (* Flush the tail into the trie, start new tail *)
    let full_tail = Leaf (Array.sub t.t_tail 0 branching) in
    let rec push node level =
      if level = bits then
        match node with
        | Internal children -> Internal (array_push children full_tail)
        | Leaf _ -> failwith "transient_push: expected Internal"
      else
        match node with
        | Internal children ->
          let sub_idx = ((t.t_cnt - 1) lsr level) land mask in
          if sub_idx < Array.length children then
            Internal (array_set children sub_idx (push children.(sub_idx) (level - bits)))
          else
            Internal (array_push children (new_path (level - bits) full_tail))
        | Leaf _ -> failwith "transient_push: expected Internal"
    and new_path level node =
      if level = 0 then node
      else Internal [| new_path (level - bits) node |]
    in
    let overflow = (t.t_cnt lsr bits) > (1 lsl t.t_shift) in
    if overflow then begin
      t.t_root <- Internal [| t.t_root; new_path t.t_shift full_tail |];
      t.t_shift <- t.t_shift + bits
    end else
      t.t_root <- push t.t_root t.t_shift;
    t.t_tail <- Array.make branching (Obj.magic 0);
    t.t_tail.(0) <- x;
    t.t_tail_len <- 1;
    t.t_cnt <- t.t_cnt + 1
  end

let persistent_of t =
  if t.frozen then failwith "Persistent_vector: transient already frozen";
  t.frozen <- true;
  { cnt = t.t_cnt;
    shift = t.t_shift;
    root = t.t_root;
    tail = Array.sub t.t_tail 0 t.t_tail_len }

(* Convenience: build from a large list efficiently *)
let of_list_fast lst =
  let t = transient_of empty in
  List.iter (transient_push t) lst;
  persistent_of t


(* =========================================================== *)
(*                        DEMO / TESTS                         *)
(* =========================================================== *)
let () =
  print_endline "=== Persistent Vector ===";
  print_endline "";

  (* --- Basic operations --- *)
  print_endline "--- Basic push_back & get ---";
  let v = empty in
  let v = push_back v 10 in
  let v = push_back v 20 in
  let v = push_back v 30 in
  Printf.printf "length: %d\n" (length v);   (* 3 *)
  Printf.printf "v[0] = %d\n" (get v 0);     (* 10 *)
  Printf.printf "v[1] = %d\n" (get v 1);     (* 20 *)
  Printf.printf "v[2] = %d\n" (get v 2);     (* 30 *)
  print_newline ();

  (* --- Functional update --- *)
  print_endline "--- Functional set (structural sharing) ---";
  let v2 = set v 1 99 in
  Printf.printf "v[1]  = %d (original unchanged)\n" (get v 1);   (* 20 *)
  Printf.printf "v2[1] = %d (updated copy)\n" (get v2 1);        (* 99 *)
  print_newline ();

  (* --- Building a larger vector --- *)
  print_endline "--- Building 1000-element vector ---";
  let big = ref empty in
  for i = 0 to 999 do
    big := push_back !big i
  done;
  Printf.printf "length: %d\n" (length !big);
  Printf.printf "big[0]   = %d\n" (get !big 0);
  Printf.printf "big[500] = %d\n" (get !big 500);
  Printf.printf "big[999] = %d\n" (get !big 999);
  print_newline ();

  (* --- pop_back --- *)
  print_endline "--- Pop back ---";
  let (v3, x) = pop_back v in
  Printf.printf "popped: %d, remaining length: %d\n" x (length v3);
  Printf.printf "v3[0] = %d, v3[1] = %d\n" (get v3 0) (get v3 1);
  print_newline ();

  (* --- of_list / to_list --- *)
  print_endline "--- of_list / to_list ---";
  let from_list = of_list [1; 2; 3; 4; 5] in
  Printf.printf "from list: ";
  pp_int from_list;
  print_newline ();
  let back = to_list from_list in
  Printf.printf "to list: [%s]\n"
    (String.concat "; " (List.map string_of_int back));
  print_newline ();

  (* --- map --- *)
  print_endline "--- Map (double each element) ---";
  let doubled = map (fun x -> x * 2) from_list in
  Printf.printf "doubled: ";
  pp_int doubled;
  print_newline ();
  print_newline ();

  (* --- fold --- *)
  print_endline "--- Fold (sum) ---";
  let sum = fold_left ( + ) 0 from_list in
  Printf.printf "sum of [1..5]: %d\n" sum;  (* 15 *)
  print_newline ();

  (* --- filter --- *)
  print_endline "--- Filter (evens only) ---";
  let evens = filter (fun x -> x mod 2 = 0) (of_list [1; 2; 3; 4; 5; 6; 7; 8]) in
  Printf.printf "evens: ";
  pp_int evens;
  print_newline ();
  print_newline ();

  (* --- find / exists / for_all --- *)
  print_endline "--- Predicates ---";
  let nums = of_list [3; 7; 11; 15; 20] in
  Printf.printf "exists (>10): %b\n" (exists (fun x -> x > 10) nums);
  Printf.printf "for_all (>0): %b\n" (for_all (fun x -> x > 0) nums);
  Printf.printf "find (even): %s\n"
    (match find_opt (fun x -> x mod 2 = 0) nums with
     | Some x -> string_of_int x
     | None -> "none");
  print_newline ();

  (* --- sub / append / rev --- *)
  print_endline "--- Slicing ---";
  let abc = of_list [10; 20; 30; 40; 50] in
  let middle = sub abc 1 4 in
  Printf.printf "sub [1,4): "; pp_int middle; print_newline ();
  let combined = append (of_list [1; 2]) (of_list [3; 4]) in
  Printf.printf "append: "; pp_int combined; print_newline ();
  let reversed = rev (of_list [1; 2; 3]) in
  Printf.printf "rev: "; pp_int reversed; print_newline ();
  print_newline ();

  (* --- Equality --- *)
  print_endline "--- Equality ---";
  let a = of_list [1; 2; 3] in
  let b = of_list [1; 2; 3] in
  let c = of_list [1; 2; 4] in
  Printf.printf "[1;2;3] = [1;2;3]: %b\n" (equal ( = ) a b);
  Printf.printf "[1;2;3] = [1;2;4]: %b\n" (equal ( = ) a c);
  print_newline ();

  (* --- Transient (batch) --- *)
  print_endline "--- Transient (batch build) ---";
  let fast = of_list_fast [1; 2; 3; 4; 5; 6; 7; 8; 9; 10] in
  Printf.printf "fast build: "; pp_int fast; print_newline ();
  Printf.printf "length: %d\n" (length fast);
  print_newline ();

  (* --- Persistence verification --- *)
  print_endline "--- Persistence check ---";
  let orig = of_list [100; 200; 300] in
  let mod1 = set orig 0 999 in
  let mod2 = push_back orig 400 in
  let (mod3, _) = pop_back orig in
  Printf.printf "orig:  "; pp_int orig; print_newline ();
  Printf.printf "mod1:  "; pp_int mod1; print_newline ();
  Printf.printf "mod2:  "; pp_int mod2; print_newline ();
  Printf.printf "mod3:  "; pp_int mod3; print_newline ();
  Printf.printf "orig unchanged: %b\n" (to_list orig = [100; 200; 300]);
  print_newline ();

  (* --- Large vector stress test --- *)
  print_endline "--- Stress test (10,000 elements via transient) ---";
  let t = transient_of empty in
  for i = 0 to 9999 do transient_push t i done;
  let large = persistent_of t in
  Printf.printf "length: %d\n" (length large);
  Printf.printf "large[0]    = %d\n" (get large 0);
  Printf.printf "large[5000] = %d\n" (get large 5000);
  Printf.printf "large[9999] = %d\n" (get large 9999);
  let large' = set large 5000 (-1) in
  Printf.printf "after set 5000: large[5000]=%d, large'[5000]=%d\n"
    (get large 5000) (get large' 5000);
  print_newline ();

  (* --- Polymorphic usage --- *)
  print_endline "--- Polymorphic (strings) ---";
  let words = of_list ["hello"; "persistent"; "vector"; "world"] in
  Printf.printf "words: "; pp_string words; print_newline ();
  let upper = map String.uppercase_ascii words in
  Printf.printf "upper: "; pp_string upper; print_newline ();
  Printf.printf "concat: %s\n" (fold_left (fun a s -> a ^ " " ^ s) "" words |> String.trim);
  print_newline ();

  (* --- Edge cases --- *)
  print_endline "--- Edge cases ---";
  Printf.printf "empty length: %d\n" (length empty);
  let single = push_back empty 42 in
  Printf.printf "single: "; pp_int single; print_newline ();
  let (back_to_empty, popped) = pop_back single in
  Printf.printf "pop single: got %d, length now %d\n" popped (length back_to_empty);
  (try ignore (get empty 0); print_endline "ERROR: should have raised"
   with Invalid_argument msg -> Printf.printf "get empty: %s\n" msg);
  (try ignore (pop_back empty); print_endline "ERROR: should have raised"
   with Invalid_argument msg -> Printf.printf "pop empty: %s\n" msg);
  print_newline ();

  (* --- Summary --- *)
  print_endline "=== Summary ===";
  print_endline "Persistent Vector: Clojure-style immutable array";
  print_endline "  Branching factor: 32 (5-bit trie)";
  print_endline "  get/set:    O(log32 n) — effectively O(1) for practical sizes";
  print_endline "  push_back:  amortized O(1) via tail buffer";
  print_endline "  pop_back:   O(log32 n)";
  print_endline "  Structural sharing: modifications share most of the tree";
  print_endline "  Transient:  mutable batch builder, then freeze to persistent";
  print_endline "  Higher-order: map, fold, filter, iter, find, exists, for_all";
  print_endline "  Slicing: sub, append, rev, equal";
  print_endline "";
  print_endline "Key insight: wide branching (32) keeps trees shallow —";
  print_endline "  1M elements = 4 levels, 1B elements = 6 levels.";
  print_endline "  This makes 'O(log32 n)' practically constant for all";
  print_endline "  real-world data sizes."
