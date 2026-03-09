(* ========================================================================= *)
(*  HAMT -- Hash Array Mapped Trie                                          *)
(*                                                                          *)
(*  A persistent (immutable, structurally-shared) hash map based on the     *)
(*  Hash Array Mapped Trie invented by Phil Bagwell (2001).                 *)
(*                                                                          *)
(*  Key ideas:                                                              *)
(*  - 32-way branching at each level using 5-bit hash chunks               *)
(*  - Bitmap compression: only allocate slots for occupied branches         *)
(*  - Structural sharing on insert/remove for persistence                   *)
(*  - O(log32 n) ≈ O(1) lookup, insert, remove for practical sizes        *)
(*                                                                          *)
(*  Features:                                                               *)
(*  - Polymorphic keys with custom hash/equality                            *)
(*  - Full map API: find, mem, add, remove, update, merge                   *)
(*  - Iteration: fold, iter, map, filter, to_list, of_list                  *)
(*  - Set operations via merge: union, intersection, difference             *)
(*  - Transient (mutable) builder for efficient batch construction          *)
(*  - Statistics: depth histogram, collision count, node count              *)
(* ========================================================================= *)

(* -- Bit manipulation helpers -- *)

let popcount (x : int) : int =
  let rec go n count =
    if n = 0 then count
    else go (n land (n - 1)) (count + 1)
  in go (x land 0x7FFFFFFF) 0

let bit_index (bitmap : int) (bit : int) : int =
  popcount (bitmap land (bit - 1))

(* -- Core types -- *)

let bits_per_level = 5
let branch_factor = 1 lsl bits_per_level   (* 32 *)
let mask = branch_factor - 1

type ('k, 'v) node =
  | Empty
  | Leaf of int * 'k * 'v
  | Collision of int * ('k * 'v) list
  | Branch of int * ('k, 'v) node array  (* bitmap, children *)

type ('k, 'v) config = {
  hash : 'k -> int;
  equal : 'k -> 'k -> bool;
}

type ('k, 'v) t = {
  config : ('k, 'v) config;
  root : ('k, 'v) node;
  size : int;
}

(* -- Hash utilities -- *)

let hash_fragment (hash : int) (shift : int) : int =
  (hash lsr shift) land mask

let bit_pos (hash : int) (shift : int) : int =
  1 lsl (hash_fragment hash shift)

(* -- Node operations -- *)

let rec node_find (cfg : ('k, 'v) config) (hash : int) (shift : int) (key : 'k) (node : ('k, 'v) node) : 'v option =
  match node with
  | Empty -> None
  | Leaf (h, k, v) ->
    if h = hash && cfg.equal k key then Some v else None
  | Collision (h, pairs) ->
    if h <> hash then None
    else
      let rec find_in = function
        | [] -> None
        | (k, v) :: rest -> if cfg.equal k key then Some v else find_in rest
      in find_in pairs
  | Branch (bitmap, children) ->
    let bit = bit_pos hash shift in
    if bitmap land bit = 0 then None
    else
      let idx = bit_index bitmap bit in
      node_find cfg hash (shift + bits_per_level) key children.(idx)

let clone_array (arr : 'a array) : 'a array =
  Array.init (Array.length arr) (fun i -> arr.(i))

let array_insert (arr : 'a array) (idx : int) (value : 'a) : 'a array =
  let len = Array.length arr in
  let new_arr = Array.make (len + 1) value in
  for i = 0 to idx - 1 do new_arr.(i) <- arr.(i) done;
  new_arr.(idx) <- value;
  for i = idx to len - 1 do new_arr.(i + 1) <- arr.(i) done;
  new_arr

let array_remove (arr : 'a array) (idx : int) : 'a array =
  let len = Array.length arr in
  if len = 1 then [||]
  else begin
    let new_arr = Array.make (len - 1) arr.(0) in
    for i = 0 to idx - 1 do new_arr.(i) <- arr.(i) done;
    for i = idx + 1 to len - 1 do new_arr.(i - 1) <- arr.(i) done;
    new_arr
  end

let array_update (arr : 'a array) (idx : int) (value : 'a) : 'a array =
  let new_arr = clone_array arr in
  new_arr.(idx) <- value;
  new_arr

let rec make_two_leaf (cfg : ('k, 'v) config) (shift : int) (h1 : int) (k1 : 'k) (v1 : 'v) (h2 : int) (k2 : 'k) (v2 : 'v) : ('k, 'v) node =
  if shift > 30 then
    if cfg.equal k1 k2 then Leaf (h1, k2, v2)
    else Collision (h1, [(k2, v2); (k1, v1)])
  else
    let f1 = hash_fragment h1 shift in
    let f2 = hash_fragment h2 shift in
    if f1 = f2 then
      let child = make_two_leaf cfg (shift + bits_per_level) h1 k1 v1 h2 k2 v2 in
      Branch (1 lsl f1, [|child|])
    else begin
      let b1 = 1 lsl f1 in
      let b2 = 1 lsl f2 in
      let bitmap = b1 lor b2 in
      let leaf1 = Leaf (h1, k1, v1) in
      let leaf2 = Leaf (h2, k2, v2) in
      if f1 < f2 then Branch (bitmap, [|leaf1; leaf2|])
      else Branch (bitmap, [|leaf2; leaf1|])
    end

let rec node_add (cfg : ('k, 'v) config) (hash : int) (shift : int) (key : 'k) (value : 'v) (node : ('k, 'v) node) : ('k, 'v) node * int =
  match node with
  | Empty -> (Leaf (hash, key, value), 1)
  | Leaf (h, k, v) ->
    if h = hash && cfg.equal k key then
      (Leaf (h, key, value), 0)
    else
      (make_two_leaf cfg shift h k v hash key value, 1)
  | Collision (h, pairs) ->
    if h = hash then begin
      let rec replace_or_add = function
        | [] -> [(key, value)]
        | (k, v) :: rest ->
          if cfg.equal k key then (key, value) :: rest
          else (k, v) :: replace_or_add rest
      in
      let new_pairs = replace_or_add pairs in
      let delta = if List.length new_pairs > List.length pairs then 1 else 0 in
      (Collision (h, new_pairs), delta)
    end else begin
      let col_node = Collision (h, pairs) in
      let leaf = Leaf (hash, key, value) in
      let f1 = hash_fragment h shift in
      let f2 = hash_fragment hash shift in
      if f1 = f2 then
        let child, _ = node_add cfg hash (shift + bits_per_level) key value col_node in
        (Branch (1 lsl f1, [|child|]), 1)
      else begin
        let b1 = 1 lsl f1 in
        let b2 = 1 lsl f2 in
        if f1 < f2 then (Branch (b1 lor b2, [|col_node; leaf|]), 1)
        else (Branch (b1 lor b2, [|leaf; col_node|]), 1)
      end
    end
  | Branch (bitmap, children) ->
    let bit = bit_pos hash shift in
    let idx = bit_index bitmap bit in
    if bitmap land bit = 0 then begin
      let new_children = array_insert children idx (Leaf (hash, key, value)) in
      (Branch (bitmap lor bit, new_children), 1)
    end else begin
      let child = children.(idx) in
      let new_child, delta = node_add cfg hash (shift + bits_per_level) key value child in
      let new_children = array_update children idx new_child in
      (Branch (bitmap, new_children), delta)
    end

let rec node_remove (cfg : ('k, 'v) config) (hash : int) (shift : int) (key : 'k) (node : ('k, 'v) node) : ('k, 'v) node * int =
  match node with
  | Empty -> (Empty, 0)
  | Leaf (h, k, _) ->
    if h = hash && cfg.equal k key then (Empty, -1)
    else (node, 0)
  | Collision (h, pairs) ->
    if h <> hash then (node, 0)
    else begin
      let new_pairs = List.filter (fun (k, _) -> not (cfg.equal k key)) pairs in
      let removed = List.length pairs - List.length new_pairs in
      if removed = 0 then (node, 0)
      else match new_pairs with
        | [] -> (Empty, -removed)
        | [(k, v)] -> (Leaf (h, k, v), -removed)
        | _ -> (Collision (h, new_pairs), -removed)
    end
  | Branch (bitmap, children) ->
    let bit = bit_pos hash shift in
    if bitmap land bit = 0 then (node, 0)
    else begin
      let idx = bit_index bitmap bit in
      let child = children.(idx) in
      let new_child, delta = node_remove cfg hash (shift + bits_per_level) key child in
      if delta = 0 then (node, 0)
      else match new_child with
        | Empty ->
          let new_bitmap = bitmap lxor bit in
          if new_bitmap = 0 then (Empty, delta)
          else begin
            let new_children = array_remove children idx in
            if Array.length new_children = 1 then
              match new_children.(0) with
              | Leaf _ | Collision _ -> (new_children.(0), delta)
              | _ -> (Branch (new_bitmap, new_children), delta)
            else (Branch (new_bitmap, new_children), delta)
          end
        | _ ->
          let new_children = array_update children idx new_child in
          (Branch (bitmap, new_children), delta)
    end

let rec node_fold (f : 'a -> 'k -> 'v -> 'a) (acc : 'a) (node : ('k, 'v) node) : 'a =
  match node with
  | Empty -> acc
  | Leaf (_, k, v) -> f acc k v
  | Collision (_, pairs) -> List.fold_left (fun a (k, v) -> f a k v) acc pairs
  | Branch (_, children) -> Array.fold_left (fun a child -> node_fold f a child) acc children

let rec node_iter (f : 'k -> 'v -> unit) (node : ('k, 'v) node) : unit =
  match node with
  | Empty -> ()
  | Leaf (_, k, v) -> f k v
  | Collision (_, pairs) -> List.iter (fun (k, v) -> f k v) pairs
  | Branch (_, children) -> Array.iter (fun child -> node_iter f child) children

let rec node_map (f : 'k -> 'v -> 'w) (node : ('k, 'v) node) : ('k, 'w) node =
  match node with
  | Empty -> Empty
  | Leaf (h, k, v) -> Leaf (h, k, f k v)
  | Collision (h, pairs) -> Collision (h, List.map (fun (k, v) -> (k, f k v)) pairs)
  | Branch (bitmap, children) ->
    Branch (bitmap, Array.map (fun child -> node_map f child) children)

let rec node_filter (cfg : ('k, 'v) config) (pred : 'k -> 'v -> bool) (node : ('k, 'v) node) : ('k, 'v) node * int =
  match node with
  | Empty -> (Empty, 0)
  | Leaf (_, k, v) ->
    if pred k v then (node, 0) else (Empty, -1)
  | Collision (h, pairs) ->
    let kept = List.filter (fun (k, v) -> pred k v) pairs in
    let removed = List.length pairs - List.length kept in
    if removed = 0 then (node, 0)
    else match kept with
      | [] -> (Empty, -removed)
      | [(k, v)] -> (Leaf (h, k, v), -removed)
      | _ -> (Collision (h, kept), -removed)
  | Branch (bitmap, children) ->
    let new_bitmap = ref bitmap in
    let total_delta = ref 0 in
    let len = Array.length children in
    let result = Array.make len Empty in
    let out_idx = ref 0 in
    let bits_seen = ref 0 in
    let cur_bitmap = ref bitmap in
    for i = 0 to len - 1 do
      while !cur_bitmap land (1 lsl !bits_seen) = 0 do
        bits_seen := !bits_seen + 1
      done;
      let bit = 1 lsl !bits_seen in
      let child = children.(i) in
      let new_child, delta = node_filter cfg pred child in
      total_delta := !total_delta + delta;
      (match new_child with
       | Empty -> new_bitmap := !new_bitmap lxor bit
       | _ ->
         result.(!out_idx) <- new_child;
         out_idx := !out_idx + 1);
      bits_seen := !bits_seen + 1
    done;
    if !new_bitmap = 0 then (Empty, !total_delta)
    else begin
      let final_arr = Array.sub result 0 !out_idx in
      if Array.length final_arr = 1 then
        match final_arr.(0) with
        | Leaf _ | Collision _ -> (final_arr.(0), !total_delta)
        | _ -> (Branch (!new_bitmap, final_arr), !total_delta)
      else (Branch (!new_bitmap, final_arr), !total_delta)
    end

(* -- Statistics -- *)

type stats = {
  node_count : int;
  leaf_count : int;
  collision_count : int;
  branch_count : int;
  max_depth : int;
  total_collision_entries : int;
  depth_histogram : (int * int) list;
}

let rec collect_stats (depth : int) (node : ('k, 'v) node) (acc : stats) : stats =
  match node with
  | Empty -> acc
  | Leaf _ ->
    let hist = (depth, 1) :: acc.depth_histogram in
    { acc with
      node_count = acc.node_count + 1;
      leaf_count = acc.leaf_count + 1;
      max_depth = max acc.max_depth depth;
      depth_histogram = hist }
  | Collision (_, pairs) ->
    let hist = (depth, List.length pairs) :: acc.depth_histogram in
    { acc with
      node_count = acc.node_count + 1;
      collision_count = acc.collision_count + 1;
      total_collision_entries = acc.total_collision_entries + List.length pairs;
      max_depth = max acc.max_depth depth;
      depth_histogram = hist }
  | Branch (_, children) ->
    let acc = { acc with
      node_count = acc.node_count + 1;
      branch_count = acc.branch_count + 1;
      max_depth = max acc.max_depth depth } in
    Array.fold_left (fun a child -> collect_stats (depth + 1) child a) acc children

let merge_histogram (hist : (int * int) list) : (int * int) list =
  let tbl = Hashtbl.create 16 in
  List.iter (fun (d, c) ->
    let cur = try Hashtbl.find tbl d with Not_found -> 0 in
    Hashtbl.replace tbl d (cur + c)
  ) hist;
  let pairs = Hashtbl.fold (fun d c acc -> (d, c) :: acc) tbl [] in
  List.sort compare pairs

(* -- Public API -- *)

let make ?(hash = Hashtbl.hash) ?(equal = (=)) () : ('k, 'v) t =
  { config = { hash; equal }; root = Empty; size = 0 }

let empty (cfg : ('k, 'v) config) : ('k, 'v) t =
  { config = cfg; root = Empty; size = 0 }

let is_empty (t : ('k, 'v) t) : bool = t.size = 0

let length (t : ('k, 'v) t) : int = t.size

let find (key : 'k) (t : ('k, 'v) t) : 'v option =
  let hash = t.config.hash key in
  node_find t.config hash 0 key t.root

let find_exn (key : 'k) (t : ('k, 'v) t) : 'v =
  match find key t with
  | Some v -> v
  | None -> raise Not_found

let mem (key : 'k) (t : ('k, 'v) t) : bool =
  find key t <> None

let add (key : 'k) (value : 'v) (t : ('k, 'v) t) : ('k, 'v) t =
  let hash = t.config.hash key in
  let new_root, delta = node_add t.config hash 0 key value t.root in
  { t with root = new_root; size = t.size + delta }

let remove (key : 'k) (t : ('k, 'v) t) : ('k, 'v) t =
  let hash = t.config.hash key in
  let new_root, delta = node_remove t.config hash 0 key t.root in
  { t with root = new_root; size = t.size + delta }

let update (key : 'k) (f : 'v option -> 'v option) (t : ('k, 'v) t) : ('k, 'v) t =
  match f (find key t) with
  | None -> remove key t
  | Some v -> add key v t

let fold (f : 'a -> 'k -> 'v -> 'a) (acc : 'a) (t : ('k, 'v) t) : 'a =
  node_fold f acc t.root

let iter (f : 'k -> 'v -> unit) (t : ('k, 'v) t) : unit =
  node_iter f t.root

let map (f : 'k -> 'v -> 'w) (t : ('k, 'v) t) : ('k, 'w) t =
  { config = { hash = t.config.hash; equal = t.config.equal };
    root = node_map f t.root;
    size = t.size }

let filter (pred : 'k -> 'v -> bool) (t : ('k, 'v) t) : ('k, 'v) t =
  let new_root, delta = node_filter t.config pred t.root in
  { t with root = new_root; size = t.size + delta }

let to_list (t : ('k, 'v) t) : ('k * 'v) list =
  fold (fun acc k v -> (k, v) :: acc) [] t

let of_list ?(hash = Hashtbl.hash) ?(equal = (=)) (pairs : ('k * 'v) list) : ('k, 'v) t =
  List.fold_left (fun acc (k, v) -> add k v acc) (make ~hash ~equal ()) pairs

let keys (t : ('k, 'v) t) : 'k list =
  fold (fun acc k _ -> k :: acc) [] t

let values (t : ('k, 'v) t) : 'v list =
  fold (fun acc _ v -> v :: acc) [] t

let for_all (pred : 'k -> 'v -> bool) (t : ('k, 'v) t) : bool =
  try
    iter (fun k v -> if not (pred k v) then raise Exit) t;
    true
  with Exit -> false

let exists (pred : 'k -> 'v -> bool) (t : ('k, 'v) t) : bool =
  try
    iter (fun k v -> if pred k v then raise Exit) t;
    false
  with Exit -> true

(* -- Merge / set operations -- *)

let merge (f : 'k -> 'v option -> 'w option -> 'x option) (t1 : ('k, 'v) t) (t2 : ('k, 'w) t) : ('k, 'x) t =
  let result = ref (make ~hash:t1.config.hash ~equal:t1.config.equal ()) in
  iter (fun k v ->
    let v2 = find k t2 in
    match f k (Some v) v2 with
    | Some x -> result := add k x !result
    | None -> ()
  ) t1;
  iter (fun k w ->
    if not (mem k t1) then
      match f k None (Some w) with
      | Some x -> result := add k x !result
      | None -> ()
  ) t2;
  !result

let union (t1 : ('k, 'v) t) (t2 : ('k, 'v) t) : ('k, 'v) t =
  fold (fun acc k v ->
    if mem k acc then acc else add k v acc
  ) t1 t2

let inter (t1 : ('k, 'v) t) (t2 : ('k, 'v) t) : ('k, 'v) t =
  filter (fun k _ -> mem k t2) t1

let diff (t1 : ('k, 'v) t) (t2 : ('k, 'v) t) : ('k, 'v) t =
  filter (fun k _ -> not (mem k t2)) t1

let symmetric_diff (t1 : ('k, 'v) t) (t2 : ('k, 'v) t) : ('k, 'v) t =
  let only1 = diff t1 t2 in
  let only2 = diff t2 t1 in
  union only1 only2

(* -- Equality -- *)

let equal (veq : 'v -> 'v -> bool) (t1 : ('k, 'v) t) (t2 : ('k, 'v) t) : bool =
  t1.size = t2.size &&
  for_all (fun k v ->
    match find k t2 with
    | Some v2 -> veq v v2
    | None -> false
  ) t1

(* -- Transient builder -- *)

module Transient = struct
  type ('k, 'v) builder = {
    mutable map : ('k, 'v) t;
  }

  let create ?(hash = Hashtbl.hash) ?(equal = (=)) () : ('k, 'v) builder =
    { map = make ~hash ~equal () }

  let of_hamt (t : ('k, 'v) t) : ('k, 'v) builder =
    { map = t }

  let add (key : 'k) (value : 'v) (b : ('k, 'v) builder) : unit =
    b.map <- add key value b.map

  let remove (key : 'k) (b : ('k, 'v) builder) : unit =
    b.map <- remove key b.map

  let find (key : 'k) (b : ('k, 'v) builder) : 'v option =
    find key b.map

  let length (b : ('k, 'v) builder) : int =
    b.map.size

  let persist (b : ('k, 'v) builder) : ('k, 'v) t =
    b.map
end

(* -- Statistics -- *)

let stats (t : ('k, 'v) t) : stats =
  let empty_stats = {
    node_count = 0; leaf_count = 0; collision_count = 0;
    branch_count = 0; max_depth = 0; total_collision_entries = 0;
    depth_histogram = [];
  } in
  let s = collect_stats 0 t.root empty_stats in
  { s with depth_histogram = merge_histogram s.depth_histogram }

let pp_stats (s : stats) : string =
  let buf = Buffer.create 256 in
  Printf.bprintf buf "HAMT Statistics:\n";
  Printf.bprintf buf "  Nodes: %d (branches: %d, leaves: %d, collisions: %d)\n"
    s.node_count s.branch_count s.leaf_count s.collision_count;
  Printf.bprintf buf "  Max depth: %d\n" s.max_depth;
  if s.collision_count > 0 then
    Printf.bprintf buf "  Collision entries: %d\n" s.total_collision_entries;
  Printf.bprintf buf "  Depth histogram:\n";
  List.iter (fun (d, c) ->
    Printf.bprintf buf "    depth %d: %d entries\n" d c
  ) s.depth_histogram;
  Buffer.contents buf


(* ========================================================================= *)
(*  Tests                                                                    *)
(* ========================================================================= *)

let tests_passed = ref 0
let tests_failed = ref 0

let assert_test (name : string) (condition : bool) : unit =
  if condition then begin
    incr tests_passed;
    Printf.printf "  ✓ %s\n" name
  end else begin
    incr tests_failed;
    Printf.printf "  ✗ FAIL: %s\n" name
  end

let () = Printf.printf "\n=== HAMT (Hash Array Mapped Trie) Tests ===\n\n"

(* -- Basic operations -- *)
let () =
  Printf.printf "Basic operations:\n";
  let m = make () in
  assert_test "empty map has size 0" (length m = 0);
  assert_test "empty map is_empty" (is_empty m);

  let m = add "hello" 1 m in
  assert_test "add one -> size 1" (length m = 1);
  assert_test "find added key" (find "hello" m = Some 1);
  assert_test "mem added key" (mem "hello" m);
  assert_test "find missing key" (find "world" m = None);
  assert_test "not mem missing" (not (mem "world" m));

  let m = add "world" 2 m in
  assert_test "add second -> size 2" (length m = 2);
  assert_test "find both keys" (find "hello" m = Some 1 && find "world" m = Some 2);

  let m2 = add "hello" 42 m in
  assert_test "replace keeps size" (length m2 = 2);
  assert_test "replace updates value" (find "hello" m2 = Some 42);
  assert_test "original unchanged" (find "hello" m = Some 1);
  ()

(* -- Remove -- *)
let () =
  Printf.printf "\nRemove:\n";
  let m = of_list [("a", 1); ("b", 2); ("c", 3)] in
  assert_test "of_list size" (length m = 3);

  let m2 = remove "b" m in
  assert_test "remove decrements size" (length m2 = 2);
  assert_test "removed key gone" (find "b" m2 = None);
  assert_test "other keys remain" (find "a" m2 = Some 1 && find "c" m2 = Some 3);

  let m3 = remove "missing" m in
  assert_test "remove missing is no-op" (length m3 = 3);

  let m4 = remove "a" (remove "b" (remove "c" m)) in
  assert_test "remove all -> empty" (is_empty m4);
  ()

(* -- Many entries -- *)
let () =
  Printf.printf "\nScaling:\n";
  let n = 1000 in
  let m = ref (make ()) in
  for i = 0 to n - 1 do
    m := add i (i * 10) !m
  done;
  assert_test "1000 entries size" (length !m = n);

  let all_found = ref true in
  for i = 0 to n - 1 do
    if find i !m <> Some (i * 10) then all_found := false
  done;
  assert_test "all 1000 found" !all_found;

  for i = 0 to 499 do
    m := remove i !m
  done;
  assert_test "removed half -> 500" (length !m = 500);

  let remaining_ok = ref true in
  for i = 500 to 999 do
    if find i !m <> Some (i * 10) then remaining_ok := false
  done;
  assert_test "remaining 500 correct" !remaining_ok;
  ()

(* -- Update -- *)
let () =
  Printf.printf "\nUpdate:\n";
  let m = of_list [("x", 10)] in
  let m2 = update "x" (function Some v -> Some (v + 5) | None -> None) m in
  assert_test "update existing" (find "x" m2 = Some 15);

  let m3 = update "y" (function None -> Some 99 | Some v -> Some v) m in
  assert_test "update insert" (find "y" m3 = Some 99 && length m3 = 2);

  let m4 = update "x" (fun _ -> None) m in
  assert_test "update remove" (is_empty m4);
  ()

(* -- Fold, iter, map, filter -- *)
let () =
  Printf.printf "\nHigher-order:\n";
  let m = of_list [(1, 10); (2, 20); (3, 30)] in

  let sum = fold (fun acc _ v -> acc + v) 0 m in
  assert_test "fold sum" (sum = 60);

  let count = ref 0 in
  iter (fun _ _ -> incr count) m;
  assert_test "iter count" (!count = 3);

  let m2 = map (fun _ v -> v * 2) m in
  assert_test "map doubles" (find 1 m2 = Some 20 && find 2 m2 = Some 40);

  let m3 = filter (fun k _ -> k > 1) m in
  assert_test "filter" (length m3 = 2 && not (mem 1 m3));
  ()

(* -- to_list, keys, values -- *)
let () =
  Printf.printf "\nConversions:\n";
  let m = of_list [("a", 1); ("b", 2); ("c", 3)] in
  let lst = to_list m in
  assert_test "to_list length" (List.length lst = 3);
  assert_test "to_list contains all" (
    List.mem ("a", 1) lst && List.mem ("b", 2) lst && List.mem ("c", 3) lst
  );

  let ks = List.sort compare (keys m) in
  assert_test "keys" (ks = ["a"; "b"; "c"]);

  let vs = List.sort compare (values m) in
  assert_test "values" (vs = [1; 2; 3]);
  ()

(* -- for_all, exists -- *)
let () =
  Printf.printf "\nPredicates:\n";
  let m = of_list [(1, 2); (3, 4); (5, 6)] in
  assert_test "for_all even values" (for_all (fun _ v -> v mod 2 = 0) m);
  assert_test "not for_all even keys" (not (for_all (fun k _ -> k mod 2 = 0) m));
  assert_test "exists key=3" (exists (fun k _ -> k = 3) m);
  assert_test "not exists key=99" (not (exists (fun k _ -> k = 99) m));
  ()

(* -- Set operations -- *)
let () =
  Printf.printf "\nSet operations:\n";
  let m1 = of_list [("a", 1); ("b", 2); ("c", 3)] in
  let m2 = of_list [("b", 20); ("c", 30); ("d", 40)] in

  let u = union m1 m2 in
  assert_test "union size" (length u = 4);
  assert_test "union prefers left" (find "b" u = Some 20);

  let i = inter m1 m2 in
  assert_test "inter size" (length i = 2);
  assert_test "inter keys" (mem "b" i && mem "c" i && not (mem "a" i));

  let d = diff m1 m2 in
  assert_test "diff" (length d = 1 && mem "a" d);

  let sd = symmetric_diff m1 m2 in
  assert_test "symmetric_diff" (length sd = 2 && mem "a" sd && mem "d" sd);
  ()

(* -- Merge -- *)
let () =
  Printf.printf "\nMerge:\n";
  let m1 = of_list [(1, "a"); (2, "b")] in
  let m2 = of_list [(2, "B"); (3, "c")] in
  let merged = merge (fun _k v1 v2 ->
    match v1, v2 with
    | Some a, Some b -> Some (a ^ "+" ^ b)
    | Some a, None -> Some a
    | None, Some b -> Some b
    | None, None -> None
  ) m1 m2 in
  assert_test "merge size" (length merged = 3);
  assert_test "merge combines" (find 2 merged = Some "b+B");
  assert_test "merge left-only" (find 1 merged = Some "a");
  assert_test "merge right-only" (find 3 merged = Some "c");
  ()

(* -- Equality -- *)
let () =
  Printf.printf "\nEquality:\n";
  let m1 = of_list [(1, "a"); (2, "b")] in
  let m2 = of_list [(2, "b"); (1, "a")] in
  let m3 = of_list [(1, "a"); (2, "c")] in
  assert_test "equal same entries" (equal (=) m1 m2);
  assert_test "not equal different values" (not (equal (=) m1 m3));
  assert_test "equal empty" (equal (=) (make ()) (make ()));
  ()

(* -- Persistence / structural sharing -- *)
let () =
  Printf.printf "\nPersistence:\n";
  let m0 = of_list [(1, "a"); (2, "b"); (3, "c")] in
  let m1 = add 4 "d" m0 in
  let m2 = remove 2 m0 in
  assert_test "original unchanged after add" (length m0 = 3 && find 4 m0 = None);
  assert_test "original unchanged after remove" (find 2 m0 = Some "b");
  assert_test "new version has add" (length m1 = 4 && find 4 m1 = Some "d");
  assert_test "new version has remove" (length m2 = 2 && find 2 m2 = None);
  ()

(* -- Transient builder -- *)
let () =
  Printf.printf "\nTransient builder:\n";
  let b = Transient.create () in
  Transient.add "x" 1 b;
  Transient.add "y" 2 b;
  Transient.add "z" 3 b;
  assert_test "builder length" (Transient.length b = 3);
  assert_test "builder find" (Transient.find "y" b = Some 2);

  Transient.remove "y" b;
  assert_test "builder remove" (Transient.length b = 2);

  let m = Transient.persist b in
  assert_test "persist correct" (length m = 2 && find "x" m = Some 1);

  let b2 = Transient.of_hamt m in
  Transient.add "w" 4 b2;
  let m2 = Transient.persist b2 in
  assert_test "of_hamt builder" (length m2 = 3);
  assert_test "original map unchanged" (length m = 2);
  ()

(* -- Custom hash/equal -- *)
let () =
  Printf.printf "\nCustom hash:\n";
  let ci_hash s = Hashtbl.hash (String.lowercase_ascii s) in
  let ci_equal a b = String.lowercase_ascii a = String.lowercase_ascii b in
  let m = make ~hash:ci_hash ~equal:ci_equal () in
  let m = add "Hello" 1 m in
  assert_test "custom: find exact" (find "Hello" m = Some 1);
  assert_test "custom: find different case" (find "hello" m = Some 1);
  assert_test "custom: find HELLO" (find "HELLO" m = Some 1);

  let m = add "HELLO" 2 m in
  assert_test "custom: replace via different case" (length m = 1 && find "hello" m = Some 2);
  ()

(* -- Hash collisions -- *)
let () =
  Printf.printf "\nHash collisions:\n";
  let bad_hash _ = 42 in
  let m = make ~hash:bad_hash () in
  let m = add "a" 1 m in
  let m = add "b" 2 m in
  let m = add "c" 3 m in
  assert_test "collision: all found" (
    find "a" m = Some 1 && find "b" m = Some 2 && find "c" m = Some 3
  );
  assert_test "collision: size" (length m = 3);

  let m2 = remove "b" m in
  assert_test "collision: remove" (length m2 = 2 && find "b" m2 = None);
  assert_test "collision: others remain" (find "a" m2 = Some 1 && find "c" m2 = Some 3);

  let m3 = add "a" 100 m in
  assert_test "collision: replace" (length m3 = 3 && find "a" m3 = Some 100);
  ()

(* -- Statistics -- *)
let () =
  Printf.printf "\nStatistics:\n";
  let m = ref (make ()) in
  for i = 0 to 99 do m := add i i !m done;
  let s = stats !m in
  assert_test "stats: leaf_count = 100" (s.leaf_count = 100);
  assert_test "stats: branches > 0" (s.branch_count > 0);
  assert_test "stats: max_depth reasonable" (s.max_depth <= 7);
  assert_test "stats: histogram non-empty" (s.depth_histogram <> []);

  let txt = pp_stats s in
  assert_test "pp_stats non-empty" (String.length txt > 50);
  ()

(* -- find_exn -- *)
let () =
  Printf.printf "\nfind_exn:\n";
  let m = of_list [("x", 42)] in
  assert_test "find_exn found" (find_exn "x" m = 42);
  let raised = try ignore (find_exn "y" m); false with Not_found -> true in
  assert_test "find_exn raises Not_found" raised;
  ()

(* -- Edge cases -- *)
let () =
  Printf.printf "\nEdge cases:\n";
  let m = make () in
  let m2 = remove "nope" m in
  assert_test "remove from empty" (is_empty m2);

  let m = of_list [(0, "zero")] in
  assert_test "zero key works" (find 0 m = Some "zero");

  let neg_hash _ = -999999 in
  let m = make ~hash:neg_hash () in
  let m = add "a" 1 m in
  assert_test "negative hash works" (find "a" m = Some 1);
  ()

(* -- Summary -- *)
let () =
  Printf.printf "\n=== Results: %d passed, %d failed ===\n" !tests_passed !tests_failed;
  if !tests_failed > 0 then exit 1
