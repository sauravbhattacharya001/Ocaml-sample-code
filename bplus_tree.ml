(* B+ Tree implementation *)
(* Demonstrates: algebraic data types, recursive algorithms, database-style indexing *)
(* A B+ Tree differs from a B-Tree in that:
   - All data/values are stored only in leaf nodes
   - Internal nodes store only keys for routing
   - Leaf nodes are linked together for efficient range queries
   - This makes sequential access and range scans very fast *)

(* We use a mutable linked-list at leaf level for simplicity *)

type ('k, 'v) leaf = {
  mutable leaf_keys: 'k array;
  mutable leaf_vals: 'v array;
  mutable leaf_count: int;
  mutable next_leaf: ('k, 'v) leaf option;
}

type 'k internal = {
  mutable int_keys: 'k array;
  mutable int_count: int;  (* number of keys; children = int_count + 1 *)
  mutable children: 'k node array;
}

and 'k node =
  | Leaf of ('k, string) leaf
  | Internal of 'k internal

type 'k bplus_tree = {
  mutable root: 'k node;
  order: int;  (* max keys per node *)
}

(* ---- Creation ---- *)

let create_leaf order =
  { leaf_keys = Array.make order (Obj.magic 0);
    leaf_vals = Array.make order "";
    leaf_count = 0;
    next_leaf = None }

let create ~order =
  if order < 3 then invalid_arg "B+ Tree order must be >= 3";
  { root = Leaf (create_leaf order); order }

(* ---- Leaf operations ---- *)

let leaf_find_pos keys count key =
  (* Binary search for insertion position *)
  let lo = ref 0 and hi = ref (count - 1) in
  while !lo <= !hi do
    let mid = (!lo + !hi) / 2 in
    if compare keys.(mid) key < 0 then lo := mid + 1
    else hi := mid - 1
  done;
  !lo

let leaf_search leaf key =
  let pos = leaf_find_pos leaf.leaf_keys leaf.leaf_count key in
  if pos < leaf.leaf_count && compare leaf.leaf_keys.(pos) key = 0 then
    Some leaf.leaf_vals.(pos)
  else
    None

let leaf_insert leaf key value order =
  let pos = leaf_find_pos leaf.leaf_keys leaf.leaf_count key in
  (* Update if key exists *)
  if pos < leaf.leaf_count && compare leaf.leaf_keys.(pos) key = 0 then begin
    leaf.leaf_vals.(pos) <- value;
    None  (* no split needed *)
  end else if leaf.leaf_count < order then begin
    (* Shift right and insert *)
    for i = leaf.leaf_count - 1 downto pos do
      leaf.leaf_keys.(i + 1) <- leaf.leaf_keys.(i);
      leaf.leaf_vals.(i + 1) <- leaf.leaf_vals.(i)
    done;
    leaf.leaf_keys.(pos) <- key;
    leaf.leaf_vals.(pos) <- value;
    leaf.leaf_count <- leaf.leaf_count + 1;
    None
  end else begin
    (* Need to split: create temp arrays with all keys + new key *)
    let all_keys = Array.make (order + 1) (Obj.magic 0) in
    let all_vals = Array.make (order + 1) "" in
    let j = ref 0 in
    for i = 0 to order - 1 do
      if i = pos then begin
        all_keys.(!j) <- key;
        all_vals.(!j) <- value;
        incr j
      end;
      all_keys.(!j) <- leaf.leaf_keys.(i);
      all_vals.(!j) <- leaf.leaf_vals.(i);
      incr j
    done;
    if pos = order then begin
      all_keys.(!j) <- key;
      all_vals.(!j) <- value
    end;
    let total = order + 1 in
    let mid = total / 2 in
    (* Left half stays in current leaf *)
    leaf.leaf_count <- mid;
    for i = 0 to mid - 1 do
      leaf.leaf_keys.(i) <- all_keys.(i);
      leaf.leaf_vals.(i) <- all_vals.(i)
    done;
    (* Right half goes to new leaf *)
    let new_leaf = create_leaf order in
    new_leaf.leaf_count <- total - mid;
    for i = 0 to new_leaf.leaf_count - 1 do
      new_leaf.leaf_keys.(i) <- all_keys.(mid + i);
      new_leaf.leaf_vals.(i) <- all_vals.(mid + i)
    done;
    new_leaf.next_leaf <- leaf.next_leaf;
    leaf.next_leaf <- Some new_leaf;
    (* Promote first key of new leaf *)
    Some (new_leaf.leaf_keys.(0), Leaf new_leaf)
  end

(* ---- Internal node operations ---- *)

let create_internal order =
  { int_keys = Array.make (order) (Obj.magic 0);
    int_count = 0;
    children = Array.make (order + 1) (Leaf (create_leaf order)) }

let internal_find_child node key =
  let pos = ref 0 in
  while !pos < node.int_count && compare node.int_keys.(!pos) key <= 0 do
    incr pos
  done;
  !pos

let internal_insert_key node pos key child order =
  if node.int_count < order then begin
    for i = node.int_count - 1 downto pos do
      node.int_keys.(i + 1) <- node.int_keys.(i);
      node.children.(i + 2) <- node.children.(i + 1)
    done;
    node.int_keys.(pos) <- key;
    node.children.(pos + 1) <- child;
    node.int_count <- node.int_count + 1;
    None
  end else begin
    (* Split internal node *)
    let all_keys = Array.make (order + 1) (Obj.magic 0) in
    let all_children = Array.make (order + 2) (Leaf (create_leaf order)) in
    let j = ref 0 in
    for i = 0 to order - 1 do
      if i = pos then begin
        all_keys.(!j) <- key;
        all_children.(!j + 1) <- child;
        incr j
      end;
      all_keys.(!j) <- node.int_keys.(i);
      all_children.(!j + 1) <- node.children.(i + 1);
      incr j
    done;
    if pos = order then begin
      all_keys.(!j) <- key;
      all_children.(!j + 1) <- child
    end;
    all_children.(0) <- node.children.(0);
    let total = order + 1 in
    let mid = total / 2 in
    let promote_key = all_keys.(mid) in
    (* Left half stays *)
    node.int_count <- mid;
    node.children.(0) <- all_children.(0);
    for i = 0 to mid - 1 do
      node.int_keys.(i) <- all_keys.(i);
      node.children.(i + 1) <- all_children.(i + 1)
    done;
    (* Right half in new node *)
    let new_node = create_internal order in
    new_node.int_count <- total - mid - 1;
    new_node.children.(0) <- all_children.(mid + 1);
    for i = 0 to new_node.int_count - 1 do
      new_node.int_keys.(i) <- all_keys.(mid + 1 + i);
      new_node.children.(i + 1) <- all_children.(mid + 2 + i)
    done;
    Some (promote_key, Internal new_node)
  end

(* ---- Public API ---- *)

let search tree key =
  let rec go = function
    | Leaf l -> leaf_search l key
    | Internal n ->
      let pos = internal_find_child n key in
      go n.children.(pos)
  in
  go tree.root

let insert tree key value =
  let rec go node =
    match node with
    | Leaf l -> leaf_insert l key value tree.order
    | Internal n ->
      let pos = internal_find_child n key in
      match go n.children.(pos) with
      | None -> None
      | Some (promoted_key, new_child) ->
        internal_insert_key n pos promoted_key new_child tree.order
  in
  match go tree.root with
  | None -> ()
  | Some (promoted_key, new_child) ->
    let new_root = create_internal tree.order in
    new_root.children.(0) <- tree.root;
    new_root.int_keys.(0) <- promoted_key;
    new_root.children.(1) <- new_child;
    new_root.int_count <- 1;
    tree.root <- Internal new_root

(* Range query: find all key-value pairs where lo <= key <= hi *)
let range_query tree lo hi =
  let rec find_leaf = function
    | Leaf l -> l
    | Internal n ->
      let pos = internal_find_child n lo in
      find_leaf n.children.(pos)
  in
  let leaf = find_leaf tree.root in
  let results = ref [] in
  let rec scan l =
    for i = 0 to l.leaf_count - 1 do
      if compare l.leaf_keys.(i) lo >= 0 && compare l.leaf_keys.(i) hi <= 0 then
        results := (l.leaf_keys.(i), l.leaf_vals.(i)) :: !results
    done;
    if l.leaf_count > 0 && compare l.leaf_keys.(l.leaf_count - 1) hi < 0 then
      match l.next_leaf with
      | Some next -> scan next
      | None -> ()
  in
  scan leaf;
  List.rev !results

(* Count total keys *)
let count tree =
  let rec first_leaf = function
    | Leaf l -> l
    | Internal n -> first_leaf n.children.(0)
  in
  let leaf = first_leaf tree.root in
  let total = ref 0 in
  let rec scan l =
    total := !total + l.leaf_count;
    match l.next_leaf with
    | Some next -> scan next
    | None -> ()
  in
  scan leaf;
  !total

(* Get all key-value pairs in order (via leaf scan) *)
let to_list tree =
  let rec first_leaf = function
    | Leaf l -> l
    | Internal n -> first_leaf n.children.(0)
  in
  let leaf = first_leaf tree.root in
  let results = ref [] in
  let rec scan l =
    for i = 0 to l.leaf_count - 1 do
      results := (l.leaf_keys.(i), l.leaf_vals.(i)) :: !results
    done;
    match l.next_leaf with
    | Some next -> scan next
    | None -> ()
  in
  scan leaf;
  List.rev !results

(* Height of the tree *)
let height tree =
  let rec go = function
    | Leaf _ -> 1
    | Internal n -> 1 + go n.children.(0)
  in
  go tree.root

(* Pretty-print tree structure *)
let pp tree =
  let buf = Buffer.create 256 in
  let rec go indent = function
    | Leaf l ->
      Buffer.add_string buf (String.make indent ' ');
      Buffer.add_string buf "Leaf[";
      for i = 0 to l.leaf_count - 1 do
        if i > 0 then Buffer.add_string buf ", ";
        Buffer.add_string buf (Printf.sprintf "%s=%s"
          (string_of_int (Obj.magic l.leaf_keys.(i)))
          l.leaf_vals.(i))
      done;
      Buffer.add_string buf "]\n"
    | Internal n ->
      Buffer.add_string buf (String.make indent ' ');
      Buffer.add_string buf "Internal[";
      for i = 0 to n.int_count - 1 do
        if i > 0 then Buffer.add_string buf ", ";
        Buffer.add_string buf (string_of_int (Obj.magic n.int_keys.(i)))
      done;
      Buffer.add_string buf "]\n";
      for i = 0 to n.int_count do
        go (indent + 2) n.children.(i)
      done
  in
  go 0 tree.root;
  Buffer.contents buf

(* ---- Demo ---- *)

let () =
  Printf.printf "=== B+ Tree Demo ===\n\n";

  let tree = create ~order:4 in

  (* Insert some data *)
  let data = [
    (10, "ten"); (20, "twenty"); (5, "five"); (15, "fifteen");
    (25, "twenty-five"); (30, "thirty"); (1, "one"); (7, "seven");
    (12, "twelve"); (17, "seventeen"); (22, "twenty-two");
    (27, "twenty-seven"); (3, "three"); (8, "eight"); (35, "thirty-five")
  ] in

  List.iter (fun (k, v) ->
    insert tree k v;
    Printf.printf "Inserted %d -> %s\n" k v
  ) data;

  Printf.printf "\nTree height: %d\n" (height tree);
  Printf.printf "Total keys: %d\n" (count tree);

  (* Search *)
  Printf.printf "\n--- Searches ---\n";
  List.iter (fun k ->
    match search tree k with
    | Some v -> Printf.printf "search(%d) = %s\n" k v
    | None -> Printf.printf "search(%d) = not found\n" k
  ) [5; 15; 25; 99];

  (* Range query *)
  Printf.printf "\n--- Range Query [10, 25] ---\n";
  let range = range_query tree 10 25 in
  List.iter (fun (k, v) ->
    Printf.printf "  %d -> %s\n" k v
  ) range;

  (* All entries in order *)
  Printf.printf "\n--- All entries (leaf scan) ---\n";
  let all = to_list tree in
  List.iter (fun (k, v) ->
    Printf.printf "  %d -> %s\n" k v
  ) all;

  (* Update existing key *)
  Printf.printf "\n--- Update key 10 ---\n";
  insert tree 10 "TEN (updated)";
  (match search tree 10 with
   | Some v -> Printf.printf "search(10) = %s\n" v
   | None -> Printf.printf "search(10) = not found\n");

  Printf.printf "\n--- Tree Structure ---\n";
  print_string (pp tree);

  Printf.printf "\nDone!\n"
