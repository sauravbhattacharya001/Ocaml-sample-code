(* B-Tree implementation *)
(* Demonstrates: algebraic data types, recursive algorithms, balanced tree structures *)
(* A B-Tree of minimum degree t has these properties:
   - Every node has at most 2t-1 keys
   - Every non-root node has at least t-1 keys
   - All leaves appear at the same level
   - A non-leaf node with k keys has k+1 children *)

type 'a node = {
  keys: 'a list;
  children: 'a node list;
  leaf: bool;
}

type 'a btree = {
  root: 'a node;
  t: int;  (* minimum degree *)
}

(* Create an empty B-Tree with minimum degree t *)
let create ~t =
  if t < 2 then invalid_arg "B-Tree minimum degree must be >= 2";
  { root = { keys = []; children = []; leaf = true }; t }

(* Search for a key in the B-Tree *)
let rec search key node =
  let rec find_index keys i =
    match keys with
    | [] -> (i, false)
    | k :: _ when key = k -> (i, true)
    | k :: _ when key < k -> (i, false)
    | _ :: rest -> find_index rest (i + 1)
  in
  let (i, found) = find_index node.keys 0 in
  if found then true
  else if node.leaf then false
  else search key (List.nth node.children i)

(* Helper: split the i-th child of a node (child is full) *)
let split_child node i t =
  let child = List.nth node.children i in
  let mid = t - 1 in
  let median = List.nth child.keys mid in
  (* Left child gets keys[0..mid-1], right gets keys[mid+1..] *)
  let left_keys = List.filteri (fun j _ -> j < mid) child.keys in
  let right_keys = List.filteri (fun j _ -> j > mid) child.keys in
  let left_children, right_children =
    if child.leaf then ([], [])
    else
      let lc = List.filteri (fun j _ -> j <= mid) child.children in
      let rc = List.filteri (fun j _ -> j > mid) child.children in
      (lc, rc)
  in
  let left_node = { keys = left_keys; children = left_children; leaf = child.leaf } in
  let right_node = { keys = right_keys; children = right_children; leaf = child.leaf } in
  (* Insert median into parent's keys at position i *)
  let new_keys =
    let before = List.filteri (fun j _ -> j < i) node.keys in
    let after = List.filteri (fun j _ -> j >= i) node.keys in
    before @ [median] @ after
  in
  (* Replace child at i with left_node, insert right_node at i+1 *)
  let new_children =
    let before = List.filteri (fun j _ -> j < i) node.children in
    let after = List.filteri (fun j _ -> j > i) node.children in
    before @ [left_node; right_node] @ after
  in
  { keys = new_keys; children = new_children; leaf = node.leaf }

(* Insert a key into a non-full node *)
let rec insert_nonfull key node t =
  if node.leaf then begin
    (* Insert key into sorted position *)
    let rec ins = function
      | [] -> [key]
      | k :: rest when key <= k -> key :: k :: rest
      | k :: rest -> k :: ins rest
    in
    { node with keys = ins node.keys }
  end else begin
    (* Find child to recurse into *)
    let rec find_child keys i =
      match keys with
      | [] -> i
      | k :: _ when key < k -> i
      | _ :: rest -> find_child rest (i + 1)
    in
    let i = find_child node.keys 0 in
    let child = List.nth node.children i in
    let max_keys = 2 * t - 1 in
    if List.length child.keys = max_keys then begin
      (* Split full child first *)
      let node' = split_child node i t in
      (* Determine which of the two children to recurse into *)
      let median = List.nth node'.keys i in
      let ci = if key > median then i + 1 else i in
      let updated_child = insert_nonfull key (List.nth node'.children ci) t in
      { node' with children = List.mapi (fun j c -> if j = ci then updated_child else c) node'.children }
    end else begin
      let updated_child = insert_nonfull key child t in
      { node with children = List.mapi (fun j c -> if j = i then updated_child else c) node.children }
    end
  end

(* Insert a key into the B-Tree *)
let insert key btree =
  let max_keys = 2 * btree.t - 1 in
  if List.length btree.root.keys = max_keys then begin
    (* Root is full — create new root and split *)
    let new_root = { keys = []; children = [btree.root]; leaf = false } in
    let new_root = split_child new_root 0 btree.t in
    let new_root = insert_nonfull key new_root btree.t in
    { btree with root = new_root }
  end else
    { btree with root = insert_nonfull key btree.root btree.t }

(* In-order traversal — returns sorted list of all keys *)
let to_sorted_list btree =
  let rec traverse node =
    if node.leaf then node.keys
    else
      let pairs = List.combine node.children node.keys in
      let prefix =
        List.concat_map (fun (child, key) -> traverse child @ [key]) pairs
      in
      let last_child = List.nth node.children (List.length node.children - 1) in
      prefix @ traverse last_child
  in
  traverse btree.root

(* Count all keys in the tree *)
let size btree =
  let rec count node =
    let key_count = List.length node.keys in
    if node.leaf then key_count
    else key_count + List.fold_left (fun acc c -> acc + count c) 0 node.children
  in
  count btree.root

(* Height of the tree *)
let height btree =
  let rec h node =
    if node.leaf then 0
    else 1 + h (List.hd node.children)
  in
  h btree.root

(* Pretty-print the tree structure *)
let pp btree =
  let rec pp_node indent node =
    let prefix = String.make (indent * 2) ' ' in
    Printf.printf "%sKeys: [%s]\n" prefix
      (String.concat "; " (List.map string_of_int node.keys));
    if not node.leaf then
      List.iteri (fun i child ->
        Printf.printf "%sChild %d:\n" prefix i;
        pp_node (indent + 1) child
      ) node.children
  in
  Printf.printf "B-Tree (t=%d, size=%d, height=%d):\n" btree.t (size btree) (height btree);
  pp_node 1 btree.root

(* Demo *)
let () =
  Printf.printf "=== B-Tree Demo ===\n\n";

  (* Create a B-Tree with minimum degree 2 (2-3-4 tree) *)
  let tree = create ~t:2 in
  Printf.printf "Created empty B-Tree with t=2\n\n";

  (* Insert values *)
  let values = [10; 20; 5; 6; 12; 30; 7; 17; 3; 25; 35; 15; 1; 8; 22; 28; 40; 2; 4; 9] in
  let tree = List.fold_left (fun t v -> insert v t) tree values in

  Printf.printf "Inserted %d values\n" (List.length values);
  Printf.printf "Tree size: %d\n" (size tree);
  Printf.printf "Tree height: %d\n\n" (height tree);

  pp tree;
  Printf.printf "\n";

  (* Search *)
  Printf.printf "Search results:\n";
  List.iter (fun k ->
    Printf.printf "  search(%d) = %b\n" k (search k tree.root)
  ) [5; 17; 40; 11; 99];
  Printf.printf "\n";

  (* Sorted traversal *)
  let sorted = to_sorted_list tree in
  Printf.printf "In-order traversal: [%s]\n"
    (String.concat "; " (List.map string_of_int sorted));
  Printf.printf "\n";

  (* Larger tree with t=3 *)
  Printf.printf "=== Larger B-Tree (t=3) ===\n\n";
  let big = create ~t:3 in
  let big = List.fold_left (fun t v -> insert v t) big
    (List.init 50 (fun i -> i * 3 + 1)) in
  Printf.printf "Inserted 50 values, size=%d, height=%d\n" (size big) (height big);
  pp big
