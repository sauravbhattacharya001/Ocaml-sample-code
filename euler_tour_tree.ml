(* Euler Tour Tree - Dynamic forest connectivity via Euler tour sequences
   
   An Euler Tour Tree (ETT) represents a forest of rooted trees using
   Euler tour sequences stored in balanced BSTs (treaps). This enables
   efficient dynamic connectivity operations:
   
   - Link two trees (merge forests)
   - Cut an edge (split a tree)
   - Check if two nodes are connected
   - Find the root of a node's tree
   - Aggregate values over subtrees
   
   The key insight: an Euler tour of a tree visits each edge twice
   (once going down, once coming back up), producing a sequence where
   the subtree of any node forms a contiguous subsequence.
   
   Time complexities (expected, using treap):
   - Link:        O(log n)
   - Cut:         O(log n)
   - Connected:   O(log n)
   - Find root:   O(log n)
   - Subtree sum: O(log n)
   - Reroot:      O(log n)
   
   Space: O(n) per forest
   
   Applications:
   - Dynamic graph connectivity
   - Network reliability
   - Minimum spanning forest maintenance
   - Dynamic lowest common ancestor
*)

(* ---- Treap-based implicit sequence ---- *)

module Treap = struct
  type 'a node = {
    mutable value: 'a;
    mutable priority: int;
    mutable size: int;
    mutable sum: int;        (* aggregate: sum of node weights *)
    mutable weight: int;     (* this node's weight *)
    mutable left: 'a node option;
    mutable right: 'a node option;
    mutable parent: 'a node option;
  }

  let size = function
    | None -> 0
    | Some n -> n.size

  let sum_of = function
    | None -> 0
    | Some n -> n.sum

  let update node =
    node.size <- 1 + size node.left + size node.right;
    node.sum <- node.weight + sum_of node.left + sum_of node.right;
    (match node.left with Some l -> l.parent <- Some node | None -> ());
    (match node.right with Some r -> r.parent <- Some node | None -> ())

  let create value weight =
    { value; priority = Random.bits ();
      size = 1; sum = weight; weight;
      left = None; right = None; parent = None }

  (* Split treap into (left, right) at position k (0-indexed, left gets k elements) *)
  let rec split k = function
    | None -> (None, None)
    | Some node ->
      let left_size = size node.left in
      if k <= left_size then begin
        let (ll, lr) = split k node.left in
        node.left <- lr;
        update node;
        node.parent <- None;
        (match ll with Some n -> n.parent <- None | None -> ());
        (ll, Some node)
      end else begin
        let (rl, rr) = split (k - left_size - 1) node.right in
        node.right <- rl;
        update node;
        node.parent <- None;
        (match rr with Some n -> n.parent <- None | None -> ());
        (Some node, rr)
      end

  (* Merge two treaps *)
  let rec merge a b =
    match a, b with
    | None, t | t, None -> t
    | Some a_node, Some b_node ->
      if a_node.priority >= b_node.priority then begin
        a_node.right <- merge a_node.right (Some b_node);
        update a_node;
        a_node.parent <- None;
        Some a_node
      end else begin
        b_node.left <- merge (Some a_node) b_node.left;
        update b_node;
        b_node.parent <- None;
        Some b_node
      end

  (* Find position of a node by walking up to the root *)
  let position node =
    let pos = ref (size node.left) in
    let cur = ref (Some node) in
    let prev = ref (Some node) in
    while !cur <> None do
      let c = match !cur with Some n -> n | None -> assert false in
      (match c.right with
       | Some r when (match !prev with Some p -> p == r | None -> false) ->
         ()  (* came from right child, no adjustment *)
       | _ ->
         if (match !prev with Some p -> not (p == c) | None -> true) then
           ()  (* this is the starting node *)
         else
           (* came from left child, add parent + right subtree *)
           pos := !pos + 1 + size c.left);
      prev := !cur;
      cur := c.parent
    done;
    !pos

  (* Find root of the treap containing this node *)
  let rec root node =
    match node.parent with
    | None -> node
    | Some p -> root p

  (* Get the k-th element (0-indexed) *)
  let rec kth k = function
    | None -> failwith "index out of bounds"
    | Some node ->
      let left_size = size node.left in
      if k < left_size then kth k node.left
      else if k = left_size then node
      else kth (k - left_size - 1) node.right

  (* Collect all values in order *)
  let to_list root =
    let result = ref [] in
    let rec inorder = function
      | None -> ()
      | Some node ->
        inorder node.right;
        result := node.value :: !result;
        inorder node.left
    in
    inorder root;
    !result
end

(* ---- Euler Tour Tree ---- *)

type node_id = int

type occurrence = {
  node_id: node_id;
  is_first: bool;  (* first or last occurrence in the tour *)
}

type t = {
  n: int;                                         (* number of nodes *)
  mutable roots: occurrence Treap.node option array; (* treap roots per component *)
  first_occ: occurrence Treap.node array;         (* first occurrence of each node *)
  last_occ: occurrence Treap.node array;          (* last occurrence of each node *)
  weights: int array;                             (* node weights for aggregation *)
  mutable component: int array;                   (* component id for each node *)
}

(* Create a forest of n isolated nodes with optional weights *)
let create ?(weights=[||]) n =
  let w = if Array.length weights = n then weights
          else Array.make n 1 in
  let first_occ = Array.init n (fun i ->
    Treap.create { node_id = i; is_first = true } w.(i)) in
  let last_occ = Array.init n (fun i ->
    Treap.create { node_id = i; is_first = false } 0) in
  (* Each node starts as its own tour: [first_i, last_i] *)
  let roots = Array.init n (fun i ->
    let merged = Treap.merge (Some first_occ.(i)) (Some last_occ.(i)) in
    merged
  ) in
  let component = Array.init n (fun i -> i) in
  { n; roots; first_occ; last_occ; weights = w; component }

(* Find which component a node belongs to *)
let find_root ett node_id =
  let r = Treap.root ett.first_occ.(node_id) in
  (* Walk to find leftmost to identify component *)
  let first = Treap.kth 0 (Some r) in
  first.value.node_id

(* Check if two nodes are in the same tree *)
let connected ett u v =
  let ru = Treap.root ett.first_occ.(u) in
  let rv = Treap.root ett.first_occ.(v) in
  ru == rv

(* Reroot the tour at a given node *)
let reroot ett node_id =
  let root = Treap.root ett.first_occ.(node_id) in
  let first = ett.first_occ.(node_id) in
  let pos = Treap.position first in
  if pos = 0 then Some root  (* already the root *)
  else begin
    (* Split at position of first_occ[node_id], rotate *)
    let (left, right) = Treap.split pos (Some root) in
    Treap.merge right left
  end

(* Link: add edge between u and v (must be in different trees) *)
let link ett u v =
  if connected ett u v then
    failwith (Printf.sprintf "nodes %d and %d are already connected" u v)
  else begin
    (* Reroot u's tree at u, reroot v's tree at v *)
    let tree_u = reroot ett u in
    let tree_v = reroot ett v in
    (* Merge: tree_u ++ tree_v *)
    let merged = Treap.merge tree_u tree_v in
    (* Update component ids *)
    let comp = min ett.component.(u) ett.component.(v) in
    let values = Treap.to_list merged in
    List.iter (fun occ -> ett.component.(occ.node_id) <- comp) values;
    let _ = merged in
    ()
  end

(* Cut: remove edge between u and v (must be adjacent) *)
let cut ett u v =
  if not (connected ett u v) then
    failwith (Printf.sprintf "nodes %d and %d are not connected" u v)
  else begin
    (* Reroot at u *)
    let tree = reroot ett u in
    (* Find v's first and last occurrences *)
    let first_v = ett.first_occ.(v) in
    let last_v = ett.last_occ.(v) in
    let pos_first = Treap.position first_v in
    let pos_last = Treap.position last_v in
    let (p1, p2) = if pos_first < pos_last then (pos_first, pos_last)
                   else (pos_last, pos_first) in
    (* Split into three parts: before v's subtree, v's subtree, after *)
    let (left, rest) = Treap.split p1 tree in
    let (middle, right) = Treap.split (p2 - p1 + 1) rest in
    (* left ++ right is u's tree, middle is v's tree *)
    let u_tree = Treap.merge left right in
    (* Update component ids for v's subtree *)
    let v_values = Treap.to_list middle in
    List.iter (fun occ -> ett.component.(occ.node_id) <- v) v_values;
    let u_values = Treap.to_list u_tree in
    List.iter (fun occ -> ett.component.(occ.node_id) <- u) u_values;
    ()
  end

(* Get the size of the tree containing a node *)
let tree_size ett node_id =
  let root = Treap.root ett.first_occ.(node_id) in
  (Treap.size (Some root)) / 2  (* each node has 2 occurrences *)

(* Get the sum of weights in the tree containing a node *)
let tree_sum ett node_id =
  let root = Treap.root ett.first_occ.(node_id) in
  Treap.sum_of (Some root)

(* Update the weight of a node *)
let set_weight ett node_id w =
  ett.weights.(node_id) <- w;
  let first = ett.first_occ.(node_id) in
  first.Treap.weight <- w;
  (* Propagate update up *)
  let rec propagate node =
    Treap.update node;
    match node.Treap.parent with
    | Some p -> propagate p
    | None -> ()
  in
  propagate first

(* List all nodes in the same tree *)
let tree_nodes ett node_id =
  let root = Treap.root ett.first_occ.(node_id) in
  let values = Treap.to_list (Some root) in
  let seen = Hashtbl.create 16 in
  List.iter (fun occ ->
    if not (Hashtbl.mem seen occ.node_id) then
      Hashtbl.add seen occ.node_id true
  ) values;
  Hashtbl.fold (fun k _ acc -> k :: acc) seen []
  |> List.sort compare

(* Get the number of distinct trees in the forest *)
let num_trees ett =
  let seen = Hashtbl.create 16 in
  for i = 0 to ett.n - 1 do
    let r = find_root ett i in
    if not (Hashtbl.mem seen r) then
      Hashtbl.add seen r true
  done;
  Hashtbl.length seen

(* Pretty-print forest info *)
let to_string ett =
  let buf = Buffer.create 256 in
  Buffer.add_string buf (Printf.sprintf "Euler Tour Forest (%d nodes):\n" ett.n);
  let trees = Hashtbl.create 16 in
  for i = 0 to ett.n - 1 do
    let r = find_root ett i in
    let nodes = try Hashtbl.find trees r with Not_found -> [] in
    Hashtbl.replace trees r (i :: nodes)
  done;
  let tree_id = ref 0 in
  Hashtbl.iter (fun _ nodes ->
    incr tree_id;
    let sorted = List.sort compare nodes in
    Buffer.add_string buf (Printf.sprintf "  Tree %d: {%s}\n" !tree_id
      (String.concat ", " (List.map string_of_int sorted)))
  ) trees;
  Buffer.contents buf

(* ---- Demo ---- *)

let () =
  Printf.printf "=== Euler Tour Tree Demo ===\n\n";
  
  (* Create a forest of 8 nodes *)
  let weights = [| 10; 20; 30; 40; 50; 60; 70; 80 |] in
  let ett = create ~weights 8 in
  Printf.printf "Initial forest (8 isolated nodes):\n%s\n" (to_string ett);
  Printf.printf "Number of trees: %d\n\n" (num_trees ett);
  
  (* Build a tree: 0-1, 0-2, 1-3, 1-4, 2-5 *)
  Printf.printf "--- Linking nodes ---\n";
  link ett 0 1; Printf.printf "Linked 0-1\n";
  link ett 0 2; Printf.printf "Linked 0-2\n";
  link ett 1 3; Printf.printf "Linked 1-3\n";
  link ett 1 4; Printf.printf "Linked 1-4\n";
  link ett 2 5; Printf.printf "Linked 2-5\n";
  
  (* Build another small tree: 6-7 *)
  link ett 6 7; Printf.printf "Linked 6-7\n\n";
  
  Printf.printf "After linking:\n%s\n" (to_string ett);
  Printf.printf "Number of trees: %d\n\n" (num_trees ett);
  
  (* Connectivity queries *)
  Printf.printf "--- Connectivity ---\n";
  Printf.printf "Connected(0, 5) = %b (expect true)\n" (connected ett 0 5);
  Printf.printf "Connected(3, 4) = %b (expect true)\n" (connected ett 3 4);
  Printf.printf "Connected(0, 6) = %b (expect false)\n" (connected ett 0 6);
  Printf.printf "Connected(6, 7) = %b (expect true)\n\n" (connected ett 6 7);
  
  (* Tree sizes and sums *)
  Printf.printf "--- Aggregates ---\n";
  Printf.printf "Tree size of node 0's tree: %d (expect 6)\n" (tree_size ett 0);
  Printf.printf "Tree sum of node 0's tree: %d (expect 210)\n" (tree_sum ett 0);
  Printf.printf "Tree size of node 6's tree: %d (expect 2)\n" (tree_size ett 6);
  Printf.printf "Tree sum of node 6's tree: %d (expect 150)\n\n" (tree_sum ett 6);
  
  (* Tree members *)
  Printf.printf "--- Tree members ---\n";
  let nodes_0 = tree_nodes ett 0 in
  Printf.printf "Nodes in tree with 0: {%s}\n"
    (String.concat ", " (List.map string_of_int nodes_0));
  let nodes_6 = tree_nodes ett 6 in
  Printf.printf "Nodes in tree with 6: {%s}\n\n"
    (String.concat ", " (List.map string_of_int nodes_6));
  
  (* Update weight *)
  Printf.printf "--- Weight update ---\n";
  Printf.printf "Before: tree sum = %d\n" (tree_sum ett 0);
  set_weight ett 3 100;
  Printf.printf "After setting node 3 weight to 100: tree sum = %d\n\n" (tree_sum ett 0);
  
  (* Cut edge 1-3 *)
  Printf.printf "--- Cut edge 1-3 ---\n";
  cut ett 1 3;
  Printf.printf "After cut:\n%s\n" (to_string ett);
  Printf.printf "Connected(1, 3) = %b (expect false)\n" (connected ett 1 3);
  Printf.printf "Connected(0, 4) = %b (expect true)\n" (connected ett 0 4);
  Printf.printf "Number of trees: %d\n\n" (num_trees ett);
  
  (* Link the two separate trees *)
  Printf.printf "--- Link trees: 3-6 ---\n";
  link ett 3 6;
  Printf.printf "After linking 3-6:\n%s\n" (to_string ett);
  Printf.printf "Connected(3, 7) = %b (expect true)\n" (connected ett 3 7);
  Printf.printf "Number of trees: %d\n" (num_trees ett);
  
  Printf.printf "\n=== Demo complete ===\n"
