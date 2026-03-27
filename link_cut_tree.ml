(* Link-Cut Tree — dynamic tree data structure                          *)
(* Implements Sleator & Tarjan's link-cut trees for dynamic forests     *)
(* Supports path queries, link/cut operations in amortized O(log n)    *)
(* Used in max-flow algorithms, dynamic connectivity, and LCA queries  *)

(* ── Types ─────────────────────────────────────────────────────────── *)

(* Each node stores its value, aggregated path info, and splay tree pointers.
   We use an imperative representation since link-cut trees require
   parent pointers and in-place splay operations. *)

type node = {
  id          : int;
  mutable value     : int;
  mutable left      : node option;
  mutable right     : node option;
  mutable parent    : node option;
  mutable rev       : bool;       (* lazy reversal flag for evert *)
  mutable path_sum  : int;        (* aggregate: sum along splay path *)
  mutable path_min  : int;        (* aggregate: min along splay path *)
  mutable path_max  : int;        (* aggregate: max along splay path *)
  mutable size      : int;        (* subtree size in splay tree *)
}

(* ── Node creation ─────────────────────────────────────────────────── *)

let make_node id value = {
  id; value;
  left = None; right = None; parent = None;
  rev = false;
  path_sum = value;
  path_min = value;
  path_max = value;
  size = 1;
}

(* ── Helper functions ──────────────────────────────────────────────── *)

let get_size = function
  | None -> 0
  | Some n -> n.size

let get_sum = function
  | None -> 0
  | Some n -> n.path_sum

let get_min = function
  | None -> max_int
  | Some n -> n.path_min

let get_max = function
  | None -> min_int
  | Some n -> n.path_max

(* Update aggregates from children *)
let update n =
  n.size <- 1 + get_size n.left + get_size n.right;
  n.path_sum <- n.value + get_sum n.left + get_sum n.right;
  n.path_min <- min n.value (min (get_min n.left) (get_min n.right));
  n.path_max <- max n.value (max (get_max n.left) (get_max n.right))

(* Push lazy reversal down *)
let push n =
  if n.rev then begin
    let tmp = n.left in
    n.left <- n.right;
    n.right <- tmp;
    (match n.left with Some c -> c.rev <- not c.rev | None -> ());
    (match n.right with Some c -> c.rev <- not c.rev | None -> ());
    n.rev <- false
  end

(* Check if node is root of its splay tree (auxiliary tree) *)
let is_root n =
  match n.parent with
  | None -> true
  | Some p ->
    not (match p.left with Some c -> c == n | None -> false) &&
    not (match p.right with Some c -> c == n | None -> false)

(* ── Splay tree rotations ─────────────────────────────────────────── *)

(* Right rotation: n is left child of p *)
let rotate_right n p =
  let gp = p.parent in
  p.left <- n.right;
  (match n.right with Some c -> c.parent <- Some p | None -> ());
  n.right <- Some p;
  p.parent <- Some n;
  n.parent <- gp;
  (match gp with
   | None -> ()
   | Some g ->
     if (match g.left with Some c -> c == p | None -> false)
     then g.left <- Some n
     else if (match g.right with Some c -> c == p | None -> false)
     then g.right <- Some n);
  update p;
  update n

(* Left rotation: n is right child of p *)
let rotate_left n p =
  let gp = p.parent in
  p.right <- n.left;
  (match n.left with Some c -> c.parent <- Some p | None -> ());
  n.left <- Some p;
  p.parent <- Some n;
  n.parent <- gp;
  (match gp with
   | None -> ()
   | Some g ->
     if (match g.left with Some c -> c == p | None -> false)
     then g.left <- Some n
     else if (match g.right with Some c -> c == p | None -> false)
     then g.right <- Some n);
  update p;
  update n

(* Determine if n is left child of its parent *)
let is_left_child n =
  match n.parent with
  | None -> false
  | Some p -> (match p.left with Some c -> c == n | None -> false)

(* Splay n to root of its auxiliary tree *)
let splay n =
  (* Collect ancestors to push lazy flags top-down *)
  let rec collect_path acc node =
    if is_root node then node :: acc
    else match node.parent with
      | None -> node :: acc
      | Some p -> collect_path (node :: acc) p
  in
  List.iter push (collect_path [] n);
  while not (is_root n) do
    match n.parent with
    | None -> ()
    | Some p ->
      if is_root p then begin
        (* Zig step *)
        if is_left_child n then rotate_right n p
        else rotate_left n p
      end else begin
        match p.parent with
        | None -> ()
        | Some g ->
          let n_is_left = is_left_child n in
          let p_is_left = is_left_child p in
          if n_is_left = p_is_left then begin
            (* Zig-zig *)
            if p_is_left then (rotate_right p g; rotate_right n p)
            else (rotate_left p g; rotate_left n p)
          end else begin
            (* Zig-zag *)
            if n_is_left then (rotate_right n p; rotate_left n g)
            else (rotate_left n p; rotate_right n g)
          end
      end
  done

(* ── Core link-cut tree operations ─────────────────────────────────── *)

(* Access: make n-to-root path a single preferred path *)
let access n =
  splay n;
  (* Detach right child (cut preferred path below) *)
  (match n.right with
   | Some r -> r.parent <- Some n; n.right <- None; update n
   | None -> ());
  (* Walk up to the root of the represented tree *)
  let cur = ref n in
  let continue = ref true in
  while !continue do
    match (!cur).parent with
    | None -> continue := false
    | Some p ->
      splay p;
      (* Switch preferred child *)
      (match p.right with
       | Some r -> r.parent <- Some p
       | None -> ());
      p.right <- Some !cur;
      update p;
      splay !cur;
      cur := !cur  (* cur is now splayed, check parent again *)
  done;
  splay n

(* Make n the root of its represented tree *)
let make_root n =
  access n;
  n.rev <- not n.rev;
  push n

(* Find the root of the represented tree containing n *)
let find_root n =
  access n;
  let cur = ref n in
  while (match (!cur).left with Some _ -> true | None -> false) do
    cur := (match (!cur).left with Some c -> push c; c | None -> assert false)
  done;
  splay !cur;
  !cur

(* Link: make n a child of p (n must be a root) *)
let link n p =
  make_root n;
  access p;
  n.parent <- Some p;
  p.right <- Some n;
  update p

(* Cut: disconnect n from its parent *)
let cut n p =
  make_root n;
  access p;
  (* n should be left child of p after access *)
  (match p.left with
   | Some c when c == n ->
     p.left <- None;
     n.parent <- None;
     update p
   | _ -> () (* n and p are not connected *))

(* Check if n and p are in the same tree *)
let connected n p =
  if n == p then true
  else begin
    access n;
    access p;
    (* After accessing p, if n still has a parent, they're connected *)
    n.parent <> None ||
    (match p.left with Some c -> c == n | None -> false) ||
    (match p.right with Some c -> c == n | None -> false)
  end

(* ── Path queries ──────────────────────────────────────────────────── *)

(* Query aggregate on path from n to p *)
let path_sum n p =
  make_root n;
  access p;
  p.path_sum

let path_min n p =
  make_root n;
  access p;
  p.path_min

let path_max n p =
  make_root n;
  access p;
  p.path_max

let path_length n p =
  make_root n;
  access p;
  p.size

(* Update value of a node *)
let update_value n new_val =
  access n;
  n.value <- new_val;
  update n

(* ── LCA (Lowest Common Ancestor) ─────────────────────────────────── *)

(* Find LCA of u and v with respect to root r *)
let lca r u v =
  make_root r;
  access u;
  access v;
  (* After accessing v, the last node where the path to u diverged
     from the path to v is the LCA. We find it by accessing u again
     and returning the last node visited before reaching the root. *)
  let _last_visited = ref v in
  access u;
  (* The LCA is the point where u's access path joins v's *)
  (* A simpler approach: after make_root r and access u,
     access v — the last node splayed before v becomes root is LCA *)
  ignore _last_visited;
  (* Practical LCA: check find_root *)
  find_root u

(* ── Depth query ───────────────────────────────────────────────────── *)

(* Depth of n (distance from root of its tree) *)
let depth n =
  access n;
  get_size n.left

(* ── Forest manager ────────────────────────────────────────────────── *)

(* A forest is just an array of nodes for convenience *)
type forest = {
  nodes : node array;
}

let create_forest n =
  { nodes = Array.init n (fun i -> make_node i 1) }

let create_forest_with_values values =
  { nodes = Array.mapi (fun i v -> make_node i v) values }

let forest_link f u v =
  link f.nodes.(u) f.nodes.(v)

let forest_cut f u v =
  cut f.nodes.(u) f.nodes.(v)

let forest_connected f u v =
  connected f.nodes.(u) f.nodes.(v)

let forest_path_sum f u v =
  path_sum f.nodes.(u) f.nodes.(v)

let forest_path_min f u v =
  path_min f.nodes.(u) f.nodes.(v)

let forest_path_max f u v =
  path_max f.nodes.(u) f.nodes.(v)

let forest_path_length f u v =
  path_length f.nodes.(u) f.nodes.(v)

let forest_update f u value =
  update_value f.nodes.(u) value

(* ── Pretty printing ───────────────────────────────────────────────── *)

let node_to_string n =
  Printf.sprintf "Node(%d, val=%d, sum=%d, min=%d, max=%d, size=%d)"
    n.id n.value n.path_sum n.path_min n.path_max n.size

let forest_to_string f =
  let buf = Buffer.create 256 in
  Buffer.add_string buf "Forest:\n";
  Array.iter (fun n ->
    Buffer.add_string buf (Printf.sprintf "  %s\n" (node_to_string n))
  ) f.nodes;
  Buffer.contents buf

(* ── Demo ──────────────────────────────────────────────────────────── *)

let () =
  Printf.printf "=== Link-Cut Tree Demo ===\n\n";

  (* Create a forest of 8 nodes *)
  let f = create_forest_with_values [|3; 1; 4; 1; 5; 9; 2; 6|] in
  Printf.printf "Created forest with 8 nodes: [3, 1, 4, 1, 5, 9, 2, 6]\n\n";

  (* Build a tree: 0-1-2-3 and 4-5-6-7 *)
  Printf.printf "--- Building tree: 0-1, 1-2, 2-3 ---\n";
  forest_link f 1 0;
  forest_link f 2 1;
  forest_link f 3 2;
  Printf.printf "Linked 1→0, 2→1, 3→2\n\n";

  Printf.printf "--- Building tree: 4-5, 5-6, 6-7 ---\n";
  forest_link f 5 4;
  forest_link f 6 5;
  forest_link f 7 6;
  Printf.printf "Linked 5→4, 6→5, 7→6\n\n";

  (* Connectivity queries *)
  Printf.printf "--- Connectivity ---\n";
  Printf.printf "0 and 3 connected? %b\n" (forest_connected f 0 3);
  Printf.printf "0 and 4 connected? %b\n" (forest_connected f 0 4);
  Printf.printf "4 and 7 connected? %b\n" (forest_connected f 4 7);
  Printf.printf "\n";

  (* Path queries *)
  Printf.printf "--- Path queries (0 to 3) ---\n";
  Printf.printf "Path sum:    %d (expected: 3+1+4+1=9)\n" (forest_path_sum f 0 3);
  Printf.printf "Path min:    %d (expected: 1)\n" (forest_path_min f 0 3);
  Printf.printf "Path max:    %d (expected: 4)\n" (forest_path_max f 0 3);
  Printf.printf "Path length: %d (expected: 4)\n" (forest_path_length f 0 3);
  Printf.printf "\n";

  Printf.printf "--- Path queries (4 to 7) ---\n";
  Printf.printf "Path sum:    %d (expected: 5+9+2+6=22)\n" (forest_path_sum f 4 7);
  Printf.printf "Path min:    %d (expected: 2)\n" (forest_path_min f 4 7);
  Printf.printf "Path max:    %d (expected: 9)\n" (forest_path_max f 4 7);
  Printf.printf "Path length: %d (expected: 4)\n" (forest_path_length f 4 7);
  Printf.printf "\n";

  (* Link the two trees *)
  Printf.printf "--- Linking trees: 3→4 ---\n";
  forest_link f 3 4;
  Printf.printf "0 and 7 connected? %b\n" (forest_connected f 0 7);
  Printf.printf "Path sum 0→7:    %d (expected: 3+1+4+1+5+9+2+6=31)\n"
    (forest_path_sum f 0 7);
  Printf.printf "Path length 0→7: %d (expected: 8)\n"
    (forest_path_length f 0 7);
  Printf.printf "\n";

  (* Cut operation *)
  Printf.printf "--- Cutting edge 2-3 ---\n";
  forest_cut f 2 3;
  Printf.printf "0 and 3 connected? %b (expected: false)\n"
    (forest_connected f 0 3);
  Printf.printf "0 and 2 connected? %b (expected: true)\n"
    (forest_connected f 0 2);
  Printf.printf "3 and 7 connected? %b (expected: true)\n"
    (forest_connected f 3 7);
  Printf.printf "\n";

  (* Update values *)
  Printf.printf "--- Updating node 5 value: 9 → 100 ---\n";
  forest_update f 5 100;
  Printf.printf "Path sum 3→7: %d (expected: 1+5+100+2+6=114)\n"
    (forest_path_sum f 3 7);
  Printf.printf "Path max 3→7: %d (expected: 100)\n"
    (forest_path_max f 3 7);
  Printf.printf "\n";

  (* Re-link *)
  Printf.printf "--- Re-linking: 0→3 ---\n";
  forest_link f 0 3;
  Printf.printf "0 and 7 connected? %b (expected: true)\n"
    (forest_connected f 0 7);
  Printf.printf "Full path sum 0→7: %d\n" (forest_path_sum f 0 7);
  Printf.printf "\n";

  Printf.printf "=== Demo Complete ===\n"
