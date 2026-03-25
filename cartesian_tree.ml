(* cartesian_tree.ml — Cartesian Tree data structure
 *
 * A Cartesian tree is a binary tree derived from a sequence of numbers.
 * It satisfies two properties simultaneously:
 *   1. It is a binary search tree with respect to indices (in-order traversal
 *      yields the original sequence)
 *   2. It is a min-heap with respect to values (parent value ≤ children values)
 *
 * Cartesian trees are useful for:
 *   - Range Minimum Queries (RMQ) in O(1) with O(n) preprocessing
 *   - Constructing suffix trees (via LCP arrays)
 *   - Treaps (randomized BSTs)
 *
 * Construction: O(n) using a stack-based algorithm
 *)

module CartesianTree = struct

  type 'a node = {
    value: 'a;
    index: int;
    left: 'a tree;
    right: 'a tree;
  }
  and 'a tree = 'a node option

  (* Build a Cartesian tree from an array in O(n) time using a stack *)
  let build (arr : 'a array) (cmp : 'a -> 'a -> int) : 'a tree =
    let n = Array.length arr in
    if n = 0 then None
    else begin
      (* Each element gets a node; we maintain a stack of nodes
         where the stack represents the rightmost path of the tree *)
      let nodes = Array.init n (fun i ->
        ref { value = arr.(i); index = i; left = None; right = None }
      ) in
      let stack = Stack.create () in
      for i = 0 to n - 1 do
        let last_popped = ref None in
        (* Pop nodes from stack while they have larger values *)
        while not (Stack.is_empty stack) &&
              cmp (!(Stack.top stack)).value arr.(i) > 0 do
          last_popped := Some (Stack.pop stack)
        done;
        (* The last popped node becomes left child of current *)
        (match !last_popped with
         | Some parent_ref -> nodes.(i) := { !(nodes.(i)) with left = Some !parent_ref }
         | None -> ());
        (* Current becomes right child of stack top (if any) *)
        (if not (Stack.is_empty stack) then
           let top = Stack.top stack in
           top := { !(!top) with right = Some !(nodes.(i)) }
        );
        Stack.push nodes.(i) stack
      done;
      (* Root is bottom of stack *)
      let root = ref None in
      Stack.iter (fun n -> root := Some !n) stack;
      !root
    end

  (* Build from a list *)
  let of_list (lst : 'a list) (cmp : 'a -> 'a -> int) : 'a tree =
    build (Array.of_list lst) cmp

  (* In-order traversal recovers the original sequence *)
  let to_list (t : 'a tree) : 'a list =
    let rec aux acc = function
      | None -> acc
      | Some node ->
        let acc = aux acc node.right in
        let acc = node.value :: acc in
        aux acc node.left
    in
    aux [] t

  (* Get the root (minimum element) *)
  let root_value (t : 'a tree) : 'a option =
    match t with
    | None -> None
    | Some node -> Some node.value

  (* Get the root index *)
  let root_index (t : 'a tree) : int option =
    match t with
    | None -> None
    | Some node -> Some node.index

  (* Tree size *)
  let rec size (t : 'a tree) : int =
    match t with
    | None -> 0
    | Some node -> 1 + size node.left + size node.right

  (* Tree height *)
  let rec height (t : 'a tree) : int =
    match t with
    | None -> 0
    | Some node -> 1 + max (height node.left) (height node.right)

  (* Check if a tree satisfies the min-heap property *)
  let rec is_min_heap (t : 'a tree) (cmp : 'a -> 'a -> int) : bool =
    match t with
    | None -> true
    | Some node ->
      let left_ok = match node.left with
        | None -> true
        | Some l -> cmp node.value l.value <= 0 && is_min_heap (Some l) cmp
      in
      let right_ok = match node.right with
        | None -> true
        | Some r -> cmp node.value r.value <= 0 && is_min_heap (Some r) cmp
      in
      left_ok && right_ok

  (* Check if in-order traversal preserves index order (BST on indices) *)
  let is_index_sorted (t : 'a tree) : bool =
    let indices = ref [] in
    let rec collect = function
      | None -> ()
      | Some node ->
        collect node.left;
        indices := node.index :: !indices;
        collect node.right
    in
    collect t;
    let lst = List.rev !indices in
    let rec sorted = function
      | [] | [_] -> true
      | a :: (b :: _ as rest) -> a < b && sorted rest
    in
    sorted lst

  (* Validate: both heap property and index ordering hold *)
  let is_valid (t : 'a tree) (cmp : 'a -> 'a -> int) : bool =
    is_min_heap t cmp && is_index_sorted t

  (* Range Minimum Query using the Cartesian tree structure.
     Given indices [lo, hi], find the index of the minimum value.
     This naive implementation is O(h) per query; with Euler tour + sparse table
     it can be made O(1). *)
  let rec rmq (t : 'a tree) (lo : int) (hi : int) (cmp : 'a -> 'a -> int) : int option =
    match t with
    | None -> None
    | Some node ->
      if node.index < lo then
        rmq node.right lo hi cmp
      else if node.index > hi then
        rmq node.left lo hi cmp
      else
        (* node.index is in [lo, hi], and it's the min of its subtree *)
        Some node.index

  (* Pretty-print the tree *)
  let to_string (t : 'a tree) (show : 'a -> string) : string =
    let buf = Buffer.create 256 in
    let rec aux prefix is_left = function
      | None -> ()
      | Some node ->
        Buffer.add_string buf prefix;
        Buffer.add_string buf (if is_left then "├── " else "└── ");
        Buffer.add_string buf (Printf.sprintf "[%d]=%s\n" node.index (show node.value));
        let new_prefix = prefix ^ (if is_left then "│   " else "    ") in
        aux new_prefix true node.left;
        aux new_prefix false node.right
    in
    (match t with
     | None -> Buffer.add_string buf "(empty)\n"
     | Some node ->
       Buffer.add_string buf (Printf.sprintf "[%d]=%s\n" node.index (show node.value));
       aux "" true node.left;
       aux "" false node.right);
    Buffer.contents buf

  (* Euler tour for O(1) RMQ preprocessing *)
  type 'a rmq_table = {
    euler_nodes: 'a node array;   (* Euler tour *)
    euler_depths: int array;       (* depth at each tour position *)
    first_occurrence: int array;   (* first occurrence of index i in tour *)
    sparse: int array array;       (* sparse table over euler tour *)
    compare: 'a -> 'a -> int;
  }

  let build_rmq_table (t : 'a tree) (n : int) (cmp : 'a -> 'a -> int) : 'a rmq_table option =
    match t with
    | None -> None
    | Some root ->
      (* Euler tour has at most 2n-1 entries *)
      let cap = 2 * n in
      let euler_nodes = Array.make cap root in
      let euler_depths = Array.make cap 0 in
      let first_occurrence = Array.make n (-1) in
      let pos = ref 0 in
      let rec tour node depth =
        let p = !pos in
        euler_nodes.(p) <- node;
        euler_depths.(p) <- depth;
        if first_occurrence.(node.index) = -1 then
          first_occurrence.(node.index) <- p;
        incr pos;
        (match node.left with
         | Some l ->
           tour l (depth + 1);
           let p2 = !pos in
           euler_nodes.(p2) <- node;
           euler_depths.(p2) <- depth;
           incr pos
         | None -> ());
        (match node.right with
         | Some r ->
           tour r (depth + 1);
           let p2 = !pos in
           euler_nodes.(p2) <- node;
           euler_depths.(p2) <- depth;
           incr pos
         | None -> ())
      in
      tour root 0;
      let len = !pos in
      (* Build sparse table for range minimum on euler_depths *)
      let log2 x =
        let r = ref 0 in
        let v = ref x in
        while !v > 1 do incr r; v := !v / 2 done;
        !r
      in
      let k = log2 len + 1 in
      let sparse = Array.init k (fun _ -> Array.make len 0) in
      for i = 0 to len - 1 do
        sparse.(0).(i) <- i
      done;
      for j = 1 to k - 1 do
        for i = 0 to len - (1 lsl j) do
          let l = sparse.(j-1).(i) in
          let r = sparse.(j-1).(i + (1 lsl (j-1))) in
          sparse.(j).(i) <- if euler_depths.(l) <= euler_depths.(r) then l else r
        done
      done;
      Some { euler_nodes; euler_depths; first_occurrence; sparse; compare = cmp }

  (* O(1) range minimum query using sparse table *)
  let rmq_fast (table : 'a rmq_table) (lo : int) (hi : int) : int option =
    if lo < 0 || hi < 0 || lo >= Array.length table.first_occurrence
       || hi >= Array.length table.first_occurrence then None
    else
      let l = table.first_occurrence.(lo) in
      let r = table.first_occurrence.(hi) in
      if l < 0 || r < 0 then None
      else
        let l, r = if l <= r then l, r else r, l in
        let len = r - l + 1 in
        let log2 x =
          let r = ref 0 in
          let v = ref x in
          while !v > 1 do incr r; v := !v / 2 done;
          !r
        in
        let k = log2 len in
        let left_idx = table.sparse.(k).(l) in
        let right_idx = table.sparse.(k).(r - (1 lsl k) + 1) in
        let best = if table.euler_depths.(left_idx) <= table.euler_depths.(right_idx)
                   then left_idx else right_idx in
        Some table.euler_nodes.(best).index

end

(* === Demo === *)

let () =
  Printf.printf "=== Cartesian Tree Demo ===\n\n";

  let arr = [| 3; 2; 6; 1; 9; 5; 7 |] in
  Printf.printf "Input array: [|";
  Array.iteri (fun i v ->
    if i > 0 then Printf.printf "; ";
    Printf.printf "%d" v
  ) arr;
  Printf.printf "|]\n\n";

  let cmp = compare in
  let tree = CartesianTree.build arr cmp in

  Printf.printf "Tree structure:\n%s\n"
    (CartesianTree.to_string tree string_of_int);

  Printf.printf "Root (minimum): %s at index %s\n"
    (match CartesianTree.root_value tree with Some v -> string_of_int v | None -> "none")
    (match CartesianTree.root_index tree with Some i -> string_of_int i | None -> "none");

  Printf.printf "Size: %d\n" (CartesianTree.size tree);
  Printf.printf "Height: %d\n" (CartesianTree.height tree);
  Printf.printf "Valid (heap + index order): %b\n"
    (CartesianTree.is_valid tree cmp);

  Printf.printf "In-order traversal: [";
  List.iteri (fun i v ->
    if i > 0 then Printf.printf "; ";
    Printf.printf "%d" v
  ) (CartesianTree.to_list tree);
  Printf.printf "]\n\n";

  (* Range Minimum Queries *)
  Printf.printf "=== Range Minimum Queries (naive O(h)) ===\n";
  let queries = [(0, 6); (0, 2); (2, 5); (4, 6); (1, 3)] in
  List.iter (fun (lo, hi) ->
    match CartesianTree.rmq tree lo hi cmp with
    | Some idx ->
      Printf.printf "RMQ(%d, %d) = index %d (value %d)\n" lo hi idx arr.(idx)
    | None ->
      Printf.printf "RMQ(%d, %d) = none\n" lo hi
  ) queries;

  (* O(1) RMQ with sparse table *)
  Printf.printf "\n=== Range Minimum Queries (O(1) with sparse table) ===\n";
  let n = Array.length arr in
  (match CartesianTree.build_rmq_table tree n cmp with
   | Some table ->
     List.iter (fun (lo, hi) ->
       match CartesianTree.rmq_fast table lo hi with
       | Some idx ->
         Printf.printf "RMQ_fast(%d, %d) = index %d (value %d)\n" lo hi idx arr.(idx)
       | None ->
         Printf.printf "RMQ_fast(%d, %d) = none\n" lo hi
     ) queries
   | None -> Printf.printf "Could not build RMQ table\n");

  (* Build from a list *)
  Printf.printf "\n=== Build from list ===\n";
  let tree2 = CartesianTree.of_list [5; 10; 40; 30; 28] cmp in
  Printf.printf "%s" (CartesianTree.to_string tree2 string_of_int);
  Printf.printf "Valid: %b\n" (CartesianTree.is_valid tree2 cmp);

  Printf.printf "\nDone!\n"
