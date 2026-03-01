(* test_all.ml — Comprehensive test suite for OCaml sample code *)
(* Tests core algorithms: BST, factorization, fibonacci, mergesort, heap, list_last, graph *)
(* Uses simple assertion-based testing — no external dependencies required *)

let tests_run = ref 0
let tests_passed = ref 0
let tests_failed = ref 0
let current_suite = ref ""

let assert_equal ~msg expected actual =
  incr tests_run;
  if expected = actual then
    incr tests_passed
  else begin
    incr tests_failed;
    Printf.printf "  FAIL [%s] %s: expected %s, got %s\n"
      !current_suite msg
      (expected) (actual)
  end

let assert_true ~msg condition =
  incr tests_run;
  if condition then
    incr tests_passed
  else begin
    incr tests_failed;
    Printf.printf "  FAIL [%s] %s\n" !current_suite msg
  end

let assert_raises ~msg f =
  incr tests_run;
  try
    ignore (f ());
    incr tests_failed;
    Printf.printf "  FAIL [%s] %s: expected exception\n" !current_suite msg
  with _ ->
    incr tests_passed

let suite name f =
  current_suite := name;
  Printf.printf "Running: %s\n" name;
  f ()

let string_of_int_list lst =
  "[" ^ String.concat "; " (List.map string_of_int lst) ^ "]"

let string_of_option f = function
  | None -> "None"
  | Some x -> "Some(" ^ f x ^ ")"

(* ===== BST functions (from bst.ml) ===== *)

type 'a tree =
  | Leaf
  | Node of 'a tree * 'a * 'a tree

let rec bst_insert x = function
  | Leaf -> Node (Leaf, x, Leaf)
  | Node (left, v, right) ->
    if x < v then Node (bst_insert x left, v, right)
    else if x > v then Node (left, v, bst_insert x right)
    else Node (left, v, right)

let rec bst_member x = function
  | Leaf -> false
  | Node (left, v, right) ->
    if x = v then true
    else if x < v then bst_member x left
    else bst_member x right

let bst_inorder tree =
  let rec aux acc = function
    | Leaf -> acc
    | Node (left, v, right) -> aux (v :: aux acc right) left
  in
  aux [] tree

let rec bst_min_elem = function
  | Leaf -> None
  | Node (Leaf, v, _) -> Some v
  | Node (left, _, _) -> bst_min_elem left

let rec bst_max_elem = function
  | Leaf -> None
  | Node (_, v, Leaf) -> Some v
  | Node (_, _, right) -> bst_max_elem right

let rec bst_size = function
  | Leaf -> 0
  | Node (left, _, right) -> 1 + bst_size left + bst_size right

let rec bst_depth = function
  | Leaf -> 0
  | Node (left, _, right) -> 1 + max (bst_depth left) (bst_depth right)

let rec bst_delete x = function
  | Leaf -> Leaf
  | Node (left, v, right) ->
    if x < v then Node (bst_delete x left, v, right)
    else if x > v then Node (left, v, bst_delete x right)
    else
      match left, right with
      | Leaf, _ -> right
      | _, Leaf -> left
      | _ ->
        (match bst_min_elem right with
         | None -> Leaf
         | Some successor -> Node (left, successor, bst_delete successor right))

let bst_of_list lst =
  List.fold_left (fun acc x -> bst_insert x acc) Leaf lst

(* ===== Factor functions (from factor.ml) ===== *)

let factors n =
  if n < 2 then invalid_arg "factors: input must be >= 2"
  else
    let rec extract_twos n =
      if n mod 2 = 0 then 2 :: extract_twos (n / 2)
      else odd_factors 3 n
    and odd_factors d n =
      if n = 1 then []
      else if d * d > n then [n]
      else if n mod d = 0 then d :: odd_factors d (n / d)
      else odd_factors (d + 2) n
    in
    extract_twos n

(* ===== Fibonacci functions (from fibonacci.ml) ===== *)

let rec fib_naive = function
  | 0 -> 0
  | 1 -> 1
  | n -> fib_naive (n - 1) + fib_naive (n - 2)

let fib_memo =
  let cache = Hashtbl.create 64 in
  let rec fib n =
    match Hashtbl.find_opt cache n with
    | Some v -> v
    | None ->
      let v = match n with
        | 0 -> 0
        | 1 -> 1
        | _ -> fib (n - 1) + fib (n - 2)
      in
      Hashtbl.replace cache n v;
      v
  in
  fib

let fib_iter n =
  if n <= 0 then 0
  else
    let rec aux a b i =
      if i = n then b
      else aux b (a + b) (i + 1)
    in
    aux 0 1 1

let fib_sequence n =
  List.init n fib_iter

(* ===== Mergesort functions (from mergesort.ml) ===== *)

let merge_split lst =
  let rec aux left right = function
    | [] -> (List.rev left, List.rev right)
    | [x] -> (List.rev (x :: left), List.rev right)
    | x :: y :: rest -> aux (x :: left) (y :: right) rest
  in
  aux [] [] lst

let merge_sorted cmp l1 l2 =
  let rec aux acc l1 l2 =
    match l1, l2 with
    | [], l | l, [] -> List.rev_append acc l
    | h1 :: t1, h2 :: t2 ->
      if cmp h1 h2 <= 0 then aux (h1 :: acc) t1 l2
      else aux (h2 :: acc) l1 t2
  in
  aux [] l1 l2

let rec mergesort cmp = function
  | ([] | [_]) as l -> l
  | lst ->
    let (left, right) = merge_split lst in
    merge_sorted cmp (mergesort cmp left) (mergesort cmp right)

(* ===== Heap functions (from heap.ml) ===== *)

type 'a heap =
  | HEmpty
  | HNode of int * 'a * 'a heap * 'a heap

let heap_rank = function
  | HEmpty -> 0
  | HNode (r, _, _, _) -> r

let heap_make_node x a b =
  if heap_rank a >= heap_rank b then HNode (heap_rank b + 1, x, a, b)
  else HNode (heap_rank a + 1, x, b, a)

let heap_is_empty = function
  | HEmpty -> true
  | HNode _ -> false

let rec heap_merge cmp h1 h2 =
  match h1, h2 with
  | HEmpty, h | h, HEmpty -> h
  | HNode (_, x, a1, b1), HNode (_, y, _, _) ->
    if cmp x y <= 0 then
      heap_make_node x a1 (heap_merge cmp b1 h2)
    else
      heap_merge cmp h2 h1

let heap_insert cmp x h =
  heap_merge cmp (HNode (1, x, HEmpty, HEmpty)) h

let heap_find_min = function
  | HEmpty -> None
  | HNode (_, x, _, _) -> Some x

let heap_delete_min cmp = function
  | HEmpty -> HEmpty
  | HNode (_, _, left, right) -> heap_merge cmp left right

let rec heap_size = function
  | HEmpty -> 0
  | HNode (_, _, left, right) -> 1 + heap_size left + heap_size right

let heap_from_list cmp lst =
  List.fold_left (fun h x -> heap_insert cmp x h) HEmpty lst

let heap_to_sorted cmp h =
  let rec aux acc h =
    match heap_find_min h with
    | None -> List.rev acc
    | Some x -> aux (x :: acc) (heap_delete_min cmp h)
  in
  aux [] h

let rec heap_is_leftist = function
  | HEmpty -> true
  | HNode (_, _, left, right) ->
    heap_rank left >= heap_rank right && heap_is_leftist left && heap_is_leftist right

let rec heap_is_min_heap cmp = function
  | HEmpty -> true
  | HNode (_, x, left, right) ->
    let left_ok = match left with
      | HEmpty -> true
      | HNode (_, y, _, _) -> cmp x y <= 0 && heap_is_min_heap cmp left
    in
    let right_ok = match right with
      | HEmpty -> true
      | HNode (_, y, _, _) -> cmp x y <= 0 && heap_is_min_heap cmp right
    in
    left_ok && right_ok

(* ===== List last element (from list_last_elem.ml) ===== *)

let rec list_last = function
  | [] -> None
  | [x] -> Some x
  | _ :: t -> list_last t

(* ===== Graph functions (from graph.ml) ===== *)

module IntMap = Map.Make(Int)

type graph = {
  adj: int list IntMap.t;
  directed: bool;
}

let empty_graph ~directed = { adj = IntMap.empty; directed }

let graph_add_edge g u v =
  let add_neighbor src dst adj =
    let neighbors = try IntMap.find src adj with Not_found -> [] in
    if List.mem dst neighbors then adj
    else IntMap.add src (dst :: neighbors) adj
  in
  let adj = add_neighbor u v g.adj in
  let adj = if not g.directed then add_neighbor v u adj else adj in
  let adj = if not (IntMap.mem v adj) then IntMap.add v [] adj else adj in
  { g with adj }

let graph_vertices g =
  IntMap.fold (fun k _ acc -> k :: acc) g.adj []
  |> List.sort compare

let graph_neighbors g v =
  try IntMap.find v g.adj |> List.sort compare
  with Not_found -> []

let graph_num_vertices g = IntMap.cardinal g.adj

let graph_num_edges g =
  let total = IntMap.fold (fun _ ns acc -> acc + List.length ns) g.adj 0 in
  if g.directed then total else total / 2

let graph_bfs g start =
  if not (IntMap.mem start g.adj) then []
  else begin
    let visited = Hashtbl.create 16 in
    let queue = Queue.create () in
    let result = ref [] in
    Queue.push start queue;
    Hashtbl.replace visited start true;
    while not (Queue.is_empty queue) do
      let v = Queue.pop queue in
      result := v :: !result;
      List.iter (fun w ->
        if not (Hashtbl.mem visited w) then begin
          Hashtbl.replace visited w true;
          Queue.push w queue
        end
      ) (graph_neighbors g v)
    done;
    List.rev !result
  end

let graph_dfs g start =
  if not (IntMap.mem start g.adj) then []
  else begin
    let visited = Hashtbl.create 16 in
    let result = ref [] in
    let rec explore v =
      if not (Hashtbl.mem visited v) then begin
        Hashtbl.replace visited v true;
        result := v :: !result;
        List.iter explore (graph_neighbors g v)
      end
    in
    explore start;
    List.rev !result
  end

type color = White | Gray | Black

let graph_has_cycle g =
  let color = Hashtbl.create 16 in
  List.iter (fun v -> Hashtbl.replace color v White) (graph_vertices g);
  let found_cycle = ref false in
  let rec visit v =
    if !found_cycle then ()
    else begin
      Hashtbl.replace color v Gray;
      List.iter (fun w ->
        if not !found_cycle then
          match Hashtbl.find color w with
          | Gray -> found_cycle := true
          | White -> visit w
          | Black -> ()
      ) (graph_neighbors g v);
      Hashtbl.replace color v Black
    end
  in
  List.iter (fun v ->
    if Hashtbl.find color v = White then visit v
  ) (graph_vertices g);
  !found_cycle

(* Add a vertex (no-op if it already exists) *)
let graph_add_vertex g v =
  if IntMap.mem v g.adj then g
  else { g with adj = IntMap.add v [] g.adj }

(* BFS shortest path: returns the path from start to goal, or None *)
let graph_bfs_path g start goal =
  if not (IntMap.mem start g.adj) || not (IntMap.mem goal g.adj) then None
  else if start = goal then Some [start]
  else begin
    let visited = Hashtbl.create 16 in
    let parent = Hashtbl.create 16 in
    let queue = Queue.create () in
    Queue.push start queue;
    Hashtbl.replace visited start true;
    let found = ref false in
    while not (Queue.is_empty queue) && not !found do
      let v = Queue.pop queue in
      List.iter (fun w ->
        if not (Hashtbl.mem visited w) then begin
          Hashtbl.replace visited w true;
          Hashtbl.replace parent w v;
          if w = goal then found := true
          else Queue.push w queue
        end
      ) (graph_neighbors g v)
    done;
    if not !found then None
    else begin
      let rec build_path v acc =
        if v = start then v :: acc
        else build_path (Hashtbl.find parent v) (v :: acc)
      in
      Some (build_path goal [])
    end
  end

(* Internal DFS that uses a shared visited Hashtbl *)
let graph_dfs_collect g start visited =
  let result = ref [] in
  let rec explore v =
    if not (Hashtbl.mem visited v) then begin
      Hashtbl.replace visited v true;
      result := v :: !result;
      List.iter explore (graph_neighbors g v)
    end
  in
  explore start;
  List.rev !result

(* Connected components — returns list of sorted vertex lists *)
let graph_connected_components g =
  let visited = Hashtbl.create 16 in
  let components = ref [] in
  List.iter (fun v ->
    if not (Hashtbl.mem visited v) then begin
      let component = graph_dfs_collect g v visited in
      components := List.sort compare component :: !components
    end
  ) (graph_vertices g);
  List.rev !components

(* Topological sort — returns Some sorted_list or None if cycle *)
let graph_topological_sort g =
  let in_deg = Hashtbl.create 16 in
  List.iter (fun v -> Hashtbl.replace in_deg v 0) (graph_vertices g);
  IntMap.iter (fun _ ns ->
    List.iter (fun w ->
      let d = try Hashtbl.find in_deg w with Not_found -> 0 in
      Hashtbl.replace in_deg w (d + 1)
    ) ns
  ) g.adj;
  let queue = Queue.create () in
  Hashtbl.iter (fun v d -> if d = 0 then Queue.push v queue) in_deg;
  let result = ref [] in
  while not (Queue.is_empty queue) do
    let v = Queue.pop queue in
    result := v :: !result;
    List.iter (fun w ->
      let d = Hashtbl.find in_deg w - 1 in
      Hashtbl.replace in_deg w d;
      if d = 0 then Queue.push w queue
    ) (graph_neighbors g v)
  done;
  let sorted = List.rev !result in
  if List.length sorted <> graph_num_vertices g then None
  else Some sorted


(* =============================================================== *)
(*                          TEST SUITES                            *)
(* =============================================================== *)

let test_bst () = suite "BST" (fun () ->
  (* Empty tree *)
  assert_true ~msg:"empty tree has size 0" (bst_size Leaf = 0);
  assert_true ~msg:"empty tree has depth 0" (bst_depth Leaf = 0);
  assert_true ~msg:"empty tree min is None" (bst_min_elem Leaf = None);
  assert_true ~msg:"empty tree max is None" (bst_max_elem Leaf = None);
  assert_true ~msg:"member in empty tree is false" (not (bst_member 5 Leaf));
  assert_true ~msg:"inorder of empty tree is []" (bst_inorder Leaf = []);

  (* Single element *)
  let t1 = bst_insert 5 Leaf in
  assert_true ~msg:"singleton size is 1" (bst_size t1 = 1);
  assert_true ~msg:"singleton depth is 1" (bst_depth t1 = 1);
  assert_true ~msg:"singleton member" (bst_member 5 t1);
  assert_true ~msg:"singleton non-member" (not (bst_member 3 t1));
  assert_equal ~msg:"singleton min" "Some(5)" (string_of_option string_of_int (bst_min_elem t1));
  assert_equal ~msg:"singleton max" "Some(5)" (string_of_option string_of_int (bst_max_elem t1));
  assert_equal ~msg:"singleton inorder" "[5]" (string_of_int_list (bst_inorder t1));

  (* Multiple elements *)
  let t = bst_of_list [5; 3; 7; 1; 4; 6; 8] in
  assert_true ~msg:"tree size is 7" (bst_size t = 7);
  assert_equal ~msg:"inorder is sorted" "[1; 3; 4; 5; 6; 7; 8]"
    (string_of_int_list (bst_inorder t));
  assert_true ~msg:"member 4" (bst_member 4 t);
  assert_true ~msg:"member 8" (bst_member 8 t);
  assert_true ~msg:"not member 9" (not (bst_member 9 t));
  assert_true ~msg:"not member 2" (not (bst_member 2 t));
  assert_equal ~msg:"min is 1" "Some(1)" (string_of_option string_of_int (bst_min_elem t));
  assert_equal ~msg:"max is 8" "Some(8)" (string_of_option string_of_int (bst_max_elem t));

  (* Duplicate insertion — should not change tree *)
  let t_dup = bst_insert 5 t in
  assert_true ~msg:"duplicate insert preserves size" (bst_size t_dup = 7);

  (* Deletion *)
  let t_del = bst_delete 3 t in
  assert_true ~msg:"deleted 3 not member" (not (bst_member 3 t_del));
  assert_true ~msg:"other elements preserved after delete" (bst_member 4 t_del);
  assert_true ~msg:"size decremented after delete" (bst_size t_del = 6);
  assert_equal ~msg:"inorder after deleting 3" "[1; 4; 5; 6; 7; 8]"
    (string_of_int_list (bst_inorder t_del));

  (* Delete root *)
  let t_del_root = bst_delete 5 t in
  assert_true ~msg:"root deleted" (not (bst_member 5 t_del_root));
  assert_true ~msg:"size after root delete" (bst_size t_del_root = 6);
  (* inorder should still be sorted *)
  let sorted = bst_inorder t_del_root in
  assert_true ~msg:"inorder still sorted after root delete"
    (sorted = List.sort compare sorted);

  (* Delete leaf *)
  let t_del_leaf = bst_delete 1 t in
  assert_true ~msg:"leaf deleted" (not (bst_member 1 t_del_leaf));

  (* Delete non-existent — should be no-op *)
  let t_del_none = bst_delete 99 t in
  assert_true ~msg:"delete non-existent preserves size" (bst_size t_del_none = 7);

  (* Delete from empty tree *)
  assert_true ~msg:"delete from empty" (bst_delete 5 Leaf = Leaf);

  (* Sorted input (degenerate tree) *)
  let t_sorted = bst_of_list [1; 2; 3; 4; 5] in
  assert_equal ~msg:"sorted input inorder" "[1; 2; 3; 4; 5]"
    (string_of_int_list (bst_inorder t_sorted));
  assert_true ~msg:"sorted input size" (bst_size t_sorted = 5);
  (* Degenerate tree has depth = n *)
  assert_true ~msg:"sorted input depth" (bst_depth t_sorted = 5);
)

let test_factors () = suite "Factors" (fun () ->
  assert_equal ~msg:"factors 2" "[2]" (string_of_int_list (factors 2));
  assert_equal ~msg:"factors 3" "[3]" (string_of_int_list (factors 3));
  assert_equal ~msg:"factors 4" "[2; 2]" (string_of_int_list (factors 4));
  assert_equal ~msg:"factors 12" "[2; 2; 3]" (string_of_int_list (factors 12));
  assert_equal ~msg:"factors 30" "[2; 3; 5]" (string_of_int_list (factors 30));
  assert_equal ~msg:"factors 97 (prime)" "[97]" (string_of_int_list (factors 97));
  assert_equal ~msg:"factors 360" "[2; 2; 2; 3; 3; 5]" (string_of_int_list (factors 360));
  assert_equal ~msg:"factors 1024" "[2; 2; 2; 2; 2; 2; 2; 2; 2; 2]" (string_of_int_list (factors 1024));
  assert_equal ~msg:"factors 17 (prime)" "[17]" (string_of_int_list (factors 17));

  (* Verify product equals original *)
  let check_product n =
    let fs = factors n in
    let product = List.fold_left ( * ) 1 fs in
    assert_true ~msg:(Printf.sprintf "product of factors(%d) = %d" n n) (product = n)
  in
  List.iter check_product [2; 12; 30; 97; 360; 1024; 7919; 100];

  (* Edge cases *)
  assert_raises ~msg:"factors 0 raises" (fun () -> factors 0);
  assert_raises ~msg:"factors 1 raises" (fun () -> factors 1);
  assert_raises ~msg:"factors -5 raises" (fun () -> factors (-5));
)

let test_fibonacci () = suite "Fibonacci" (fun () ->
  (* Base cases *)
  assert_true ~msg:"fib(0) = 0" (fib_iter 0 = 0);
  assert_true ~msg:"fib(1) = 1" (fib_iter 1 = 1);
  assert_true ~msg:"fib(2) = 1" (fib_iter 2 = 1);
  assert_true ~msg:"fib(10) = 55" (fib_iter 10 = 55);
  assert_true ~msg:"fib(20) = 6765" (fib_iter 20 = 6765);

  (* All three implementations agree *)
  for i = 0 to 25 do
    let naive = fib_naive i in
    let memo = fib_memo i in
    let iter = fib_iter i in
    assert_true
      ~msg:(Printf.sprintf "all fib implementations agree at n=%d" i)
      (naive = memo && memo = iter)
  done;

  (* Fibonacci sequence *)
  assert_equal ~msg:"first 10 fib" "[0; 1; 1; 2; 3; 5; 8; 13; 21; 34]"
    (string_of_int_list (fib_sequence 10));

  (* Negative input *)
  assert_true ~msg:"fib_iter(-1) = 0" (fib_iter (-1) = 0);

  (* Larger values *)
  assert_true ~msg:"fib(30) = 832040" (fib_iter 30 = 832040);

  (* Extended: Fibonacci properties *)
  (* fib(n) + fib(n+1) = fib(n+2) *)
  for i = 0 to 20 do
    assert_true
      ~msg:(Printf.sprintf "fib(%d) + fib(%d) = fib(%d)" i (i+1) (i+2))
      (fib_iter i + fib_iter (i + 1) = fib_iter (i + 2))
  done;

  (* fib_sequence length *)
  assert_true ~msg:"fib_sequence 0 is empty" (fib_sequence 0 = []);
  assert_equal ~msg:"fib_sequence 1" "[0]" (string_of_int_list (fib_sequence 1));
  assert_equal ~msg:"fib_sequence 2" "[0; 1]" (string_of_int_list (fib_sequence 2));

  (* Monotonicity: fib(n) <= fib(n+1) for n >= 1 *)
  for i = 1 to 30 do
    assert_true
      ~msg:(Printf.sprintf "fib(%d) <= fib(%d)" i (i+1))
      (fib_iter i <= fib_iter (i + 1))
  done;

  (* Known larger Fibonacci numbers *)
  assert_true ~msg:"fib(40) = 102334155" (fib_iter 40 = 102334155);
  assert_true ~msg:"fib(3) = 2" (fib_iter 3 = 2);
  assert_true ~msg:"fib(4) = 3" (fib_iter 4 = 3);
  assert_true ~msg:"fib(5) = 5" (fib_iter 5 = 5);
  assert_true ~msg:"fib(6) = 8" (fib_iter 6 = 8);
  assert_true ~msg:"fib(7) = 13" (fib_iter 7 = 13);

  (* Negative inputs for all implementations *)
  assert_true ~msg:"fib_naive(-1) = 0" (fib_naive (-1) = 0);
  assert_true ~msg:"fib_memo(-5) = 0" (fib_memo (-5) = 0);
  assert_true ~msg:"fib_sequence negative" (fib_sequence (-1) = []);
)

let test_mergesort () = suite "Mergesort" (fun () ->
  (* Empty list *)
  assert_equal ~msg:"sort empty" "[]" (string_of_int_list (mergesort compare []));

  (* Single element *)
  assert_equal ~msg:"sort [1]" "[1]" (string_of_int_list (mergesort compare [1]));

  (* Already sorted *)
  assert_equal ~msg:"sort already sorted" "[1; 2; 3; 4; 5]"
    (string_of_int_list (mergesort compare [1; 2; 3; 4; 5]));

  (* Reverse sorted *)
  assert_equal ~msg:"sort reverse" "[1; 2; 3; 4; 5]"
    (string_of_int_list (mergesort compare [5; 4; 3; 2; 1]));

  (* Random order *)
  assert_equal ~msg:"sort random" "[3; 9; 10; 27; 38; 43; 82]"
    (string_of_int_list (mergesort compare [38; 27; 43; 3; 9; 82; 10]));

  (* Duplicates *)
  assert_equal ~msg:"sort with duplicates" "[1; 2; 2; 3; 3; 5]"
    (string_of_int_list (mergesort compare [3; 1; 2; 5; 2; 3]));

  (* All same *)
  assert_equal ~msg:"sort all same" "[7; 7; 7; 7]"
    (string_of_int_list (mergesort compare [7; 7; 7; 7]));

  (* Descending sort *)
  assert_equal ~msg:"sort descending" "[82; 43; 38; 27; 10; 9; 3]"
    (string_of_int_list (mergesort (fun a b -> compare b a) [38; 27; 43; 3; 9; 82; 10]));

  (* Two elements *)
  assert_equal ~msg:"sort two elements" "[1; 2]"
    (string_of_int_list (mergesort compare [2; 1]));

  (* String sort *)
  let words = mergesort String.compare ["banana"; "apple"; "cherry"; "date"] in
  assert_equal ~msg:"sort strings" "[apple; banana; cherry; date]"
    ("[" ^ String.concat "; " words ^ "]");

  (* Split function *)
  let (l, r) = merge_split [1; 2; 3; 4; 5; 6] in
  assert_true ~msg:"split even length"
    (List.length l = 3 && List.length r = 3);
  let (l2, r2) = merge_split [1; 2; 3; 4; 5] in
  assert_true ~msg:"split odd length"
    (List.length l2 = 3 && List.length r2 = 2);
  let (l3, r3) = merge_split [] in
  assert_true ~msg:"split empty" (l3 = [] && r3 = []);

  (* Stability: mergesort should be stable *)
  (* Large list *)
  let big = List.init 100 (fun i -> 100 - i) in
  let sorted_big = mergesort compare big in
  assert_true ~msg:"sort 100 elements"
    (sorted_big = List.init 100 (fun i -> i + 1));
)

let test_heap () = suite "Heap" (fun () ->
  (* Empty heap *)
  assert_true ~msg:"empty heap is empty" (heap_is_empty HEmpty);
  assert_true ~msg:"empty heap size 0" (heap_size HEmpty = 0);
  assert_true ~msg:"empty heap min None" (heap_find_min HEmpty = None);
  assert_true ~msg:"delete from empty" (heap_delete_min compare HEmpty = HEmpty);

  (* Singleton *)
  let h1 = heap_insert compare 42 HEmpty in
  assert_true ~msg:"singleton not empty" (not (heap_is_empty h1));
  assert_true ~msg:"singleton size 1" (heap_size h1 = 1);
  assert_equal ~msg:"singleton min" "Some(42)"
    (string_of_option string_of_int (heap_find_min h1));
  assert_true ~msg:"singleton delete -> empty"
    (heap_is_empty (heap_delete_min compare h1));

  (* Multiple elements *)
  let h = heap_from_list compare [5; 3; 8; 1; 7; 2; 6; 4] in
  assert_true ~msg:"heap size 8" (heap_size h = 8);
  assert_equal ~msg:"heap min is 1" "Some(1)"
    (string_of_option string_of_int (heap_find_min h));

  (* Sorted extraction *)
  assert_equal ~msg:"heap sorted extraction" "[1; 2; 3; 4; 5; 6; 7; 8]"
    (string_of_int_list (heap_to_sorted compare h));

  (* Structural properties *)
  assert_true ~msg:"heap is leftist" (heap_is_leftist h);
  assert_true ~msg:"heap is min-heap" (heap_is_min_heap compare h);

  (* Merge two heaps *)
  let ha = heap_from_list compare [10; 20; 30] in
  let hb = heap_from_list compare [15; 25; 5] in
  let hc = heap_merge compare ha hb in
  assert_true ~msg:"merged size" (heap_size hc = 6);
  assert_equal ~msg:"merged min" "Some(5)"
    (string_of_option string_of_int (heap_find_min hc));
  assert_equal ~msg:"merged sorted" "[5; 10; 15; 20; 25; 30]"
    (string_of_int_list (heap_to_sorted compare hc));
  assert_true ~msg:"merged is leftist" (heap_is_leftist hc);
  assert_true ~msg:"merged is min-heap" (heap_is_min_heap compare hc);

  (* Persistence — original unchanged after insert/delete *)
  let h_orig = heap_from_list compare [3; 1; 4; 1; 5] in
  let h_ins = heap_insert compare 0 h_orig in
  let h_del = heap_delete_min compare h_orig in
  assert_equal ~msg:"original min unchanged" "Some(1)"
    (string_of_option string_of_int (heap_find_min h_orig));
  assert_equal ~msg:"insert 0 min" "Some(0)"
    (string_of_option string_of_int (heap_find_min h_ins));
  assert_equal ~msg:"delete min gives next" "Some(1)"
    (string_of_option string_of_int (heap_find_min h_del));
  (* Original has 5 elements (1 appears twice) *)
  assert_true ~msg:"original size unchanged" (heap_size h_orig = 5);
  assert_true ~msg:"insert size +1" (heap_size h_ins = 6);
  assert_true ~msg:"delete size -1" (heap_size h_del = 4);

  (* Max-heap via reverse comparator *)
  let max_cmp a b = compare b a in
  let max_h = heap_from_list max_cmp [5; 3; 8; 1; 7] in
  assert_equal ~msg:"max-heap top is 8" "Some(8)"
    (string_of_option string_of_int (heap_find_min max_h));
  assert_equal ~msg:"max-heap sorted desc" "[8; 7; 5; 3; 1]"
    (string_of_int_list (heap_to_sorted max_cmp max_h));

  (* Heap sort *)
  let unsorted = [42; 17; 93; 5; 28; 61; 3; 84; 50; 12] in
  let sorted = heap_to_sorted compare (heap_from_list compare unsorted) in
  assert_equal ~msg:"heap sort" "[3; 5; 12; 17; 28; 42; 50; 61; 84; 93]"
    (string_of_int_list sorted);

  (* Duplicates in heap *)
  let h_dups = heap_from_list compare [3; 3; 3; 1; 1] in
  assert_equal ~msg:"heap with dups sorted" "[1; 1; 3; 3; 3]"
    (string_of_int_list (heap_to_sorted compare h_dups));
)

let test_list_last () = suite "List Last" (fun () ->
  assert_equal ~msg:"last [1;2;3]" "Some(3)"
    (string_of_option string_of_int (list_last [1; 2; 3]));
  assert_equal ~msg:"last [42]" "Some(42)"
    (string_of_option string_of_int (list_last [42]));
  assert_equal ~msg:"last []" "None"
    (string_of_option string_of_int (list_last []));
  assert_equal ~msg:"last [1;2;3;4;5]" "Some(5)"
    (string_of_option string_of_int (list_last [1; 2; 3; 4; 5]));
  (* Extended tests *)
  assert_equal ~msg:"last [0]" "Some(0)"
    (string_of_option string_of_int (list_last [0]));
  assert_equal ~msg:"last negative" "Some(-1)"
    (string_of_option string_of_int (list_last [1; 2; -1]));
  assert_equal ~msg:"last two elements" "Some(2)"
    (string_of_option string_of_int (list_last [1; 2]));
  assert_equal ~msg:"last large list" "Some(100)"
    (string_of_option string_of_int (list_last (List.init 100 (fun i -> i + 1))));
  assert_equal ~msg:"last duplicates" "Some(5)"
    (string_of_option string_of_int (list_last [5; 5; 5]));
  assert_equal ~msg:"last max_int" "Some(max_int)"
    (string_of_option (fun _ -> "max_int") (list_last [max_int]));
)

let test_graph () = suite "Graph" (fun () ->
  (* Undirected graph *)
  let g = empty_graph ~directed:false in
  let g = List.fold_left (fun g (u, v) -> graph_add_edge g u v)
    g [(1,2); (1,3); (2,4); (3,4); (4,5)] in
  assert_true ~msg:"undirected vertices" (graph_num_vertices g = 5);
  assert_true ~msg:"undirected edges" (graph_num_edges g = 5);
  assert_equal ~msg:"undirected vertices list" "[1; 2; 3; 4; 5]"
    (string_of_int_list (graph_vertices g));

  (* Neighbors *)
  let n1 = graph_neighbors g 1 in
  assert_true ~msg:"vertex 1 neighbors" (List.mem 2 n1 && List.mem 3 n1);
  assert_true ~msg:"vertex 4 has 3 neighbors" (List.length (graph_neighbors g 4) = 3);

  (* BFS *)
  let bfs_result = graph_bfs g 1 in
  assert_true ~msg:"BFS visits all 5" (List.length bfs_result = 5);
  assert_true ~msg:"BFS starts at 1" (List.hd bfs_result = 1);

  (* DFS *)
  let dfs_result = graph_dfs g 1 in
  assert_true ~msg:"DFS visits all 5" (List.length dfs_result = 5);
  assert_true ~msg:"DFS starts at 1" (List.hd dfs_result = 1);

  (* BFS from non-existent vertex *)
  assert_true ~msg:"BFS non-existent" (graph_bfs g 99 = []);
  assert_true ~msg:"DFS non-existent" (graph_dfs g 99 = []);

  (* Disconnected graph *)
  let g2 = graph_add_edge g 6 7 in
  assert_true ~msg:"disconnected vertices" (graph_num_vertices g2 = 7);
  let bfs_from_1 = graph_bfs g2 1 in
  assert_true ~msg:"BFS doesn't reach disconnected" (not (List.mem 6 bfs_from_1));

  (* Directed graph *)
  let dg = empty_graph ~directed:true in
  let dg = List.fold_left (fun g (u, v) -> graph_add_edge g u v)
    dg [(1,2); (2,3); (3,4)] in
  assert_true ~msg:"directed edges" (graph_num_edges dg = 3);
  assert_true ~msg:"directed forward neighbor" (List.mem 2 (graph_neighbors dg 1));
  (* In directed graph, 2 is not a neighbor of 1 in reverse *)
  assert_true ~msg:"directed no back neighbor" (not (List.mem 1 (graph_neighbors dg 2)));

  (* Cycle detection *)
  assert_true ~msg:"DAG no cycle" (not (graph_has_cycle dg));
  let cyclic = graph_add_edge dg 4 1 in
  assert_true ~msg:"cyclic has cycle" (graph_has_cycle cyclic);

  (* Empty graph *)
  let eg = empty_graph ~directed:true in
  assert_true ~msg:"empty graph 0 vertices" (graph_num_vertices eg = 0);
  assert_true ~msg:"empty graph 0 edges" (graph_num_edges eg = 0);
  assert_true ~msg:"empty graph no cycle" (not (graph_has_cycle eg));

  (* === add_vertex === *)
  let gv = empty_graph ~directed:false in
  let gv = graph_add_vertex gv 10 in
  assert_true ~msg:"add_vertex creates vertex" (graph_num_vertices gv = 1);
  assert_true ~msg:"add_vertex vertex exists" (List.mem 10 (graph_vertices gv));
  assert_true ~msg:"add_vertex no edges" (graph_num_edges gv = 0);
  assert_true ~msg:"add_vertex empty neighbors" (graph_neighbors gv 10 = []);
  (* add_vertex is idempotent *)
  let gv2 = graph_add_vertex gv 10 in
  assert_true ~msg:"add_vertex idempotent" (graph_num_vertices gv2 = 1);
  (* add_vertex then add_edge *)
  let gv3 = graph_add_vertex (graph_add_vertex gv 20) 30 in
  assert_true ~msg:"add_vertex multiple" (graph_num_vertices gv3 = 3);
  let gv3 = graph_add_edge gv3 10 20 in
  assert_true ~msg:"add_vertex then edge" (graph_num_edges gv3 = 1);
  assert_true ~msg:"add_vertex preserves isolated" (graph_neighbors gv3 30 = []);

  (* === bfs_path === *)
  (* Reuse g: 1-2, 1-3, 2-4, 3-4, 4-5 undirected *)
  let path_1_5 = graph_bfs_path g 1 5 in
  (match path_1_5 with
   | None -> assert_true ~msg:"path 1->5 should exist" false
   | Some p ->
     assert_true ~msg:"path 1->5 starts at 1" (List.hd p = 1);
     assert_true ~msg:"path 1->5 ends at 5" (List.nth p (List.length p - 1) = 5);
     assert_true ~msg:"path 1->5 length <= 3" (List.length p <= 3));
  (* Same vertex path *)
  let path_self = graph_bfs_path g 1 1 in
  (match path_self with
   | None -> assert_true ~msg:"path 1->1 should exist" false
   | Some p -> assert_equal ~msg:"path 1->1" "[1]" (string_of_int_list p));
  (* No path to disconnected *)
  let gd = graph_add_edge g 6 7 in
  assert_true ~msg:"no path 1->6 disconnected" (graph_bfs_path gd 1 6 = None);
  (* Non-existent vertex *)
  assert_true ~msg:"path to non-existent" (graph_bfs_path g 1 99 = None);
  assert_true ~msg:"path from non-existent" (graph_bfs_path g 99 1 = None);
  (* Directed path *)
  let dg_path = graph_bfs_path dg 1 4 in
  (match dg_path with
   | None -> assert_true ~msg:"directed path 1->4 should exist" false
   | Some p ->
     assert_equal ~msg:"directed path 1->4" "[1; 2; 3; 4]" (string_of_int_list p));
  (* No reverse path in directed graph *)
  assert_true ~msg:"no reverse directed path 4->1" (graph_bfs_path dg 4 1 = None);

  (* === connected_components === *)
  let cc = graph_connected_components g in
  assert_true ~msg:"connected graph has 1 component" (List.length cc = 1);
  assert_equal ~msg:"component is all vertices" "[1; 2; 3; 4; 5]"
    (string_of_int_list (List.hd cc));
  (* Disconnected graph *)
  let cc2 = graph_connected_components gd in
  assert_true ~msg:"disconnected graph has 2 components" (List.length cc2 = 2);
  (* Components should be sorted vertex lists *)
  List.iter (fun comp ->
    assert_true ~msg:"component is sorted"
      (comp = List.sort compare comp)
  ) cc2;
  (* Three components *)
  let g3c = graph_add_vertex (graph_add_edge gd 8 9) 10 in
  let cc3 = graph_connected_components g3c in
  assert_true ~msg:"3 components + isolated = 4 components" (List.length cc3 = 4);
  (* Empty graph *)
  let cc_empty = graph_connected_components (empty_graph ~directed:false) in
  assert_true ~msg:"empty graph has 0 components" (List.length cc_empty = 0);
  (* Single vertex *)
  let cc_single = graph_connected_components (graph_add_vertex (empty_graph ~directed:false) 1) in
  assert_true ~msg:"single vertex = 1 component" (List.length cc_single = 1);
  assert_equal ~msg:"single vertex component" "[1]"
    (string_of_int_list (List.hd cc_single));

  (* === topological_sort === *)
  (* DAG: 1->2, 2->3, 3->4 *)
  let topo = graph_topological_sort dg in
  (match topo with
   | None -> assert_true ~msg:"DAG should have topo sort" false
   | Some sorted ->
     assert_true ~msg:"topo sort has all vertices" (List.length sorted = graph_num_vertices dg);
     (* Verify ordering: for every edge u->v, u appears before v *)
     let pos = Hashtbl.create 16 in
     List.iteri (fun i v -> Hashtbl.replace pos v i) sorted;
     assert_true ~msg:"topo: 1 before 2" (Hashtbl.find pos 1 < Hashtbl.find pos 2);
     assert_true ~msg:"topo: 2 before 3" (Hashtbl.find pos 2 < Hashtbl.find pos 3);
     assert_true ~msg:"topo: 3 before 4" (Hashtbl.find pos 3 < Hashtbl.find pos 4));
  (* Cyclic graph has no topo sort *)
  assert_true ~msg:"cyclic has no topo sort" (graph_topological_sort cyclic = None);
  (* Diamond DAG: 1->2, 1->3, 2->4, 3->4 *)
  let diamond = List.fold_left (fun g (u, v) -> graph_add_edge g u v)
    (empty_graph ~directed:true) [(1,2); (1,3); (2,4); (3,4)] in
  let topo_diamond = graph_topological_sort diamond in
  (match topo_diamond with
   | None -> assert_true ~msg:"diamond DAG should have topo sort" false
   | Some sorted ->
     let pos = Hashtbl.create 16 in
     List.iteri (fun i v -> Hashtbl.replace pos v i) sorted;
     assert_true ~msg:"diamond: 1 before 2" (Hashtbl.find pos 1 < Hashtbl.find pos 2);
     assert_true ~msg:"diamond: 1 before 3" (Hashtbl.find pos 1 < Hashtbl.find pos 3);
     assert_true ~msg:"diamond: 2 before 4" (Hashtbl.find pos 2 < Hashtbl.find pos 4);
     assert_true ~msg:"diamond: 3 before 4" (Hashtbl.find pos 3 < Hashtbl.find pos 4));
  (* Empty graph topo sort *)
  let topo_empty = graph_topological_sort (empty_graph ~directed:true) in
  (match topo_empty with
   | None -> assert_true ~msg:"empty graph topo sort should succeed" false
   | Some sorted -> assert_true ~msg:"empty topo sort is empty" (sorted = []));
  (* Single vertex topo sort *)
  let topo_single = graph_topological_sort (graph_add_vertex (empty_graph ~directed:true) 1) in
  (match topo_single with
   | None -> assert_true ~msg:"single vertex topo sort should succeed" false
   | Some sorted -> assert_equal ~msg:"single vertex topo sort" "[1]" (string_of_int_list sorted));
  (* Longer chain *)
  let chain = List.fold_left (fun g (u, v) -> graph_add_edge g u v)
    (empty_graph ~directed:true) [(1,2); (2,3); (3,4); (4,5); (5,6)] in
  let topo_chain = graph_topological_sort chain in
  (match topo_chain with
   | None -> assert_true ~msg:"chain topo sort should succeed" false
   | Some sorted ->
     assert_equal ~msg:"chain topo sort" "[1; 2; 3; 4; 5; 6]" (string_of_int_list sorted));

  (* === dfs_collect === *)
  let vis = Hashtbl.create 16 in
  let comp1 = graph_dfs_collect gd 1 vis in
  assert_true ~msg:"dfs_collect from 1 gets 5 vertices" (List.length comp1 = 5);
  assert_true ~msg:"dfs_collect 1 contains 1" (List.mem 1 comp1);
  assert_true ~msg:"dfs_collect 1 contains 5" (List.mem 5 comp1);
  assert_true ~msg:"dfs_collect 1 not 6" (not (List.mem 6 comp1));
  (* Shared visited: collecting from 6 should only get {6,7} *)
  let comp2 = graph_dfs_collect gd 6 vis in
  assert_true ~msg:"dfs_collect from 6 gets 2 vertices" (List.length comp2 = 2);
  assert_true ~msg:"dfs_collect 6 contains 6" (List.mem 6 comp2);
  assert_true ~msg:"dfs_collect 6 contains 7" (List.mem 7 comp2);
  (* Already visited vertex returns empty *)
  let comp3 = graph_dfs_collect gd 1 vis in
  assert_true ~msg:"dfs_collect already visited returns empty" (List.length comp3 = 0);
)

(* ===== Trie functions (from trie.ml) ===== *)

module CharMap = Map.Make(Char)

type trie = {
  is_word: bool;
  children: trie CharMap.t;
}

let trie_empty = { is_word = false; children = CharMap.empty }

let trie_chars_of_string s =
  List.init (String.length s) (String.get s)

let trie_string_of_chars chars =
  let buf = Buffer.create (List.length chars) in
  List.iter (Buffer.add_char buf) chars;
  Buffer.contents buf

let trie_insert word trie =
  let chars = trie_chars_of_string word in
  let rec aux chars node =
    match chars with
    | [] -> { node with is_word = true }
    | c :: rest ->
      let child = match CharMap.find_opt c node.children with
        | Some t -> t
        | None -> trie_empty
      in
      let updated_child = aux rest child in
      { node with children = CharMap.add c updated_child node.children }
  in
  aux chars trie

let trie_member word trie =
  let chars = trie_chars_of_string word in
  let rec aux chars node =
    match chars with
    | [] -> node.is_word
    | c :: rest ->
      match CharMap.find_opt c node.children with
      | None -> false
      | Some child -> aux rest child
  in
  aux chars trie

let trie_has_prefix prefix trie =
  let chars = trie_chars_of_string prefix in
  let rec aux chars node =
    match chars with
    | [] -> true
    | c :: rest ->
      match CharMap.find_opt c node.children with
      | None -> false
      | Some child -> aux rest child
  in
  aux chars trie

let trie_find_subtrie prefix trie =
  let chars = trie_chars_of_string prefix in
  let rec aux chars node =
    match chars with
    | [] -> Some node
    | c :: rest ->
      match CharMap.find_opt c node.children with
      | None -> None
      | Some child -> aux rest child
  in
  aux chars trie

let trie_words_with_prefix prefix trie =
  match trie_find_subtrie prefix trie with
  | None -> []
  | Some subtrie ->
    let prefix_chars = trie_chars_of_string prefix in
    let rec collect acc path node =
      let acc = if node.is_word then (trie_string_of_chars (List.rev path)) :: acc else acc in
      CharMap.fold (fun c child acc ->
        collect acc (c :: path) child
      ) node.children acc
    in
    List.rev (collect [] (List.rev prefix_chars) subtrie)

let trie_all_words trie = trie_words_with_prefix "" trie

let trie_word_count trie =
  let rec aux node =
    let count = if node.is_word then 1 else 0 in
    CharMap.fold (fun _ child acc -> acc + aux child) node.children count
  in
  aux trie

let trie_node_count trie =
  let rec aux node =
    1 + CharMap.fold (fun _ child acc -> acc + aux child) node.children 0
  in
  aux trie

let trie_delete word trie =
  let chars = trie_chars_of_string word in
  let rec aux chars node =
    match chars with
    | [] ->
      if not node.is_word then node
      else { node with is_word = false }
    | c :: rest ->
      match CharMap.find_opt c node.children with
      | None -> node
      | Some child ->
        let updated_child = aux rest child in
        if not updated_child.is_word && CharMap.is_empty updated_child.children then
          { node with children = CharMap.remove c node.children }
        else
          { node with children = CharMap.add c updated_child node.children }
  in
  aux chars trie

let trie_longest_common_prefix trie =
  let rec aux node =
    if node.is_word && not (CharMap.is_empty node.children) then ""
    else if node.is_word then ""
    else
      match CharMap.bindings node.children with
      | [(c, child)] -> String.make 1 c ^ aux child
      | _ -> ""
  in
  if CharMap.is_empty trie.children then ""
  else aux trie

let trie_of_list words =
  List.fold_left (fun t w -> trie_insert w t) trie_empty words

(* ===== Parser combinator functions (from parser.ml) ===== *)

type 'a parse_result =
  | ParseOk of 'a * int
  | ParseError of string * int

type 'a parser_t = string -> int -> 'a parse_result

let p_satisfy (pred : char -> bool) (desc : string) : char parser_t =
  fun input pos ->
    if pos >= String.length input then
      ParseError (Printf.sprintf "unexpected end of input, expected %s" desc, pos)
    else
      let c = input.[pos] in
      if pred c then ParseOk (c, pos + 1)
      else ParseError (Printf.sprintf "expected %s, got '%c'" desc c, pos)

let p_char (expected : char) : char parser_t =
  p_satisfy (fun c -> c = expected) (Printf.sprintf "'%c'" expected)

let p_string (expected : string) : string parser_t =
  fun input pos ->
    let len = String.length expected in
    if pos + len > String.length input then
      ParseError (Printf.sprintf "expected \"%s\"" expected, pos)
    else
      let sub = String.sub input pos len in
      if sub = expected then ParseOk (expected, pos + len)
      else ParseError (Printf.sprintf "expected \"%s\", got \"%s\"" expected sub, pos)

let p_return (x : 'a) : 'a parser_t =
  fun _input pos -> ParseOk (x, pos)

let p_fail (msg : string) : 'a parser_t =
  fun _input pos -> ParseError (msg, pos)

let p_bind (p : 'a parser_t) (f : 'a -> 'b parser_t) : 'b parser_t =
  fun input pos ->
    match p input pos with
    | ParseError (msg, epos) -> ParseError (msg, epos)
    | ParseOk (a, pos') -> (f a) input pos'

let ( >>~ ) = p_bind

let p_seq_right (p1 : 'a parser_t) (p2 : 'b parser_t) : 'b parser_t =
  p1 >>~ fun _ -> p2

let p_seq_left (p1 : 'a parser_t) (p2 : 'b parser_t) : 'a parser_t =
  p1 >>~ fun a -> p2 >>~ fun _ -> p_return a

let p_map (f : 'a -> 'b) (p : 'a parser_t) : 'b parser_t =
  p >>~ fun a -> p_return (f a)

let p_choice (p1 : 'a parser_t) (p2 : 'a parser_t) : 'a parser_t =
  fun input pos ->
    match p1 input pos with
    | ParseOk _ as result -> result
    | ParseError (_, epos1) as err ->
      if epos1 = pos then p2 input pos
      else err

let p_many (p : 'a parser_t) : 'a list parser_t =
  fun input pos ->
    let rec aux acc pos =
      match p input pos with
      | ParseError _ -> ParseOk (List.rev acc, pos)
      | ParseOk (x, pos') ->
        if pos' = pos then ParseOk (List.rev acc, pos)
        else aux (x :: acc) pos'
    in
    aux [] pos

let p_many1 (p : 'a parser_t) : 'a list parser_t =
  p >>~ fun first ->
  p_many p >>~ fun rest ->
  p_return (first :: rest)

let p_sep_by (p : 'a parser_t) (sep : 'b parser_t) : 'a list parser_t =
  p_choice
    (p >>~ fun first ->
     p_many (p_seq_right sep p) >>~ fun rest ->
     p_return (first :: rest))
    (p_return [])

let p_between (open_p : 'a parser_t) (close_p : 'b parser_t) (p : 'c parser_t) : 'c parser_t =
  p_seq_right open_p (p_seq_left p close_p)

let p_optional (p : 'a parser_t) : 'a option parser_t =
  p_choice (p_map (fun x -> Some x) p) (p_return None)

let p_digit : char parser_t =
  p_satisfy (fun c -> c >= '0' && c <= '9') "digit"

let p_letter : char parser_t =
  p_satisfy (fun c -> (c >= 'a' && c <= 'z') || (c >= 'A' && c <= 'Z')) "letter"

let p_whitespace : char parser_t =
  p_satisfy (fun c -> c = ' ' || c = '\t' || c = '\n' || c = '\r') "whitespace"

let p_spaces : unit parser_t =
  p_map (fun _ -> ()) (p_many p_whitespace)

let p_lexeme (p : 'a parser_t) : 'a parser_t =
  p_seq_left p p_spaces

let p_natural : int parser_t =
  p_many1 p_digit >>~ fun chars ->
  let s = String.init (List.length chars) (List.nth chars) in
  p_return (int_of_string s)

let p_integer : int parser_t =
  p_optional (p_char '-') >>~ fun sign ->
  p_natural >>~ fun n ->
  p_return (match sign with Some _ -> -n | None -> n)

let p_quoted_string : string parser_t =
  p_seq_right (p_char '"')
    (p_many (p_satisfy (fun c -> c <> '"') "non-quote") >>~ fun chars ->
     p_seq_right (p_char '"')
       (p_return (String.init (List.length chars) (List.nth chars))))

let p_identifier : string parser_t =
  p_letter >>~ fun first ->
  p_many (p_satisfy (fun c ->
    (c >= 'a' && c <= 'z') || (c >= 'A' && c <= 'Z') ||
    (c >= '0' && c <= '9') || c = '_') "alphanumeric") >>~ fun rest ->
  p_return (String.init (1 + List.length rest) (fun i ->
    if i = 0 then first else List.nth rest (i - 1)))

let p_chainl1 (p : 'a parser_t) (op : ('a -> 'a -> 'a) parser_t) : 'a parser_t =
  p >>~ fun first ->
  let rec aux acc =
    p_choice
      (op >>~ fun f ->
       p >>~ fun b ->
       aux (f acc b))
      (p_return acc)
  in
  aux first

let p_chainr1 (p : 'a parser_t) (op : ('a -> 'a -> 'a) parser_t) : 'a parser_t =
  let rec aux () =
    p >>~ fun a ->
    p_choice
      (op >>~ fun f ->
       aux () >>~ fun b ->
       p_return (f a b))
      (p_return a)
  in
  aux ()

let p_run (p : 'a parser_t) (input : string) : ('a, string) result =
  match (p_seq_left p p_spaces) input 0 with
  | ParseOk (value, pos) ->
    if pos = String.length input then Ok value
    else Error (Printf.sprintf "unexpected character '%c' at position %d"
      input.[pos] pos)
  | ParseError (msg, pos) ->
    Error (Printf.sprintf "%s at position %d" msg pos)

(* Arithmetic expression types for parser tests *)
type test_expr =
  | TNum of int
  | TAdd of test_expr * test_expr
  | TSub of test_expr * test_expr
  | TMul of test_expr * test_expr
  | TDiv of test_expr * test_expr
  | TPow of test_expr * test_expr

let rec test_eval = function
  | TNum n -> n
  | TAdd (a, b) -> test_eval a + test_eval b
  | TSub (a, b) -> test_eval a - test_eval b
  | TMul (a, b) -> test_eval a * test_eval b
  | TDiv (a, b) -> test_eval a / test_eval b
  | TPow (a, b) ->
    let rec power b e = if e = 0 then 1 else b * power b (e - 1) in
    power (test_eval a) (test_eval b)

(* Build the expression parser for tests *)
let test_expr_ref : test_expr parser_t ref = ref (p_fail "not initialized")

let test_atom : test_expr parser_t =
  p_lexeme (
    p_choice
      (p_map (fun n -> TNum n) p_integer)
      (p_seq_right (p_char '(') (p_seq_right p_spaces
        ((fun input pos -> !test_expr_ref input pos) |>
         (fun p -> p_seq_left p (p_seq_left p_spaces (p_char ')'))))))
  )

let test_power : test_expr parser_t =
  let pow_op = p_seq_right (p_lexeme (p_char '^')) (p_return (fun a b -> TPow (a, b))) in
  p_chainr1 test_atom pow_op

let test_term : test_expr parser_t =
  let mul_op = p_choice
    (p_seq_right (p_lexeme (p_char '*')) (p_return (fun a b -> TMul (a, b))))
    (p_seq_right (p_lexeme (p_char '/')) (p_return (fun a b -> TDiv (a, b))))
  in
  p_chainl1 test_power mul_op

let test_expr_p : test_expr parser_t =
  let add_op = p_choice
    (p_seq_right (p_lexeme (p_char '+')) (p_return (fun a b -> TAdd (a, b))))
    (p_seq_right (p_lexeme (p_char '-')) (p_return (fun a b -> TSub (a, b))))
  in
  p_chainl1 test_term add_op

let () = test_expr_ref := test_expr_p

let test_calc (input : string) : (int, string) result =
  match p_run (p_seq_right p_spaces test_expr_p) input with
  | Ok expr -> Ok (test_eval expr)
  | Error msg -> Error msg

(* ===== Parser combinator tests ===== *)

let test_parser () = suite "Parser Combinators" (fun () ->
  (* --- Primitive parsers --- *)

  (* satisfy / char_ *)
  assert_true ~msg:"char 'a' on \"abc\""
    (p_run (p_char 'a') "a" = Ok 'a');
  assert_true ~msg:"char 'a' on \"b\" fails"
    (match p_run (p_char 'a') "b" with Error _ -> true | _ -> false);
  assert_true ~msg:"char on empty fails"
    (match p_run (p_char 'a') "" with Error _ -> true | _ -> false);

  (* digit *)
  assert_true ~msg:"digit on \"5\"" (p_run p_digit "5" = Ok '5');
  assert_true ~msg:"digit on \"a\" fails"
    (match p_run p_digit "a" with Error _ -> true | _ -> false);

  (* letter *)
  assert_true ~msg:"letter on \"x\"" (p_run p_letter "x" = Ok 'x');
  assert_true ~msg:"letter on \"Z\"" (p_run p_letter "Z" = Ok 'Z');
  assert_true ~msg:"letter on \"3\" fails"
    (match p_run p_letter "3" with Error _ -> true | _ -> false);

  (* string_ *)
  assert_true ~msg:"string \"hello\""
    (p_run (p_string "hello") "hello" = Ok "hello");
  assert_true ~msg:"string \"hello\" on \"help\" fails"
    (match p_run (p_string "hello") "help" with Error _ -> true | _ -> false);
  assert_true ~msg:"string on too short input fails"
    (match p_run (p_string "hello") "hel" with Error _ -> true | _ -> false);

  (* return_ and fail *)
  assert_true ~msg:"return 42" (p_run (p_return 42) "" = Ok 42);
  assert_true ~msg:"fail always fails"
    (match p_run (p_fail "nope") "" with Error _ -> true | _ -> false);

  (* --- Number parsing --- *)
  assert_true ~msg:"natural 42" (p_run p_natural "42" = Ok 42);
  assert_true ~msg:"natural 0" (p_run p_natural "0" = Ok 0);
  assert_true ~msg:"natural 12345" (p_run p_natural "12345" = Ok 12345);

  assert_true ~msg:"integer 42" (p_run p_integer "42" = Ok 42);
  assert_true ~msg:"integer -7" (p_run p_integer "-7" = Ok (-7));
  assert_true ~msg:"integer 0" (p_run p_integer "0" = Ok 0);
  assert_true ~msg:"integer on \"abc\" fails"
    (match p_run p_integer "abc" with Error _ -> true | _ -> false);

  (* --- Combinators --- *)

  (* bind / sequencing *)
  let two_chars = p_bind (p_char 'a') (fun a ->
    p_bind (p_char 'b') (fun b ->
      p_return (String.init 2 (fun i -> if i = 0 then a else b)))) in
  assert_true ~msg:"bind ab" (p_run two_chars "ab" = Ok "ab");
  assert_true ~msg:"bind ac fails"
    (match p_run two_chars "ac" with Error _ -> true | _ -> false);

  (* map *)
  assert_true ~msg:"map digit to int"
    (p_run (p_map (fun c -> Char.code c - Char.code '0') p_digit) "7" = Ok 7);

  (* choice *)
  let a_or_b = p_choice (p_char 'a') (p_char 'b') in
  assert_true ~msg:"choice a" (p_run a_or_b "a" = Ok 'a');
  assert_true ~msg:"choice b" (p_run a_or_b "b" = Ok 'b');
  assert_true ~msg:"choice c fails"
    (match p_run a_or_b "c" with Error _ -> true | _ -> false);

  (* many *)
  assert_true ~msg:"many digit on \"123\""
    (p_run (p_many p_digit) "123" = Ok ['1'; '2'; '3']);
  assert_true ~msg:"many digit on \"\" is []"
    (p_run (p_many p_digit) "" = Ok []);
  assert_true ~msg:"many digit on \"abc\" is []"
    (p_run (p_many p_digit) "abc" = Ok []);

  (* many1 *)
  assert_true ~msg:"many1 digit on \"123\""
    (p_run (p_many1 p_digit) "123" = Ok ['1'; '2'; '3']);
  assert_true ~msg:"many1 digit on \"\" fails"
    (match p_run (p_many1 p_digit) "" with Error _ -> true | _ -> false);

  (* sep_by *)
  let csv_ints = p_sep_by (p_lexeme p_integer) (p_lexeme (p_char ',')) in
  assert_true ~msg:"sep_by [1,2,3]"
    (p_run csv_ints "1, 2, 3" = Ok [1; 2; 3]);
  assert_true ~msg:"sep_by single"
    (p_run csv_ints "42" = Ok [42]);
  assert_true ~msg:"sep_by empty"
    (p_run csv_ints "" = Ok []);

  (* between *)
  let bracketed = p_between (p_char '[') (p_char ']') p_natural in
  assert_true ~msg:"between [42]"
    (p_run bracketed "[42]" = Ok 42);
  assert_true ~msg:"between missing close fails"
    (match p_run bracketed "[42" with Error _ -> true | _ -> false);

  (* optional *)
  assert_true ~msg:"optional present"
    (p_run (p_optional (p_char 'x')) "x" = Ok (Some 'x'));
  assert_true ~msg:"optional absent"
    (p_run (p_optional (p_char 'x')) "" = Ok None);

  (* --- Quoted string --- *)
  assert_true ~msg:"quoted string"
    (p_run p_quoted_string "\"hello\"" = Ok "hello");
  assert_true ~msg:"quoted empty string"
    (p_run p_quoted_string "\"\"" = Ok "");
  assert_true ~msg:"quoted with spaces"
    (p_run p_quoted_string "\"hello world\"" = Ok "hello world");

  (* --- Identifier --- *)
  assert_true ~msg:"identifier hello"
    (p_run p_identifier "hello" = Ok "hello");
  assert_true ~msg:"identifier x42"
    (p_run p_identifier "x42" = Ok "x42");
  assert_true ~msg:"identifier my_var"
    (p_run p_identifier "my_var" = Ok "my_var");
  assert_true ~msg:"identifier starting with digit fails"
    (match p_run p_identifier "123bad" with Error _ -> true | _ -> false);

  (* --- Integer list parser --- *)
  let p_int_list = p_between
    (p_lexeme (p_char '[')) (p_lexeme (p_char ']'))
    (p_sep_by (p_lexeme p_integer) (p_lexeme (p_char ','))) in
  assert_true ~msg:"int list [1, 2, 3]"
    (p_run p_int_list "[1, 2, 3]" = Ok [1; 2; 3]);
  assert_true ~msg:"int list []"
    (p_run p_int_list "[]" = Ok []);
  assert_true ~msg:"int list [42]"
    (p_run p_int_list "[42]" = Ok [42]);
  assert_true ~msg:"int list [10, 20, 30, 40, 50]"
    (p_run p_int_list "[10, 20, 30, 40, 50]" = Ok [10; 20; 30; 40; 50]);

  (* --- Key-value parser --- *)
  let kv = p_lexeme p_identifier >>~ fun key ->
    p_seq_right (p_lexeme (p_char '='))
      (p_lexeme p_quoted_string >>~ fun value ->
       p_return (key, value)) in
  assert_true ~msg:"kv parse"
    (p_run kv "name = \"Alice\"" = Ok ("name", "Alice"));

  (* --- Arithmetic expression parser --- *)

  (* Simple numbers *)
  assert_true ~msg:"calc 42" (test_calc "42" = Ok 42);
  assert_true ~msg:"calc 0" (test_calc "0" = Ok 0);
  assert_true ~msg:"calc -5" (test_calc "-5" = Ok (-5));

  (* Basic operations *)
  assert_true ~msg:"calc 2+3" (test_calc "2 + 3" = Ok 5);
  assert_true ~msg:"calc 10-3" (test_calc "10 - 3" = Ok 7);
  assert_true ~msg:"calc 4*5" (test_calc "4 * 5" = Ok 20);
  assert_true ~msg:"calc 20/4" (test_calc "20 / 4" = Ok 5);

  (* Precedence: * binds tighter than + *)
  assert_true ~msg:"calc 2+3*4=14" (test_calc "2 + 3 * 4" = Ok 14);
  assert_true ~msg:"calc 2*3+4=10" (test_calc "2 * 3 + 4" = Ok 10);

  (* Parentheses override precedence *)
  assert_true ~msg:"calc (2+3)*4=20" (test_calc "(2 + 3) * 4" = Ok 20);
  assert_true ~msg:"calc 2*(3+4)=14" (test_calc "2 * (3 + 4)" = Ok 14);

  (* Left associativity *)
  assert_true ~msg:"calc 10-3-2=5" (test_calc "10 - 3 - 2" = Ok 5);
  assert_true ~msg:"calc 100/5/4=5" (test_calc "100 / 5 / 4" = Ok 5);

  (* Right associativity of ^ *)
  assert_true ~msg:"calc 2^3=8" (test_calc "2 ^ 3" = Ok 8);
  assert_true ~msg:"calc 2^10=1024" (test_calc "2 ^ 10" = Ok 1024);
  assert_true ~msg:"calc 2^3^2=512 (right-assoc)" (test_calc "2 ^ 3 ^ 2" = Ok 512);

  (* Complex expressions *)
  assert_true ~msg:"calc (1+2)*(3+4)=21" (test_calc "(1 + 2) * (3 + 4)" = Ok 21);
  assert_true ~msg:"calc ((3+5)*2)-(10/2)=11"
    (test_calc "((3 + 5) * 2) - (10 / 2)" = Ok 11);
  assert_true ~msg:"calc 1+2+3=6" (test_calc "1 + 2 + 3" = Ok 6);

  (* Whitespace handling *)
  assert_true ~msg:"calc no spaces" (test_calc "2+3" = Ok 5);
  assert_true ~msg:"calc extra spaces" (test_calc "  2  +  3  " = Ok 5);

  (* Error cases *)
  assert_true ~msg:"calc empty fails"
    (match test_calc "" with Error _ -> true | _ -> false);
  assert_true ~msg:"calc invalid fails"
    (match test_calc "+" with Error _ -> true | _ -> false);

  (* --- chainl1 basic test --- *)
  let sum_parser = p_chainl1 (p_lexeme p_natural)
    (p_seq_right (p_lexeme (p_char '+')) (p_return ( + ))) in
  assert_true ~msg:"chainl1 1+2+3" (p_run sum_parser "1 + 2 + 3" = Ok 6);
  assert_true ~msg:"chainl1 single" (p_run sum_parser "42" = Ok 42);

  (* --- chainr1 basic test --- *)
  let pow_parser = p_chainr1 (p_lexeme p_natural)
    (p_seq_right (p_lexeme (p_char '^')) (p_return (fun a b ->
      let rec power b e = if e = 0 then 1 else b * power b (e - 1) in
      power a b))) in
  assert_true ~msg:"chainr1 2^3^2=512" (p_run pow_parser "2 ^ 3 ^ 2" = Ok 512);
  assert_true ~msg:"chainr1 single" (p_run pow_parser "5" = Ok 5);
)

let test_trie () = suite "Trie" (fun () ->
  (* Empty trie *)
  assert_true ~msg:"empty trie word count 0" (trie_word_count trie_empty = 0);
  assert_true ~msg:"empty trie node count 1" (trie_node_count trie_empty = 1);
  assert_true ~msg:"empty trie member false" (not (trie_member "hello" trie_empty));
  assert_true ~msg:"empty trie has_prefix false" (not (trie_has_prefix "a" trie_empty));
  assert_true ~msg:"empty trie all_words empty" (trie_all_words trie_empty = []);
  assert_true ~msg:"empty trie LCP empty" (trie_longest_common_prefix trie_empty = "");

  (* Single word *)
  let t1 = trie_insert "hello" trie_empty in
  assert_true ~msg:"single word member" (trie_member "hello" t1);
  assert_true ~msg:"single word prefix" (trie_has_prefix "hel" t1);
  assert_true ~msg:"single word not member prefix" (not (trie_member "hel" t1));
  assert_true ~msg:"single word count 1" (trie_word_count t1 = 1);
  assert_true ~msg:"single word all_words" (trie_all_words t1 = ["hello"]);

  (* Multiple words *)
  let t = trie_of_list ["apple"; "app"; "application"; "apply"; "apt"] in
  assert_true ~msg:"multi member apple" (trie_member "apple" t);
  assert_true ~msg:"multi member app" (trie_member "app" t);
  assert_true ~msg:"multi member application" (trie_member "application" t);
  assert_true ~msg:"multi member apply" (trie_member "apply" t);
  assert_true ~msg:"multi member apt" (trie_member "apt" t);
  assert_true ~msg:"multi not member ap" (not (trie_member "ap" t));
  assert_true ~msg:"multi not member apples" (not (trie_member "apples" t));
  assert_true ~msg:"multi word count 5" (trie_word_count t = 5);

  (* Prefix search *)
  let app_words = trie_words_with_prefix "app" t in
  assert_true ~msg:"prefix app count 4" (List.length app_words = 4);
  assert_true ~msg:"prefix app has apple" (List.mem "apple" app_words);
  assert_true ~msg:"prefix app has app" (List.mem "app" app_words);
  assert_true ~msg:"prefix app has application" (List.mem "application" app_words);
  assert_true ~msg:"prefix app has apply" (List.mem "apply" app_words);
  assert_true ~msg:"prefix app no apt" (not (List.mem "apt" app_words));

  let ap_words = trie_words_with_prefix "ap" t in
  assert_true ~msg:"prefix ap count 5" (List.length ap_words = 5);

  let apt_words = trie_words_with_prefix "apt" t in
  assert_true ~msg:"prefix apt count 1" (apt_words = ["apt"]);

  let z_words = trie_words_with_prefix "z" t in
  assert_true ~msg:"prefix z empty" (z_words = []);

  (* has_prefix *)
  assert_true ~msg:"has_prefix a" (trie_has_prefix "a" t);
  assert_true ~msg:"has_prefix ap" (trie_has_prefix "ap" t);
  assert_true ~msg:"has_prefix app" (trie_has_prefix "app" t);
  assert_true ~msg:"has_prefix appl" (trie_has_prefix "appl" t);
  assert_true ~msg:"has_prefix not b" (not (trie_has_prefix "b" t));
  assert_true ~msg:"has_prefix empty string" (trie_has_prefix "" t);

  (* Deletion *)
  let t2 = trie_delete "apple" t in
  assert_true ~msg:"deleted apple not member" (not (trie_member "apple" t2));
  assert_true ~msg:"app still member after deleting apple" (trie_member "app" t2);
  assert_true ~msg:"application still member" (trie_member "application" t2);
  assert_true ~msg:"delete word count" (trie_word_count t2 = 4);

  (* Delete word that's prefix of another *)
  let t3 = trie_delete "app" t in
  assert_true ~msg:"deleted app not member" (not (trie_member "app" t3));
  assert_true ~msg:"apple still member after deleting app" (trie_member "apple" t3);
  assert_true ~msg:"delete prefix word count" (trie_word_count t3 = 4);

  (* Delete non-existent word *)
  let t4 = trie_delete "banana" t in
  assert_true ~msg:"delete non-existent no change" (trie_word_count t4 = 5);

  (* Delete all words *)
  let t5 = List.fold_left (fun t w -> trie_delete w t)
    t ["apple"; "app"; "application"; "apply"; "apt"] in
  assert_true ~msg:"delete all word count 0" (trie_word_count t5 = 0);
  assert_true ~msg:"delete all is empty" (trie_all_words t5 = []);

  (* Pruning: nodes should be removed when no longer needed *)
  let tp = trie_of_list ["abc"] in
  let tp2 = trie_delete "abc" tp in
  assert_true ~msg:"pruned trie node count 1" (trie_node_count tp2 = 1);

  (* Persistence — original unchanged *)
  assert_true ~msg:"original still has apple" (trie_member "apple" t);
  assert_true ~msg:"original word count unchanged" (trie_word_count t = 5);

  (* Longest common prefix *)
  let lcp1 = trie_of_list ["flower"; "flow"; "flight"] in
  assert_equal ~msg:"LCP fl" "fl" (trie_longest_common_prefix lcp1);

  let lcp2 = trie_of_list ["test"; "testing"; "tested"; "tester"] in
  assert_equal ~msg:"LCP test" "test" (trie_longest_common_prefix lcp2);

  let lcp3 = trie_of_list ["abc"; "xyz"] in
  assert_equal ~msg:"LCP no common" "" (trie_longest_common_prefix lcp3);

  let lcp4 = trie_of_list ["same"; "same"; "same"] in
  assert_equal ~msg:"LCP all same" "same" (trie_longest_common_prefix lcp4);

  let lcp5 = trie_of_list ["a"; "ab"; "abc"] in
  assert_equal ~msg:"LCP prefix chain" "a" (trie_longest_common_prefix lcp5);

  (* Sorted order *)
  let sorted_t = trie_of_list ["cat"; "car"; "card"; "bat"; "ball"] in
  let all = trie_all_words sorted_t in
  assert_equal ~msg:"all_words sorted" "[ball; bat; car; card; cat]"
    ("[" ^ String.concat "; " all ^ "]");

  (* Empty string as word *)
  let te = trie_insert "" trie_empty in
  assert_true ~msg:"empty string member" (trie_member "" te);
  assert_true ~msg:"empty string word count 1" (trie_word_count te = 1);
  let te2 = trie_delete "" te in
  assert_true ~msg:"empty string deleted" (not (trie_member "" te2));

  (* Duplicate insertion *)
  let td = trie_insert "hello" (trie_insert "hello" trie_empty) in
  assert_true ~msg:"duplicate insert count 1" (trie_word_count td = 1);

  (* Single character words *)
  let tc = trie_of_list ["a"; "b"; "c"] in
  assert_true ~msg:"single char words count 3" (trie_word_count tc = 3);
  assert_true ~msg:"single char member a" (trie_member "a" tc);
  assert_true ~msg:"single char member b" (trie_member "b" tc);
  assert_true ~msg:"single char member c" (trie_member "c" tc);

  (* Words with shared prefixes *)
  let ts = trie_of_list ["do"; "dog"; "dogs"; "done"; "door"] in
  assert_true ~msg:"shared prefix count 5" (trie_word_count ts = 5);
  let do_words = trie_words_with_prefix "do" ts in
  assert_true ~msg:"prefix do has 5 words" (List.length do_words = 5);
  let dog_words = trie_words_with_prefix "dog" ts in
  assert_true ~msg:"prefix dog has 2 words" (List.length dog_words = 2);

  (* find_subtrie *)
  assert_true ~msg:"find_subtrie existing" (trie_find_subtrie "app" t <> None);
  assert_true ~msg:"find_subtrie non-existing" (trie_find_subtrie "xyz" t = None);
  assert_true ~msg:"find_subtrie empty prefix" (trie_find_subtrie "" t <> None);

  (* Node count *)
  let tn = trie_of_list ["ab"; "ac"] in
  (* root -> a -> b*, c* = 4 nodes *)
  assert_true ~msg:"node count ab+ac" (trie_node_count tn = 4);

  (* Large trie *)
  let big_words = List.init 100 (fun i -> Printf.sprintf "word%03d" i) in
  let big_t = trie_of_list big_words in
  assert_true ~msg:"large trie word count 100" (trie_word_count big_t = 100);
  assert_true ~msg:"large trie member word000" (trie_member "word000" big_t);
  assert_true ~msg:"large trie member word099" (trie_member "word099" big_t);
  assert_true ~msg:"large trie prefix word" (List.length (trie_words_with_prefix "word" big_t) = 100);
)

(* ===== Regex functions (from regex.ml) ===== *)

type re_char_matcher =
  | ReLit of char
  | ReDot
  | ReClass of (char * char) list * bool

type re_regex =
  | ReEmpty
  | ReChar of re_char_matcher
  | ReSeq of re_regex * re_regex
  | ReAlt of re_regex * re_regex
  | ReStar of re_regex
  | RePlus of re_regex
  | ReOpt of re_regex
  | ReAnchor_start
  | ReAnchor_end

exception Re_parse_error of string

let re_parse (pattern : string) : re_regex =
  let len = String.length pattern in
  let pos = ref 0 in
  let peek () = if !pos < len then Some pattern.[!pos] else None in
  let advance () = incr pos in
  let expect c =
    match peek () with
    | Some c' when c' = c -> advance ()
    | Some c' -> raise (Re_parse_error (Printf.sprintf "expected '%c', got '%c' at position %d" c c' !pos))
    | None -> raise (Re_parse_error (Printf.sprintf "expected '%c', got end of pattern" c))
  in
  let parse_escape () =
    advance ();
    match peek () with
    | None -> raise (Re_parse_error "unexpected end of pattern after '\\'")
    | Some c ->
      advance ();
      match c with
      | 'd' -> ReChar (ReClass ([('0', '9')], false))
      | 'D' -> ReChar (ReClass ([('0', '9')], true))
      | 'w' -> ReChar (ReClass ([('a', 'z'); ('A', 'Z'); ('0', '9'); ('_', '_')], false))
      | 'W' -> ReChar (ReClass ([('a', 'z'); ('A', 'Z'); ('0', '9'); ('_', '_')], true))
      | 's' -> ReChar (ReClass ([(' ', ' '); ('\t', '\t'); ('\n', '\n'); ('\r', '\r')], false))
      | 'S' -> ReChar (ReClass ([(' ', ' '); ('\t', '\t'); ('\n', '\n'); ('\r', '\r')], true))
      | 'n' -> ReChar (ReLit '\n')
      | 't' -> ReChar (ReLit '\t')
      | 'r' -> ReChar (ReLit '\r')
      | _ -> ReChar (ReLit c)
  in
  let parse_class () =
    advance ();
    let negated = match peek () with
      | Some '^' -> advance (); true
      | _ -> false
    in
    let ranges = ref [] in
    let first = ref true in
    while (match peek () with Some ']' when not !first -> false | Some _ -> true | None -> false) do
      first := false;
      match peek () with
      | None -> raise (Re_parse_error "unterminated character class")
      | Some '\\' ->
        advance ();
        (match peek () with
         | None -> raise (Re_parse_error "unexpected end in character class escape")
         | Some c -> advance (); ranges := (c, c) :: !ranges)
      | Some c ->
        advance ();
        (match peek () with
         | Some '-' ->
           let saved = !pos in
           advance ();
           (match peek () with
            | Some ']' -> pos := saved; ranges := (c, c) :: !ranges
            | Some c2 -> advance (); ranges := (c, c2) :: !ranges
            | None -> pos := saved; ranges := (c, c) :: !ranges)
         | _ -> ranges := (c, c) :: !ranges)
    done;
    expect ']';
    ReChar (ReClass (List.rev !ranges, negated))
  in
  let rec parse_expr () =
    let left = parse_seq () in
    match peek () with
    | Some '|' -> advance (); let right = parse_expr () in ReAlt (left, right)
    | _ -> left
  and parse_seq () =
    let terms = ref [] in
    let continues () = match peek () with None | Some ')' | Some '|' -> false | _ -> true in
    while continues () do terms := parse_quant () :: !terms done;
    match List.rev !terms with
    | [] -> ReEmpty
    | [t] -> t
    | first :: rest -> List.fold_left (fun acc t -> ReSeq (acc, t)) first rest
  and parse_quant () =
    let atom = parse_atom () in
    match peek () with
    | Some '*' -> advance (); ReStar atom
    | Some '+' -> advance (); RePlus atom
    | Some '?' -> advance (); ReOpt atom
    | _ -> atom
  and parse_atom () =
    match peek () with
    | None -> raise (Re_parse_error "unexpected end of pattern")
    | Some '(' -> advance (); let inner = parse_expr () in expect ')'; inner
    | Some '[' -> parse_class ()
    | Some '\\' -> parse_escape ()
    | Some '.' -> advance (); ReChar ReDot
    | Some '^' -> advance (); ReAnchor_start
    | Some '$' -> advance (); ReAnchor_end
    | Some c when c <> ')' && c <> '|' && c <> '*' && c <> '+' && c <> '?' ->
      advance (); ReChar (ReLit c)
    | Some c -> raise (Re_parse_error (Printf.sprintf "unexpected '%c' at position %d" c !pos))
  in
  let result = parse_expr () in
  if !pos <> len then
    raise (Re_parse_error (Printf.sprintf "unexpected character '%c' at position %d" pattern.[!pos] !pos));
  result

(* NFA *)
type re_nfa_transition =
  | ReEpsilon of int
  | ReOn_char of re_char_matcher * int
  | ReOn_anchor_start of int
  | ReOn_anchor_end of int

type re_nfa = {
  re_start: int;
  re_accept: int;
  re_transitions: re_nfa_transition list array;
  re_num_states: int;
}

type re_fragment = { re_frag_start: int; re_frag_accept: int }

let re_build_nfa (r : re_regex) : re_nfa =
  let next_id = ref 0 in
  let new_state () = let id = !next_id in incr next_id; id in
  let trans_table : (int * re_nfa_transition) list ref = ref [] in
  let add_trans src t = trans_table := (src, t) :: !trans_table in
  let rec build r =
    match r with
    | ReEmpty ->
      let s = new_state () in let a = new_state () in
      add_trans s (ReEpsilon a);
      { re_frag_start = s; re_frag_accept = a }
    | ReChar matcher ->
      let s = new_state () in let a = new_state () in
      add_trans s (ReOn_char (matcher, a));
      { re_frag_start = s; re_frag_accept = a }
    | ReSeq (r1, r2) ->
      let f1 = build r1 in let f2 = build r2 in
      add_trans f1.re_frag_accept (ReEpsilon f2.re_frag_start);
      { re_frag_start = f1.re_frag_start; re_frag_accept = f2.re_frag_accept }
    | ReAlt (r1, r2) ->
      let f1 = build r1 in let f2 = build r2 in
      let s = new_state () in let a = new_state () in
      add_trans s (ReEpsilon f1.re_frag_start);
      add_trans s (ReEpsilon f2.re_frag_start);
      add_trans f1.re_frag_accept (ReEpsilon a);
      add_trans f2.re_frag_accept (ReEpsilon a);
      { re_frag_start = s; re_frag_accept = a }
    | ReStar r1 ->
      let f = build r1 in
      let s = new_state () in let a = new_state () in
      add_trans s (ReEpsilon f.re_frag_start);
      add_trans s (ReEpsilon a);
      add_trans f.re_frag_accept (ReEpsilon f.re_frag_start);
      add_trans f.re_frag_accept (ReEpsilon a);
      { re_frag_start = s; re_frag_accept = a }
    | RePlus r1 ->
      let f = build r1 in
      let s = new_state () in let a = new_state () in
      add_trans s (ReEpsilon f.re_frag_start);
      add_trans f.re_frag_accept (ReEpsilon f.re_frag_start);
      add_trans f.re_frag_accept (ReEpsilon a);
      { re_frag_start = s; re_frag_accept = a }
    | ReOpt r1 ->
      let f = build r1 in
      let s = new_state () in let a = new_state () in
      add_trans s (ReEpsilon f.re_frag_start);
      add_trans s (ReEpsilon a);
      add_trans f.re_frag_accept (ReEpsilon a);
      { re_frag_start = s; re_frag_accept = a }
    | ReAnchor_start ->
      let s = new_state () in let a = new_state () in
      add_trans s (ReOn_anchor_start a);
      { re_frag_start = s; re_frag_accept = a }
    | ReAnchor_end ->
      let s = new_state () in let a = new_state () in
      add_trans s (ReOn_anchor_end a);
      { re_frag_start = s; re_frag_accept = a }
  in
  let frag = build r in
  let n = !next_id in
  let arr = Array.make n [] in
  List.iter (fun (src, t) -> arr.(src) <- t :: arr.(src)) !trans_table;
  { re_start = frag.re_frag_start; re_accept = frag.re_frag_accept;
    re_transitions = arr; re_num_states = n }

let re_char_matches (m : re_char_matcher) (c : char) : bool =
  match m with
  | ReLit expected -> c = expected
  | ReDot -> c <> '\n'
  | ReClass (ranges, negated) ->
    let in_range = List.exists (fun (lo, hi) -> c >= lo && c <= hi) ranges in
    if negated then not in_range else in_range

let re_epsilon_closure (nfa : re_nfa) (state_ids : int list) (input : string) (str_pos : int) : int list =
  let visited = Hashtbl.create 16 in
  let result = ref [] in
  let rec explore id =
    if Hashtbl.mem visited id then ()
    else begin
      Hashtbl.replace visited id true;
      result := id :: !result;
      List.iter (fun t ->
        match t with
        | ReEpsilon target -> explore target
        | ReOn_anchor_start target -> if str_pos = 0 then explore target
        | ReOn_anchor_end target -> if str_pos = String.length input then explore target
        | ReOn_char _ -> ()
      ) nfa.re_transitions.(id)
    end
  in
  List.iter explore state_ids;
  !result

let re_simulate_at (nfa : re_nfa) (input : string) (start_pos : int) : int option =
  let len = String.length input in
  let current = ref (re_epsilon_closure nfa [nfa.re_start] input start_pos) in
  let last_match = ref (if List.mem nfa.re_accept !current then Some 0 else None) in
  let i = ref start_pos in
  while !i < len && !current <> [] do
    let c = input.[!i] in
    let next = List.fold_left (fun acc state_id ->
      List.fold_left (fun acc2 t ->
        match t with
        | ReOn_char (matcher, target) ->
          if re_char_matches matcher c then target :: acc2 else acc2
        | _ -> acc2
      ) acc nfa.re_transitions.(state_id)
    ) [] !current in
    incr i;
    current := re_epsilon_closure nfa next input !i;
    if List.mem nfa.re_accept !current then
      last_match := Some (!i - start_pos)
  done;
  !last_match

type re_compiled = {
  re_pattern: string;
  re_ast: re_regex;
  re_nfa_c: re_nfa;
  re_anchored_start: bool;
}

let re_compile (pattern : string) : re_compiled =
  let ast = re_parse pattern in
  let nfa = re_build_nfa ast in
  let anchored_start = match ast with
    | ReAnchor_start -> true
    | ReSeq (ReAnchor_start, _) -> true
    | _ -> false
  in
  { re_pattern = pattern; re_ast = ast; re_nfa_c = nfa; re_anchored_start = anchored_start }

let re_matches (re : re_compiled) (input : string) : bool =
  match re_simulate_at re.re_nfa_c input 0 with
  | Some n -> n = String.length input
  | None -> false

let re_find (re : re_compiled) (input : string) : (int * string) option =
  let len = String.length input in
  let i = ref 0 in
  let result = ref None in
  while !i <= len && !result = None do
    (match re_simulate_at re.re_nfa_c input !i with
     | Some match_len -> result := Some (!i, String.sub input !i match_len)
     | None -> ());
    if !result = None then (
      if re.re_anchored_start then i := len + 1
      else incr i
    )
  done;
  !result

let re_find_all (re : re_compiled) (input : string) : string list =
  let len = String.length input in
  let results = ref [] in
  let i = ref 0 in
  while !i <= len do
    match re_simulate_at re.re_nfa_c input !i with
    | Some match_len when match_len > 0 ->
      results := String.sub input !i match_len :: !results;
      i := !i + match_len
    | Some _ -> results := "" :: !results; incr i
    | None -> incr i
  done;
  List.rev !results

let re_replace (re : re_compiled) (input : string) (replacement : string) : string =
  let len = String.length input in
  let buf = Buffer.create (String.length input) in
  let i = ref 0 in
  while !i <= len do
    match re_simulate_at re.re_nfa_c input !i with
    | Some match_len when match_len > 0 ->
      Buffer.add_string buf replacement;
      i := !i + match_len
    | Some _ ->
      Buffer.add_string buf replacement;
      if !i < len then Buffer.add_char buf input.[!i];
      incr i
    | None ->
      if !i < len then Buffer.add_char buf input.[!i];
      incr i
  done;
  Buffer.contents buf

let re_split (re : re_compiled) (input : string) : string list =
  let len = String.length input in
  let parts = ref [] in
  let seg_start = ref 0 in
  let i = ref 0 in
  while !i <= len do
    match re_simulate_at re.re_nfa_c input !i with
    | Some match_len when match_len > 0 ->
      parts := String.sub input !seg_start (!i - !seg_start) :: !parts;
      i := !i + match_len;
      seg_start := !i
    | _ -> incr i
  done;
  parts := String.sub input !seg_start (len - !seg_start) :: !parts;
  List.rev !parts

let rec re_ast_to_string = function
  | ReEmpty -> "ε"
  | ReChar (ReLit c) -> String.make 1 c
  | ReChar ReDot -> "."
  | ReChar (ReClass (ranges, negated)) ->
    let range_str = String.concat ""
      (List.map (fun (lo, hi) ->
        if lo = hi then String.make 1 lo
        else Printf.sprintf "%c-%c" lo hi
      ) ranges) in
    Printf.sprintf "[%s%s]" (if negated then "^" else "") range_str
  | ReSeq (r1, r2) -> re_ast_to_string r1 ^ re_ast_to_string r2
  | ReAlt (r1, r2) -> Printf.sprintf "(%s|%s)" (re_ast_to_string r1) (re_ast_to_string r2)
  | ReStar r -> Printf.sprintf "(%s)*" (re_ast_to_string r)
  | RePlus r -> Printf.sprintf "(%s)+" (re_ast_to_string r)
  | ReOpt r -> Printf.sprintf "(%s)?" (re_ast_to_string r)
  | ReAnchor_start -> "^"
  | ReAnchor_end -> "$"

let string_of_find_result = function
  | None -> "None"
  | Some (pos, s) -> Printf.sprintf "Some(%d, \"%s\")" pos s

(* ===== Regex tests ===== *)

let test_regex () = suite "Regex" (fun () ->
  (* --- Parser tests --- *)

  (* Literal *)
  assert_equal ~msg:"parse literal"
    "abc" (re_ast_to_string (re_parse "abc"));

  (* Quantifiers *)
  assert_equal ~msg:"parse star"
    "(a)*" (re_ast_to_string (re_parse "a*"));
  assert_equal ~msg:"parse plus"
    "(a)+" (re_ast_to_string (re_parse "a+"));
  assert_equal ~msg:"parse optional"
    "(a)?" (re_ast_to_string (re_parse "a?"));
  assert_equal ~msg:"parse combined quant"
    "a(b)+c" (re_ast_to_string (re_parse "ab+c"));

  (* Alternation *)
  assert_equal ~msg:"parse alt"
    "(cat|dog)" (re_ast_to_string (re_parse "cat|dog"));

  (* Dot *)
  assert_equal ~msg:"parse dot"
    "h.t" (re_ast_to_string (re_parse "h.t"));

  (* Character class *)
  assert_equal ~msg:"parse class"
    "[a-z]" (re_ast_to_string (re_parse "[a-z]"));
  assert_equal ~msg:"parse negated class"
    "[^0-9]" (re_ast_to_string (re_parse "[^0-9]"));

  (* Anchors *)
  assert_equal ~msg:"parse anchor start"
    "^hello" (re_ast_to_string (re_parse "^hello"));
  assert_equal ~msg:"parse anchor end"
    "world$" (re_ast_to_string (re_parse "world$"));

  (* Grouping *)
  assert_equal ~msg:"parse group"
    "((ab))*" (re_ast_to_string (re_parse "(ab)*"));

  (* Escape *)
  assert_equal ~msg:"parse escape dot"
    "a.b" (re_ast_to_string (re_parse "a\\.b"));

  (* Parse errors *)
  assert_raises ~msg:"parse unmatched paren" (fun () -> re_parse "(abc");
  assert_raises ~msg:"parse empty group" (fun () -> re_parse "*)");
  assert_raises ~msg:"parse bad quantifier" (fun () -> re_parse "+abc");

  (* --- Basic matching --- *)

  let r1 = re_compile "hello" in
  assert_true ~msg:"match literal hello" (re_matches r1 "hello");
  assert_true ~msg:"no match world" (not (re_matches r1 "world"));
  assert_true ~msg:"no match partial" (not (re_matches r1 "hell"));
  assert_true ~msg:"no match longer" (not (re_matches r1 "hello!"));
  assert_true ~msg:"no match empty" (not (re_matches r1 ""));

  (* Empty pattern matches empty string *)
  let r_empty = re_compile "" in
  assert_true ~msg:"empty pattern matches empty" (re_matches r_empty "");
  assert_true ~msg:"empty pattern no match non-empty" (not (re_matches r_empty "a"));

  (* Single char *)
  let r_a = re_compile "a" in
  assert_true ~msg:"single char match" (re_matches r_a "a");
  assert_true ~msg:"single char no match" (not (re_matches r_a "b"));

  (* --- Quantifiers --- *)

  (* Star *)
  let r_star = re_compile "ab*c" in
  assert_true ~msg:"star zero" (re_matches r_star "ac");
  assert_true ~msg:"star one" (re_matches r_star "abc");
  assert_true ~msg:"star many" (re_matches r_star "abbbbc");
  assert_true ~msg:"star no match" (not (re_matches r_star "adc"));

  (* Plus *)
  let r_plus = re_compile "ab+c" in
  assert_true ~msg:"plus one" (re_matches r_plus "abc");
  assert_true ~msg:"plus many" (re_matches r_plus "abbbbc");
  assert_true ~msg:"plus zero fails" (not (re_matches r_plus "ac"));

  (* Optional *)
  let r_opt = re_compile "colou?r" in
  assert_true ~msg:"opt absent" (re_matches r_opt "color");
  assert_true ~msg:"opt present" (re_matches r_opt "colour");
  assert_true ~msg:"opt no match" (not (re_matches r_opt "colouur"));

  (* --- Alternation --- *)

  let r_alt = re_compile "cat|dog" in
  assert_true ~msg:"alt first" (re_matches r_alt "cat");
  assert_true ~msg:"alt second" (re_matches r_alt "dog");
  assert_true ~msg:"alt no match" (not (re_matches r_alt "cow"));
  assert_true ~msg:"alt no match partial" (not (re_matches r_alt "ca"));

  (* Multi-way alternation *)
  let r_alt3 = re_compile "a|b|c" in
  assert_true ~msg:"alt3 a" (re_matches r_alt3 "a");
  assert_true ~msg:"alt3 b" (re_matches r_alt3 "b");
  assert_true ~msg:"alt3 c" (re_matches r_alt3 "c");
  assert_true ~msg:"alt3 no match" (not (re_matches r_alt3 "d"));

  (* --- Dot --- *)

  let r_dot = re_compile "h.t" in
  assert_true ~msg:"dot hat" (re_matches r_dot "hat");
  assert_true ~msg:"dot hot" (re_matches r_dot "hot");
  assert_true ~msg:"dot hit" (re_matches r_dot "hit");
  assert_true ~msg:"dot no match long" (not (re_matches r_dot "heart"));
  assert_true ~msg:"dot no match short" (not (re_matches r_dot "ht"));

  (* Dot doesn't match newline *)
  assert_true ~msg:"dot no newline" (not (re_matches r_dot "h\nt"));

  (* --- Character classes --- *)

  let r_vowel = re_compile "[aeiou]+" in
  assert_true ~msg:"class vowels" (re_matches r_vowel "aei");
  assert_true ~msg:"class no match" (not (re_matches r_vowel "xyz"));

  let r_range = re_compile "[a-z]+" in
  assert_true ~msg:"range lower" (re_matches r_range "hello");
  assert_true ~msg:"range no upper" (not (re_matches r_range "HELLO"));
  assert_true ~msg:"range no digits" (not (re_matches r_range "123"));

  let r_multi_range = re_compile "[a-zA-Z]+" in
  assert_true ~msg:"multi range" (re_matches r_multi_range "Hello");

  (* Negated class *)
  let r_neg = re_compile "[^0-9]+" in
  assert_true ~msg:"neg class letters" (re_matches r_neg "hello");
  assert_true ~msg:"neg class no digits" (not (re_matches r_neg "123"));
  assert_true ~msg:"neg class mixed" (not (re_matches r_neg "abc123"));

  (* --- Shorthand classes --- *)

  let r_digit = re_compile "\\d+" in
  assert_true ~msg:"\\d digits" (re_matches r_digit "123");
  assert_true ~msg:"\\d no letters" (not (re_matches r_digit "abc"));

  let r_ndigit = re_compile "\\D+" in
  assert_true ~msg:"\\D letters" (re_matches r_ndigit "abc");
  assert_true ~msg:"\\D no digits" (not (re_matches r_ndigit "123"));

  let r_word = re_compile "\\w+" in
  assert_true ~msg:"\\w word" (re_matches r_word "hello");
  assert_true ~msg:"\\w mixed" (re_matches r_word "hi_42");
  assert_true ~msg:"\\w no space" (not (re_matches r_word "hi there"));

  let r_space = re_compile "\\s+" in
  assert_true ~msg:"\\s spaces" (re_matches r_space "   ");
  assert_true ~msg:"\\s tab" (re_matches r_space "\t");
  assert_true ~msg:"\\s no letters" (not (re_matches r_space "abc"));

  (* --- Grouping --- *)

  let r_group = re_compile "(ab)+" in
  assert_true ~msg:"group repeat" (re_matches r_group "ababab");
  assert_true ~msg:"group single" (re_matches r_group "ab");
  assert_true ~msg:"group no match" (not (re_matches r_group "aab"));

  let r_nested = re_compile "((a|b)c)+" in
  assert_true ~msg:"nested group ac" (re_matches r_nested "ac");
  assert_true ~msg:"nested group bc" (re_matches r_nested "bc");
  assert_true ~msg:"nested group repeat" (re_matches r_nested "acbc");

  (* --- Anchors --- *)

  let r_start = re_compile "^hello" in
  assert_equal ~msg:"anchor start find"
    "Some(0, \"hello\")" (string_of_find_result (re_find r_start "hello world"));
  assert_equal ~msg:"anchor start no find"
    "None" (string_of_find_result (re_find r_start "say hello"));

  let r_end = re_compile "world$" in
  assert_equal ~msg:"anchor end find"
    "Some(6, \"world\")" (string_of_find_result (re_find r_end "hello world"));
  assert_equal ~msg:"anchor end no find"
    "None" (string_of_find_result (re_find r_end "world peace"));

  let r_both = re_compile "^hello$" in
  assert_true ~msg:"both anchors match" (re_matches r_both "hello");
  assert_true ~msg:"both anchors no match" (not (re_matches r_both "hello world"));

  (* --- Find --- *)

  let r_num = re_compile "[0-9]+" in
  assert_equal ~msg:"find first number"
    "Some(4, \"123\")" (string_of_find_result (re_find r_num "abc 123 def 456"));
  assert_equal ~msg:"find no match"
    "None" (string_of_find_result (re_find r_num "no numbers here"));

  let r_word_f = re_compile "[a-z]+" in
  assert_equal ~msg:"find first word"
    "Some(0, \"hello\")" (string_of_find_result (re_find r_word_f "hello world"));

  (* --- Find All --- *)

  let found = re_find_all r_num "abc 123 def 456 ghi" in
  assert_equal ~msg:"find_all numbers"
    "[123; 456]" (string_of_int_list (List.map int_of_string found));

  let words_found = re_find_all r_word_f "hello world foo" in
  assert_equal ~msg:"find_all words"
    "[hello; world; foo]" ("[" ^ String.concat "; " words_found ^ "]");

  let empty_found = re_find_all r_num "no numbers" in
  assert_true ~msg:"find_all empty" (empty_found = []);

  let single_found = re_find_all r_num "42" in
  assert_equal ~msg:"find_all single"
    "[42]" ("[" ^ String.concat "; " single_found ^ "]");

  (* --- Replace --- *)

  assert_equal ~msg:"replace numbers"
    "abc # def #" (re_replace r_num "abc 123 def 456" "#");

  let r_ws = re_compile "\\s+" in
  assert_equal ~msg:"replace whitespace"
    "hello world" (re_replace r_ws "hello   world" " ");

  assert_equal ~msg:"replace no match"
    "hello" (re_replace r_num "hello" "#");

  let r_vowel_r = re_compile "[aeiou]" in
  assert_equal ~msg:"replace vowels"
    "h_ll_ w_rld" (re_replace r_vowel_r "hello world" "_");

  (* --- Split --- *)

  let r_comma = re_compile "[,;]\\s*" in
  let parts = re_split r_comma "apple, banana; cherry,date" in
  assert_equal ~msg:"split csv"
    "[apple; banana; cherry; date]" ("[" ^ String.concat "; " parts ^ "]");

  let r_space_s = re_compile "\\s+" in
  let word_parts = re_split r_space_s "hello   world   foo" in
  assert_equal ~msg:"split spaces"
    "[hello; world; foo]" ("[" ^ String.concat "; " word_parts ^ "]");

  let no_split = re_split r_comma "noseparator" in
  assert_equal ~msg:"split no match"
    "[noseparator]" ("[" ^ String.concat "; " no_split ^ "]");

  (* --- Complex patterns --- *)

  (* Email-like pattern *)
  let r_email = re_compile "[a-zA-Z0-9]+@[a-zA-Z0-9]+\\.[a-z]+" in
  assert_true ~msg:"email match" (re_matches r_email "user@example.com");
  assert_true ~msg:"email no match" (not (re_matches r_email "not-an-email"));

  (* IP-like pattern *)
  let r_ip = re_compile "\\d+\\.\\d+\\.\\d+\\.\\d+" in
  assert_true ~msg:"ip match" (re_matches r_ip "192.168.1.1");
  assert_true ~msg:"ip no match" (not (re_matches r_ip "abc.def"));

  (* Nested quantifiers *)
  let r_nq = re_compile "(ab)*c" in
  assert_true ~msg:"nested quant c" (re_matches r_nq "c");
  assert_true ~msg:"nested quant abc" (re_matches r_nq "abc");
  assert_true ~msg:"nested quant ababc" (re_matches r_nq "ababc");

  (* --- Escape sequences --- *)

  let r_esc_dot = re_compile "a\\.b" in
  assert_true ~msg:"escaped dot literal" (re_matches r_esc_dot "a.b");
  assert_true ~msg:"escaped dot no wildcard" (not (re_matches r_esc_dot "axb"));

  let r_esc_star = re_compile "a\\*b" in
  assert_true ~msg:"escaped star literal" (re_matches r_esc_star "a*b");

  let r_esc_paren = re_compile "\\(a\\)" in
  assert_true ~msg:"escaped parens" (re_matches r_esc_paren "(a)");

  (* --- Edge cases --- *)

  (* Single character star *)
  let r_a_star = re_compile "a*" in
  assert_true ~msg:"a* empty" (re_matches r_a_star "");
  assert_true ~msg:"a* one" (re_matches r_a_star "a");
  assert_true ~msg:"a* many" (re_matches r_a_star "aaaa");
  assert_true ~msg:"a* no match b" (not (re_matches r_a_star "b"));

  (* Alternation with empty *)
  let r_alt_e = re_compile "a|" in
  assert_true ~msg:"alt empty second" (re_matches r_alt_e "a");
  assert_true ~msg:"alt empty matches empty" (re_matches r_alt_e "");

  (* Dot star *)
  let r_dotstar = re_compile ".*" in
  assert_true ~msg:"dotstar empty" (re_matches r_dotstar "");
  assert_true ~msg:"dotstar anything" (re_matches r_dotstar "hello world 123!");

  (* Character class with literal hyphen at end *)
  let r_hyphen = re_compile "[a-]" in
  assert_true ~msg:"class literal hyphen a" (re_matches r_hyphen "a");
  (* hyphen at the boundary between first char and ']' is treated as literal *)

  (* Multiple character class items *)
  let r_mc = re_compile "[abc123]" in
  assert_true ~msg:"multi class a" (re_matches r_mc "a");
  assert_true ~msg:"multi class 1" (re_matches r_mc "1");
  assert_true ~msg:"multi class no d" (not (re_matches r_mc "d"));
)

(* ===== Stream functions (from stream.ml) ===== *)

type 'a stream =
  | SNil
  | SCons of 'a * 'a stream Lazy.t

let stream_empty = SNil

let stream_singleton x = SCons (x, lazy SNil)

let stream_cons x s = SCons (x, lazy s)

let stream_is_empty = function SNil -> true | SCons _ -> false

let stream_hd = function
  | SNil -> failwith "Stream.hd: empty stream"
  | SCons (x, _) -> x

let stream_tl = function
  | SNil -> failwith "Stream.tl: empty stream"
  | SCons (_, rest) -> Lazy.force rest

let stream_hd_opt = function
  | SNil -> None
  | SCons (x, _) -> Some x

let rec stream_unfold f seed =
  match f seed with
  | None -> SNil
  | Some (value, next_seed) ->
    SCons (value, lazy (stream_unfold f next_seed))

let rec stream_iterate f x =
  SCons (x, lazy (stream_iterate f (f x)))

let rec stream_repeat x =
  SCons (x, lazy (stream_repeat x))

let stream_cycle lst =
  if lst = [] then invalid_arg "Stream.cycle: empty list";
  let rec go = function
    | [] -> go lst
    | x :: rest -> SCons (x, lazy (go rest))
  in
  go lst

let rec stream_of_list = function
  | [] -> SNil
  | x :: rest -> SCons (x, lazy (stream_of_list rest))

let rec stream_from ?(step=1) start =
  SCons (start, lazy (stream_from ~step (start + step)))

let stream_range ?(step=1) lo hi =
  stream_unfold (fun n -> if n > hi then None else Some (n, n + step)) lo

let stream_take n s =
  let rec aux n s acc =
    if n <= 0 then List.rev acc
    else match s with
      | SNil -> List.rev acc
      | SCons (x, rest) -> aux (n - 1) (Lazy.force rest) (x :: acc)
  in
  aux n s []

let stream_take_while pred s =
  let rec aux s acc =
    match s with
    | SNil -> List.rev acc
    | SCons (x, rest) ->
      if pred x then aux (Lazy.force rest) (x :: acc)
      else List.rev acc
  in
  aux s []

let rec stream_drop n s =
  if n <= 0 then s
  else match s with
    | SNil -> SNil
    | SCons (_, rest) -> stream_drop (n - 1) (Lazy.force rest)

let rec stream_drop_while pred = function
  | SNil -> SNil
  | SCons (x, rest) as s ->
    if pred x then stream_drop_while pred (Lazy.force rest)
    else s

let stream_nth n s =
  if n < 0 then invalid_arg "Stream.nth: negative index";
  stream_hd (stream_drop n s)

let stream_nth_opt n s =
  if n < 0 then None
  else stream_hd_opt (stream_drop n s)

let stream_to_list s =
  let rec aux s acc =
    match s with
    | SNil -> List.rev acc
    | SCons (x, rest) -> aux (Lazy.force rest) (x :: acc)
  in
  aux s []

let stream_length s =
  let rec aux s n =
    match s with
    | SNil -> n
    | SCons (_, rest) -> aux (Lazy.force rest) (n + 1)
  in
  aux s 0

let rec stream_map f = function
  | SNil -> SNil
  | SCons (x, rest) ->
    SCons (f x, lazy (stream_map f (Lazy.force rest)))

let stream_mapi f s =
  let rec aux i = function
    | SNil -> SNil
    | SCons (x, rest) ->
      SCons (f i x, lazy (aux (i + 1) (Lazy.force rest)))
  in
  aux 0 s

let rec stream_filter pred = function
  | SNil -> SNil
  | SCons (x, rest) ->
    if pred x then SCons (x, lazy (stream_filter pred (Lazy.force rest)))
    else stream_filter pred (Lazy.force rest)

let rec stream_filter_map f = function
  | SNil -> SNil
  | SCons (x, rest) ->
    match f x with
    | Some y -> SCons (y, lazy (stream_filter_map f (Lazy.force rest)))
    | None -> stream_filter_map f (Lazy.force rest)

let stream_flat_map f s =
  let rec aux pending s =
    match pending with
    | x :: rest -> SCons (x, lazy (aux rest s))
    | [] ->
      match s with
      | SNil -> SNil
      | SCons (x, rest) -> aux (f x) (Lazy.force rest)
  in
  aux [] s

let rec stream_scan f init = function
  | SNil -> stream_singleton init
  | SCons (x, rest) ->
    let acc = f init x in
    SCons (init, lazy (stream_scan f acc (Lazy.force rest)))

let rec stream_append s1 s2 =
  match s1 with
  | SNil -> s2
  | SCons (x, rest) -> SCons (x, lazy (stream_append (Lazy.force rest) s2))

let rec stream_interleave s1 s2 =
  match s1 with
  | SNil -> s2
  | SCons (x, rest) -> SCons (x, lazy (stream_interleave s2 (Lazy.force rest)))

let rec stream_zip s1 s2 =
  match s1, s2 with
  | SCons (a, r1), SCons (b, r2) ->
    SCons ((a, b), lazy (stream_zip (Lazy.force r1) (Lazy.force r2)))
  | _ -> SNil

let rec stream_zip_with f s1 s2 =
  match s1, s2 with
  | SCons (a, r1), SCons (b, r2) ->
    SCons (f a b, lazy (stream_zip_with f (Lazy.force r1) (Lazy.force r2)))
  | _ -> SNil

let stream_unzip s =
  (stream_map fst s, stream_map snd s)

let rec stream_find pred = function
  | SNil -> None
  | SCons (x, rest) ->
    if pred x then Some x
    else stream_find pred (Lazy.force rest)

let stream_exists pred s =
  stream_find pred s <> None

let stream_fold f init s =
  let rec aux acc = function
    | SNil -> acc
    | SCons (x, rest) -> aux (f acc x) (Lazy.force rest)
  in
  aux init s

let stream_iter f s =
  let rec aux = function
    | SNil -> ()
    | SCons (x, rest) -> f x; aux (Lazy.force rest)
  in
  aux s

(* Classic streams *)
let stream_nats = stream_from 0
let stream_naturals = stream_from 1

let stream_fibs =
  let rec aux a b = SCons (a, lazy (aux b (a + b))) in
  aux 0 1

let stream_powers_of_2 = stream_iterate (fun x -> x * 2) 1

let stream_factorials =
  let rec aux n fact = SCons (fact, lazy (aux (n + 1) (fact * (n + 1)))) in
  aux 0 1

let stream_triangulars =
  stream_mapi (fun i _ -> i * (i + 1) / 2) stream_nats

let stream_primes =
  let rec sieve = function
    | SNil -> SNil
    | SCons (p, rest) ->
      SCons (p, lazy (sieve (stream_filter (fun n -> n mod p <> 0) (Lazy.force rest))))
  in
  sieve (stream_from 2)

let stream_show_ints ?(n=10) s =
  let elems = stream_take n s in
  let parts = List.map string_of_int elems in
  let suffix = match stream_drop n s with SNil -> "" | SCons _ -> "; ..." in
  "[" ^ String.concat "; " parts ^ suffix ^ "]"

(* ===== Stream Tests ===== *)

let string_of_int_pair (a, b) =
  "(" ^ string_of_int a ^ ", " ^ string_of_int b ^ ")"

let string_of_int_pair_list lst =
  "[" ^ String.concat "; " (List.map string_of_int_pair lst) ^ "]"

let test_stream () = suite "Stream" (fun () ->
  (* ── Constructors ── *)

  assert_true ~msg:"empty is_empty" (stream_is_empty stream_empty);

  let s1 = stream_singleton 42 in
  assert_equal ~msg:"singleton hd" "42" (string_of_int (stream_hd s1));
  assert_true ~msg:"singleton tl empty" (stream_is_empty (stream_tl s1));

  let s2 = stream_cons 1 (stream_cons 2 stream_empty) in
  assert_equal ~msg:"cons take 2" "[1; 2]" (string_of_int_list (stream_take 2 s2));

  let s3 = stream_of_list [10; 20; 30] in
  assert_equal ~msg:"of_list" "[10; 20; 30]" (string_of_int_list (stream_to_list s3));

  let r = stream_range 1 5 in
  assert_equal ~msg:"range 1..5" "[1; 2; 3; 4; 5]" (string_of_int_list (stream_to_list r));
  let r2 = stream_range ~step:2 0 8 in
  assert_equal ~msg:"range step 2" "[0; 2; 4; 6; 8]" (string_of_int_list (stream_to_list r2));

  let ints = stream_from 10 in
  assert_equal ~msg:"from 10" "[10; 11; 12; 13; 14]" (string_of_int_list (stream_take 5 ints));
  let evens = stream_from ~step:2 0 in
  assert_equal ~msg:"from step 2" "[0; 2; 4; 6; 8]" (string_of_int_list (stream_take 5 evens));

  let doubles = stream_iterate (fun x -> x * 2) 1 in
  assert_equal ~msg:"iterate *2" "[1; 2; 4; 8; 16]" (string_of_int_list (stream_take 5 doubles));

  let threes = stream_repeat 3 in
  assert_equal ~msg:"repeat 3" "[3; 3; 3; 3]" (string_of_int_list (stream_take 4 threes));

  let countdown = stream_unfold (fun n -> if n < 0 then None else Some (n, n - 1)) 5 in
  assert_equal ~msg:"unfold countdown" "[5; 4; 3; 2; 1; 0]" (string_of_int_list (stream_to_list countdown));

  let cyc = stream_cycle [1; 2; 3] in
  assert_equal ~msg:"cycle [1;2;3]" "[1; 2; 3; 1; 2; 3; 1]" (string_of_int_list (stream_take 7 cyc));

  (* ── Observation ── *)

  let s = stream_of_list [5; 10; 15] in
  assert_equal ~msg:"hd" "5" (string_of_int (stream_hd s));
  assert_equal ~msg:"tl hd" "10" (string_of_int (stream_hd (stream_tl s)));

  assert_equal ~msg:"hd_opt some" "Some(5)" (string_of_option string_of_int (stream_hd_opt s));
  assert_equal ~msg:"hd_opt none" "None" (string_of_option string_of_int (stream_hd_opt stream_empty));

  assert_raises ~msg:"hd empty raises" (fun () -> stream_hd stream_empty);

  let nats5 = stream_from 0 in
  assert_equal ~msg:"nth 0" "0" (string_of_int (stream_nth 0 nats5));
  assert_equal ~msg:"nth 4" "4" (string_of_int (stream_nth 4 nats5));

  let short = stream_of_list [100; 200] in
  assert_equal ~msg:"nth_opt 0" "Some(100)" (string_of_option string_of_int (stream_nth_opt 0 short));
  assert_equal ~msg:"nth_opt 5" "None" (string_of_option string_of_int (stream_nth_opt 5 short));
  assert_equal ~msg:"nth_opt neg" "None" (string_of_option string_of_int (stream_nth_opt (-1) short));

  assert_equal ~msg:"take 0" "[]" (string_of_int_list (stream_take 0 (stream_from 0)));
  assert_equal ~msg:"take from empty" "[]" (string_of_int_list (stream_take 5 stream_empty));

  let tw = stream_take_while (fun x -> x < 5) (stream_from 0) in
  assert_equal ~msg:"take_while <5" "[0; 1; 2; 3; 4]" (string_of_int_list tw);
  let tw2 = stream_take_while (fun _ -> false) (stream_from 0) in
  assert_equal ~msg:"take_while false" "[]" (string_of_int_list tw2);

  let dropped = stream_drop 3 (stream_of_list [1;2;3;4;5]) in
  assert_equal ~msg:"drop 3" "[4; 5]" (string_of_int_list (stream_to_list dropped));
  assert_true ~msg:"drop past end" (stream_is_empty (stream_drop 10 (stream_of_list [1])));

  let dw = stream_drop_while (fun x -> x < 3) (stream_of_list [1;2;3;4;5]) in
  assert_equal ~msg:"drop_while <3" "[3; 4; 5]" (string_of_int_list (stream_to_list dw));

  assert_equal ~msg:"length 0" "0" (string_of_int (stream_length stream_empty));
  assert_equal ~msg:"length 3" "3" (string_of_int (stream_length (stream_of_list [1;2;3])));

  (* ── Transformations ── *)

  let mapped = stream_map (fun x -> x * 10) (stream_of_list [1;2;3]) in
  assert_equal ~msg:"map *10" "[10; 20; 30]" (string_of_int_list (stream_to_list mapped));

  let sq = stream_map (fun x -> x * x) (stream_from 1) in
  assert_equal ~msg:"map squares" "[1; 4; 9; 16; 25]" (string_of_int_list (stream_take 5 sq));

  let mi = stream_mapi (fun i x -> i + x) (stream_of_list [10;20;30]) in
  assert_equal ~msg:"mapi" "[10; 21; 32]" (string_of_int_list (stream_to_list mi));

  let evens_f = stream_filter (fun x -> x mod 2 = 0) (stream_from 0) in
  assert_equal ~msg:"filter evens" "[0; 2; 4; 6; 8]" (string_of_int_list (stream_take 5 evens_f));

  let odds = stream_filter (fun x -> x mod 2 = 1) (stream_of_list [1;2;3;4;5]) in
  assert_equal ~msg:"filter odds" "[1; 3; 5]" (string_of_int_list (stream_to_list odds));

  let fm = stream_filter_map
    (fun x -> if x mod 2 = 0 then Some (x / 2) else None)
    (stream_of_list [1;2;3;4;5;6]) in
  assert_equal ~msg:"filter_map" "[1; 2; 3]" (string_of_int_list (stream_to_list fm));

  let flatm = stream_flat_map (fun x -> [x; x * 10]) (stream_of_list [1;2;3]) in
  assert_equal ~msg:"flat_map" "[1; 10; 2; 20; 3; 30]" (string_of_int_list (stream_to_list flatm));

  let running_sum = stream_scan ( + ) 0 (stream_of_list [1;2;3;4]) in
  assert_equal ~msg:"scan sum" "[0; 1; 3; 6; 10]" (string_of_int_list (stream_to_list running_sum));

  (* ── Combining ── *)

  let a = stream_of_list [1;2] in
  let b = stream_of_list [3;4] in
  assert_equal ~msg:"append" "[1; 2; 3; 4]" (string_of_int_list (stream_to_list (stream_append a b)));

  let i1 = stream_of_list [1;3;5] in
  let i2 = stream_of_list [2;4;6] in
  assert_equal ~msg:"interleave" "[1; 2; 3; 4; 5; 6]" (string_of_int_list (stream_to_list (stream_interleave i1 i2)));

  let odds_i = stream_from ~step:2 1 in
  let evens_i = stream_from ~step:2 0 in
  let mixed = stream_interleave odds_i evens_i in
  assert_equal ~msg:"interleave inf" "[1; 0; 3; 2; 5; 4; 7; 6]" (string_of_int_list (stream_take 8 mixed));

  let z = stream_zip (stream_of_list [1;2;3]) (stream_of_list [10;20;30]) in
  assert_equal ~msg:"zip" "[(1, 10); (2, 20); (3, 30)]"
    (string_of_int_pair_list (stream_to_list z));

  let zw = stream_zip_with ( + ) (stream_of_list [1;2;3]) (stream_of_list [10;20;30]) in
  assert_equal ~msg:"zip_with +" "[11; 22; 33]" (string_of_int_list (stream_to_list zw));

  let z2 = stream_zip (stream_of_list [1;2]) (stream_of_list [10;20;30]) in
  assert_equal ~msg:"zip short" "[(1, 10); (2, 20)]"
    (string_of_int_pair_list (stream_to_list z2));

  let pairs = stream_of_list [(1,10); (2,20); (3,30)] in
  let (left, right) = stream_unzip pairs in
  assert_equal ~msg:"unzip left" "[1; 2; 3]" (string_of_int_list (stream_to_list left));
  assert_equal ~msg:"unzip right" "[10; 20; 30]" (string_of_int_list (stream_to_list right));

  (* ── Searching ── *)

  let found = stream_find (fun x -> x > 10) (stream_from 0) in
  assert_equal ~msg:"find >10" "Some(11)" (string_of_option string_of_int found);

  let not_found = stream_find (fun x -> x > 5) (stream_of_list [1;2;3]) in
  assert_equal ~msg:"find none" "None" (string_of_option string_of_int not_found);

  assert_true ~msg:"exists true" (stream_exists (fun x -> x = 3) (stream_of_list [1;2;3;4]));
  assert_true ~msg:"exists false" (not (stream_exists (fun x -> x > 10) (stream_of_list [1;2;3])));

  let sum = stream_fold ( + ) 0 (stream_of_list [1;2;3;4;5]) in
  assert_equal ~msg:"fold sum" "15" (string_of_int sum);

  let acc = ref 0 in
  stream_iter (fun x -> acc := !acc + x) (stream_of_list [1;2;3]);
  assert_equal ~msg:"iter sum" "6" (string_of_int !acc);

  (* ── Classic Streams ── *)

  assert_equal ~msg:"nats" "[0; 1; 2; 3; 4]" (string_of_int_list (stream_take 5 stream_nats));
  assert_equal ~msg:"naturals" "[1; 2; 3; 4; 5]" (string_of_int_list (stream_take 5 stream_naturals));
  assert_equal ~msg:"fibs" "[0; 1; 1; 2; 3; 5; 8; 13]" (string_of_int_list (stream_take 8 stream_fibs));
  assert_equal ~msg:"powers_of_2" "[1; 2; 4; 8; 16; 32]" (string_of_int_list (stream_take 6 stream_powers_of_2));
  assert_equal ~msg:"factorials" "[1; 1; 2; 6; 24; 120; 720]" (string_of_int_list (stream_take 7 stream_factorials));
  assert_equal ~msg:"primes" "[2; 3; 5; 7; 11; 13; 17; 19; 23; 29]"
    (string_of_int_list (stream_take 10 stream_primes));
  assert_equal ~msg:"triangulars" "[0; 1; 3; 6; 10; 15]"
    (string_of_int_list (stream_take 6 stream_triangulars));

  (* ── Pretty Printing ── *)

  let shown = stream_show_ints ~n:5 (stream_from 0) in
  assert_equal ~msg:"show_ints" "[0; 1; 2; 3; 4; ...]" shown;

  let shown_finite = stream_show_ints ~n:10 (stream_of_list [1;2;3]) in
  assert_equal ~msg:"show_ints finite" "[1; 2; 3]" shown_finite;

  (* ── Edge Cases ── *)

  assert_true ~msg:"map empty" (stream_is_empty (stream_map (fun x -> x + 1) stream_empty));
  assert_true ~msg:"filter empty" (stream_is_empty (stream_filter (fun _ -> true) stream_empty));

  let ae = stream_append stream_empty (stream_of_list [1;2]) in
  assert_equal ~msg:"append empty left" "[1; 2]" (string_of_int_list (stream_to_list ae));
  let ea = stream_append (stream_of_list [1;2]) stream_empty in
  assert_equal ~msg:"append empty right" "[1; 2]" (string_of_int_list (stream_to_list ea));

  assert_true ~msg:"zip empty" (stream_is_empty (stream_zip stream_empty (stream_from 0)));

  assert_raises ~msg:"cycle empty raises" (fun () -> stream_cycle []);

  let d0 = stream_drop 0 (stream_of_list [1;2;3]) in
  assert_equal ~msg:"drop 0" "[1; 2; 3]" (string_of_int_list (stream_to_list d0));

  (* Memoization: accessing tail twice doesn't recompute *)
  let counter = ref 0 in
  let memo_stream = SCons (1, lazy (incr counter; stream_singleton 2)) in
  ignore (stream_tl memo_stream);
  ignore (stream_tl memo_stream);
  assert_equal ~msg:"lazy memoization" "1" (string_of_int !counter);

  let se = stream_scan ( + ) 0 stream_empty in
  assert_equal ~msg:"scan empty" "[0]" (string_of_int_list (stream_to_list se));

  assert_true ~msg:"flat_map empty" (stream_is_empty (stream_flat_map (fun x -> [x]) stream_empty));

  (* Composition: map then filter *)
  let composed = stream_filter (fun x -> x mod 3 = 0)
    (stream_map (fun x -> x * x) (stream_from 1)) in
  assert_equal ~msg:"compose map+filter" "[9; 36; 81; 144; 225]"
    (string_of_int_list (stream_take 5 composed));
)

(* ===== Red-Black Tree functions (from rbtree.ml) ===== *)

type rb_color = RBRed | RBBlack

type 'a rbtree =
  | RBE
  | RBT of rb_color * 'a rbtree * 'a * 'a rbtree

let rb_empty = RBE

let rb_is_empty = function RBE -> true | _ -> false

let rec rb_member x = function
  | RBE -> false
  | RBT (_, left, v, right) ->
    if x < v then rb_member x left
    else if x > v then rb_member x right
    else true

let rb_balance = function
  | RBBlack, RBT (RBRed, RBT (RBRed, a, x, b), y, c), z, d
  | RBBlack, RBT (RBRed, a, x, RBT (RBRed, b, y, c)), z, d
  | RBBlack, a, x, RBT (RBRed, RBT (RBRed, b, y, c), z, d)
  | RBBlack, a, x, RBT (RBRed, b, y, RBT (RBRed, c, z, d)) ->
    RBT (RBRed, RBT (RBBlack, a, x, b), y, RBT (RBBlack, c, z, d))
  | color, left, v, right ->
    RBT (color, left, v, right)

let rb_insert x tree =
  let rec ins = function
    | RBE -> RBT (RBRed, RBE, x, RBE)
    | RBT (color, left, v, right) ->
      if x < v then rb_balance (color, ins left, v, right)
      else if x > v then rb_balance (color, left, v, ins right)
      else RBT (color, left, v, right)
  in
  match ins tree with
  | RBT (_, left, v, right) -> RBT (RBBlack, left, v, right)
  | RBE -> failwith "impossible"

let rb_balance_del = function
  | RBBlack, RBT (RBRed, RBT (RBRed, a, x, b), y, c), z, d ->
    RBT (RBRed, RBT (RBBlack, a, x, b), y, RBT (RBBlack, c, z, d))
  | RBBlack, RBT (RBRed, a, x, RBT (RBRed, b, y, c)), z, d ->
    RBT (RBRed, RBT (RBBlack, a, x, b), y, RBT (RBBlack, c, z, d))
  | RBBlack, a, x, RBT (RBRed, RBT (RBRed, b, y, c), z, d) ->
    RBT (RBRed, RBT (RBBlack, a, x, b), y, RBT (RBBlack, c, z, d))
  | RBBlack, a, x, RBT (RBRed, b, y, RBT (RBRed, c, z, d)) ->
    RBT (RBRed, RBT (RBBlack, a, x, b), y, RBT (RBBlack, c, z, d))
  | color, left, v, right ->
    RBT (color, left, v, right)

let rb_bubble_left = function
  | RBT (RBBlack, RBT (RBRed, a, x, b), y, right) ->
    rb_balance_del (RBBlack, RBT (RBRed, a, x, b), y, right)
  | RBT (color, left, y, RBT (RBBlack, a, z, b)) ->
    rb_balance_del (color, left, y, RBT (RBRed, a, z, b))
  | RBT (color, left, y, RBT (RBRed, RBT (RBBlack, a, z, b), w, c)) ->
    RBT (color, RBT (RBBlack, left, y, RBT (RBRed, a, z, b)), w, c)
  | t -> t

let rb_bubble_right = function
  | RBT (color, RBT (RBBlack, a, x, b), y, right) ->
    rb_balance_del (color, RBT (RBRed, a, x, b), y, right)
  | RBT (RBBlack, RBT (RBRed, a, x, RBT (RBBlack, b, y, c)), z, right) ->
    RBT (RBBlack, a, x, RBT (RBBlack, RBT (RBRed, b, y, c), z, right))
  | t -> t

let rec rb_min_elt = function
  | RBE -> failwith "rb_min_elt: empty"
  | RBT (_, RBE, v, _) -> v
  | RBT (_, left, _, _) -> rb_min_elt left

let rec rb_max_elt = function
  | RBE -> failwith "rb_max_elt: empty"
  | RBT (_, _, v, RBE) -> v
  | RBT (_, _, _, right) -> rb_max_elt right

let rb_min_elt_opt = function RBE -> None | t -> Some (rb_min_elt t)
let rb_max_elt_opt = function RBE -> None | t -> Some (rb_max_elt t)

let rec rb_remove_min = function
  | RBE -> failwith "rb_remove_min: empty"
  | RBT (_, RBE, _, right) -> right
  | RBT (color, left, v, right) ->
    rb_bubble_left (RBT (color, rb_remove_min left, v, right))

let rb_delete x tree =
  let rec del = function
    | RBE -> RBE
    | RBT (color, left, v, right) ->
      if x < v then
        rb_bubble_left (RBT (color, del left, v, right))
      else if x > v then
        rb_bubble_right (RBT (color, left, v, del right))
      else
        match left, right with
        | RBE, _ -> right
        | _, RBE -> left
        | _ ->
          let s = rb_min_elt right in
          rb_bubble_right (RBT (color, left, s, rb_remove_min right))
  in
  match del tree with
  | RBT (_, left, v, right) -> RBT (RBBlack, left, v, right)
  | RBE -> RBE

let rec rb_cardinal = function
  | RBE -> 0
  | RBT (_, left, _, right) -> 1 + rb_cardinal left + rb_cardinal right

let rec rb_height = function
  | RBE -> 0
  | RBT (_, left, _, right) -> 1 + max (rb_height left) (rb_height right)

let rec rb_black_height = function
  | RBE -> 0
  | RBT (RBBlack, left, _, _) -> 1 + rb_black_height left
  | RBT (RBRed, left, _, _) -> rb_black_height left

let rb_to_list tree =
  let rec aux acc = function
    | RBE -> acc
    | RBT (_, left, v, right) -> aux (v :: aux acc right) left
  in
  aux [] tree

let rec rb_fold f acc = function
  | RBE -> acc
  | RBT (_, left, v, right) ->
    let acc' = rb_fold f acc left in
    let acc'' = f acc' v in
    rb_fold f acc'' right

let rec rb_iter f = function
  | RBE -> ()
  | RBT (_, left, v, right) ->
    rb_iter f left; f v; rb_iter f right

let rec rb_for_all p = function
  | RBE -> true
  | RBT (_, left, v, right) ->
    p v && rb_for_all p left && rb_for_all p right

let rec rb_exists p = function
  | RBE -> false
  | RBT (_, left, v, right) ->
    p v || rb_exists p left || rb_exists p right

let rb_of_list lst =
  List.fold_left (fun acc x -> rb_insert x acc) RBE lst

let rb_singleton x = rb_insert x RBE

let rb_union t1 t2 =
  rb_fold (fun acc x -> rb_insert x acc) t1 t2

let rb_inter t1 t2 =
  rb_fold (fun acc x -> if rb_member x t2 then rb_insert x acc else acc) RBE t1

let rb_diff t1 t2 =
  rb_fold (fun acc x -> if not (rb_member x t2) then rb_insert x acc else acc) RBE t1

let rb_subset t1 t2 =
  rb_for_all (fun x -> rb_member x t2) t1

let rb_equal t1 t2 =
  rb_to_list t1 = rb_to_list t2

let rb_filter p tree =
  rb_fold (fun acc x -> if p x then rb_insert x acc else acc) RBE tree

let rb_partition p tree =
  rb_fold (fun (yes, no) x ->
    if p x then (rb_insert x yes, no) else (yes, rb_insert x no))
    (RBE, RBE) tree

let rb_map f tree =
  rb_fold (fun acc x -> rb_insert (f x) acc) RBE tree

let rec rb_no_red_red = function
  | RBE -> true
  | RBT (RBRed, RBT (RBRed, _, _, _), _, _)
  | RBT (RBRed, _, _, RBT (RBRed, _, _, _)) -> false
  | RBT (_, left, _, right) ->
    rb_no_red_red left && rb_no_red_red right

let rec rb_valid_black_height = function
  | RBE -> Some 0
  | RBT (color, left, _, right) ->
    match rb_valid_black_height left, rb_valid_black_height right with
    | Some lh, Some rh when lh = rh ->
      Some (if color = RBBlack then lh + 1 else lh)
    | _ -> None

let rec rb_is_bst_aux lo hi = function
  | RBE -> true
  | RBT (_, left, v, right) ->
    (match lo with None -> true | Some l -> v > l) &&
    (match hi with None -> true | Some h -> v < h) &&
    rb_is_bst_aux lo (Some v) left &&
    rb_is_bst_aux (Some v) hi right

let rb_is_valid tree =
  let root_black = match tree with RBE -> true | RBT (RBBlack, _, _, _) -> true | _ -> false in
  root_black &&
  rb_no_red_red tree &&
  (rb_valid_black_height tree <> None) &&
  rb_is_bst_aux None None tree

(* ===== Red-Black Tree tests ===== *)

let test_rbtree () = suite "Red-Black Tree" (fun () ->
  (* -- Empty tree -- *)
  assert_true ~msg:"empty is_empty" (rb_is_empty RBE);
  assert_true ~msg:"empty is_valid" (rb_is_valid RBE);
  assert_equal ~msg:"empty cardinal" "0" (string_of_int (rb_cardinal RBE));
  assert_equal ~msg:"empty to_list" "[]" (string_of_int_list (rb_to_list RBE));
  assert_true ~msg:"empty not member" (not (rb_member 1 RBE));

  (* -- Singleton -- *)
  let s = rb_singleton 42 in
  assert_true ~msg:"singleton is_valid" (rb_is_valid s);
  assert_equal ~msg:"singleton cardinal" "1" (string_of_int (rb_cardinal s));
  assert_true ~msg:"singleton member" (rb_member 42 s);
  assert_true ~msg:"singleton not member 0" (not (rb_member 0 s));
  assert_equal ~msg:"singleton to_list" "[42]" (string_of_int_list (rb_to_list s));

  (* -- Insert maintains sorted order -- *)
  let t = rb_of_list [5; 3; 7; 1; 4; 6; 8] in
  assert_equal ~msg:"of_list sorted" "[1; 3; 4; 5; 6; 7; 8]" (string_of_int_list (rb_to_list t));
  assert_true ~msg:"of_list is_valid" (rb_is_valid t);
  assert_equal ~msg:"of_list cardinal" "7" (string_of_int (rb_cardinal t));

  (* -- Duplicate insert -- *)
  let t_dup = rb_insert 5 t in
  assert_equal ~msg:"duplicate insert no change" "7" (string_of_int (rb_cardinal t_dup));
  assert_equal ~msg:"duplicate sorted" "[1; 3; 4; 5; 6; 7; 8]" (string_of_int_list (rb_to_list t_dup));

  (* -- Member -- *)
  assert_true ~msg:"member 1" (rb_member 1 t);
  assert_true ~msg:"member 5" (rb_member 5 t);
  assert_true ~msg:"member 8" (rb_member 8 t);
  assert_true ~msg:"not member 0" (not (rb_member 0 t));
  assert_true ~msg:"not member 9" (not (rb_member 9 t));
  assert_true ~msg:"not member 2" (not (rb_member 2 t));

  (* -- Min / Max -- *)
  assert_equal ~msg:"min_elt" "1" (string_of_int (rb_min_elt t));
  assert_equal ~msg:"max_elt" "8" (string_of_int (rb_max_elt t));
  assert_equal ~msg:"min_elt_opt" "Some(1)" (string_of_option string_of_int (rb_min_elt_opt t));
  assert_equal ~msg:"max_elt_opt" "Some(8)" (string_of_option string_of_int (rb_max_elt_opt t));
  assert_equal ~msg:"min_elt_opt empty" "None" (string_of_option string_of_int (rb_min_elt_opt RBE));
  assert_equal ~msg:"max_elt_opt empty" "None" (string_of_option string_of_int (rb_max_elt_opt RBE));
  assert_raises ~msg:"min_elt empty raises" (fun () -> rb_min_elt RBE);
  assert_raises ~msg:"max_elt empty raises" (fun () -> rb_max_elt RBE);

  (* -- Delete leaf element -- *)
  let t_del1 = rb_delete 1 t in
  assert_equal ~msg:"delete 1" "[3; 4; 5; 6; 7; 8]" (string_of_int_list (rb_to_list t_del1));
  assert_true ~msg:"delete 1 valid" (rb_is_valid t_del1);
  assert_true ~msg:"1 removed" (not (rb_member 1 t_del1));

  (* -- Delete root element -- *)
  let t_del5 = rb_delete 5 t in
  assert_equal ~msg:"delete 5" "[1; 3; 4; 6; 7; 8]" (string_of_int_list (rb_to_list t_del5));
  assert_true ~msg:"delete 5 valid" (rb_is_valid t_del5);

  (* -- Delete max -- *)
  let t_del8 = rb_delete 8 t in
  assert_equal ~msg:"delete 8" "[1; 3; 4; 5; 6; 7]" (string_of_int_list (rb_to_list t_del8));
  assert_true ~msg:"delete 8 valid" (rb_is_valid t_del8);

  (* -- Delete non-existent -- *)
  let t_del99 = rb_delete 99 t in
  assert_equal ~msg:"delete non-existent" "7" (string_of_int (rb_cardinal t_del99));
  assert_true ~msg:"delete non-existent valid" (rb_is_valid t_del99);

  (* -- Delete all elements -- *)
  let t_empty = List.fold_left (fun acc x -> rb_delete x acc) t [1; 3; 4; 5; 6; 7; 8] in
  assert_true ~msg:"delete all is_empty" (rb_is_empty t_empty);
  assert_true ~msg:"delete all valid" (rb_is_valid t_empty);

  (* -- Delete from empty -- *)
  assert_true ~msg:"delete from empty" (rb_is_empty (rb_delete 1 RBE));

  (* -- Height and black-height -- *)
  let large = rb_of_list [1; 2; 3; 4; 5; 6; 7; 8; 9; 10; 11; 12; 13; 14; 15] in
  assert_true ~msg:"large is_valid" (rb_is_valid large);
  let h = rb_height large in
  let n = rb_cardinal large in
  (* RB-tree height <= 2*log2(n+1) *)
  let max_h = 2.0 *. (log (float_of_int (n + 1)) /. log 2.0) in
  assert_true ~msg:"height bounded" (float_of_int h <= max_h +. 0.001);
  assert_true ~msg:"black_height positive" (rb_black_height large > 0);

  (* -- Fold (sum) -- *)
  let sum = rb_fold (fun acc x -> acc + x) 0 t in
  assert_equal ~msg:"fold sum" "34" (string_of_int sum);

  (* -- Fold (count) -- *)
  let count = rb_fold (fun acc _ -> acc + 1) 0 t in
  assert_equal ~msg:"fold count" "7" (string_of_int count);

  (* -- for_all / exists -- *)
  assert_true ~msg:"for_all positive" (rb_for_all (fun x -> x > 0) t);
  assert_true ~msg:"not for_all >3" (not (rb_for_all (fun x -> x > 3) t));
  assert_true ~msg:"exists 7" (rb_exists (fun x -> x = 7) t);
  assert_true ~msg:"not exists 99" (not (rb_exists (fun x -> x = 99) t));

  (* -- Filter -- *)
  let evens = rb_filter (fun x -> x mod 2 = 0) t in
  assert_equal ~msg:"filter evens" "[4; 6; 8]" (string_of_int_list (rb_to_list evens));
  assert_true ~msg:"filter valid" (rb_is_valid evens);

  (* -- Partition -- *)
  let (below5, above5) = rb_partition (fun x -> x < 5) t in
  assert_equal ~msg:"partition below" "[1; 3; 4]" (string_of_int_list (rb_to_list below5));
  assert_equal ~msg:"partition above" "[5; 6; 7; 8]" (string_of_int_list (rb_to_list above5));
  assert_true ~msg:"partition below valid" (rb_is_valid below5);
  assert_true ~msg:"partition above valid" (rb_is_valid above5);

  (* -- Map -- *)
  let doubled = rb_map (fun x -> x * 2) (rb_of_list [1; 2; 3]) in
  assert_equal ~msg:"map double" "[2; 4; 6]" (string_of_int_list (rb_to_list doubled));
  assert_true ~msg:"map valid" (rb_is_valid doubled);

  (* -- Union -- *)
  let a = rb_of_list [1; 3; 5; 7] in
  let b = rb_of_list [2; 4; 6; 8] in
  let u = rb_union a b in
  assert_equal ~msg:"union disjoint" "[1; 2; 3; 4; 5; 6; 7; 8]" (string_of_int_list (rb_to_list u));
  assert_true ~msg:"union valid" (rb_is_valid u);

  let c = rb_of_list [3; 5; 9] in
  let u2 = rb_union a c in
  assert_equal ~msg:"union overlap" "[1; 3; 5; 7; 9]" (string_of_int_list (rb_to_list u2));
  assert_true ~msg:"union overlap valid" (rb_is_valid u2);

  (* -- Intersection -- *)
  let i = rb_inter (rb_of_list [1; 2; 3; 4; 5]) (rb_of_list [3; 4; 5; 6; 7]) in
  assert_equal ~msg:"inter" "[3; 4; 5]" (string_of_int_list (rb_to_list i));
  assert_true ~msg:"inter valid" (rb_is_valid i);

  let i_empty = rb_inter a b in
  assert_true ~msg:"inter disjoint empty" (rb_is_empty i_empty);

  (* -- Difference -- *)
  let d = rb_diff (rb_of_list [1; 2; 3; 4; 5]) (rb_of_list [3; 4; 5; 6; 7]) in
  assert_equal ~msg:"diff" "[1; 2]" (string_of_int_list (rb_to_list d));
  assert_true ~msg:"diff valid" (rb_is_valid d);

  (* -- Subset -- *)
  assert_true ~msg:"subset yes" (rb_subset (rb_of_list [3; 5]) a);
  assert_true ~msg:"subset no" (not (rb_subset (rb_of_list [3; 5; 9]) a));
  assert_true ~msg:"subset empty" (rb_subset RBE a);
  assert_true ~msg:"subset self" (rb_subset a a);

  (* -- Equal -- *)
  assert_true ~msg:"equal same" (rb_equal (rb_of_list [3; 1; 2]) (rb_of_list [1; 2; 3]));
  assert_true ~msg:"not equal" (not (rb_equal a b));
  assert_true ~msg:"equal empty" (rb_equal RBE RBE);

  (* -- Iter -- *)
  let buf = Buffer.create 16 in
  rb_iter (fun x -> Buffer.add_string buf (string_of_int x ^ ",")) (rb_of_list [3; 1; 2]);
  assert_equal ~msg:"iter order" "1,2,3," (Buffer.contents buf);

  (* -- Stress: insert 100 elements, verify invariants at each step -- *)
  let seq = List.init 100 (fun i -> (i * 37 + 13) mod 100) in
  let (final, all_valid) = List.fold_left (fun (t, ok) x ->
    let t' = rb_insert x t in
    (t', ok && rb_is_valid t')
  ) (RBE, true) seq in
  assert_true ~msg:"stress 100 all valid" all_valid;
  let final_list = rb_to_list final in
  let sorted = List.sort compare final_list in
  assert_true ~msg:"stress 100 sorted" (final_list = sorted);
  (* Verify no duplicates *)
  let unique = List.sort_uniq compare seq in
  assert_equal ~msg:"stress 100 cardinal" (string_of_int (List.length unique))
    (string_of_int (rb_cardinal final));

  (* -- Stress: delete half -- *)
  let to_delete = List.filteri (fun i _ -> i mod 2 = 0) (rb_to_list final) in
  let (after_del, del_valid) = List.fold_left (fun (t, ok) x ->
    let t' = rb_delete x t in
    (t', ok && rb_is_valid t')
  ) (final, true) to_delete in
  assert_true ~msg:"stress delete valid" del_valid;
  assert_equal ~msg:"stress delete cardinal"
    (string_of_int (rb_cardinal final - List.length to_delete))
    (string_of_int (rb_cardinal after_del));

  (* -- Large sequential insert (worst case for plain BST) -- *)
  let sequential = rb_of_list (List.init 50 (fun i -> i)) in
  assert_true ~msg:"sequential valid" (rb_is_valid sequential);
  assert_equal ~msg:"sequential cardinal" "50" (string_of_int (rb_cardinal sequential));
  let sh = rb_height sequential in
  (* Height must be << 50 for balanced tree *)
  assert_true ~msg:"sequential balanced" (sh <= 12);

  (* -- Reverse sequential -- *)
  let rev_seq = rb_of_list (List.init 50 (fun i -> 49 - i)) in
  assert_true ~msg:"reverse sequential valid" (rb_is_valid rev_seq);
  assert_true ~msg:"reverse sequential equal" (rb_equal sequential rev_seq);
)

(* ===== Sorting functions (from sorting.ml) ===== *)

let sort_is_sorted cmp lst =
  let rec aux = function
    | [] | [_] -> true
    | x :: (y :: _ as rest) -> cmp x y <= 0 && aux rest
  in
  aux lst

let sort_is_strictly_sorted cmp lst =
  let rec aux = function
    | [] | [_] -> true
    | x :: (y :: _ as rest) -> cmp x y < 0 && aux rest
  in
  aux lst

let rec sort_insert cmp x = function
  | [] -> [x]
  | h :: t as lst ->
    if cmp x h <= 0 then x :: lst
    else h :: sort_insert cmp x t

let sort_insertion cmp lst =
  List.fold_left (fun acc x -> sort_insert cmp x acc) [] lst

let sort_select_min cmp = function
  | [] -> failwith "select_min: empty list"
  | h :: t ->
    let rec aux min_val acc = function
      | [] -> (min_val, List.rev acc)
      | x :: rest ->
        if cmp x min_val < 0 then
          aux x (min_val :: acc) rest
        else
          aux min_val (x :: acc) rest
    in
    aux h [] t

let sort_selection cmp lst =
  let rec aux acc = function
    | [] -> List.rev acc
    | remaining ->
      let (min_val, rest) = sort_select_min cmp remaining in
      aux (min_val :: acc) rest
  in
  aux [] lst

let sort_partition3 cmp pivot lst =
  let rec aux lt eq gt = function
    | [] -> (List.rev lt, List.rev eq, List.rev gt)
    | x :: rest ->
      let c = cmp x pivot in
      if c < 0 then aux (x :: lt) eq gt rest
      else if c = 0 then aux lt (x :: eq) gt rest
      else aux lt eq (x :: gt) rest
  in
  aux [] [] [] lst

let sort_median_of_three cmp lst =
  match lst with
  | [] | [_] -> List.hd lst
  | [a; b] -> if cmp a b <= 0 then a else b
  | _ ->
    let len = List.length lst in
    let a = List.hd lst in
    let b = List.nth lst (len / 2) in
    let c = List.nth lst (len - 1) in
    if cmp a b <= 0 then
      (if cmp b c <= 0 then b
       else if cmp a c <= 0 then c else a)
    else
      (if cmp a c <= 0 then a
       else if cmp b c <= 0 then c else b)

let rec sort_quick cmp = function
  | ([] | [_]) as l -> l
  | lst ->
    let pivot = sort_median_of_three cmp lst in
    let (lt, eq, gt) = sort_partition3 cmp pivot lst in
    sort_quick cmp lt @ eq @ sort_quick cmp gt

type 'a sort_heap =
  | SHEmpty
  | SHNode of int * 'a * 'a sort_heap * 'a sort_heap

let sort_heap_rank = function
  | SHEmpty -> 0
  | SHNode (r, _, _, _) -> r

let sort_heap_make x a b =
  if sort_heap_rank a >= sort_heap_rank b then SHNode (sort_heap_rank b + 1, x, a, b)
  else SHNode (sort_heap_rank a + 1, x, b, a)

let rec sort_heap_merge cmp h1 h2 =
  match h1, h2 with
  | SHEmpty, h | h, SHEmpty -> h
  | SHNode (_, x, a1, b1), SHNode (_, y, _, _) ->
    if cmp x y <= 0 then sort_heap_make x a1 (sort_heap_merge cmp b1 h2)
    else sort_heap_merge cmp h2 h1

let sort_heap_insert cmp x h = sort_heap_merge cmp (SHNode (1, x, SHEmpty, SHEmpty)) h

let sort_heap_extract cmp = function
  | SHEmpty -> None
  | SHNode (_, x, left, right) -> Some (x, sort_heap_merge cmp left right)

let sort_heapsort cmp lst =
  let h = List.fold_left (fun h x -> sort_heap_insert cmp x h) SHEmpty lst in
  let rec drain acc h =
    match sort_heap_extract cmp h with
    | None -> List.rev acc
    | Some (x, h') -> drain (x :: acc) h'
  in
  drain [] h

let sort_counting ?(lo=0) ~hi lst =
  if hi < lo then failwith "counting_sort: hi < lo";
  let range = hi - lo + 1 in
  let counts = Array.make range 0 in
  List.iter (fun x ->
    if x < lo || x > hi then
      failwith (Printf.sprintf "counting_sort: %d out of range [%d, %d]" x lo hi);
    counts.(x - lo) <- counts.(x - lo) + 1
  ) lst;
  let result = ref [] in
  for i = range - 1 downto 0 do
    for _ = 1 to counts.(i) do
      result := (i + lo) :: !result
    done
  done;
  !result

let sort_find_runs cmp lst =
  let rec build_run run = function
    | [] -> [List.rev run]
    | x :: rest ->
      if cmp x (List.hd run) >= 0 then
        build_run (x :: run) rest
      else
        List.rev run :: build_run [x] rest
  in
  match lst with
  | [] -> []
  | x :: rest -> build_run [x] rest

let sort_merge cmp l1 l2 =
  let rec aux acc l1 l2 =
    match l1, l2 with
    | [], l | l, [] -> List.rev_append acc l
    | h1 :: t1, h2 :: t2 ->
      if cmp h1 h2 <= 0 then aux (h1 :: acc) t1 l2
      else aux (h2 :: acc) l1 t2
  in
  aux [] l1 l2

let rec sort_merge_runs cmp = function
  | [] -> []
  | [single] -> single
  | runs ->
    let rec pairwise acc = function
      | [] -> List.rev acc
      | [r] -> List.rev (r :: acc)
      | r1 :: r2 :: rest -> pairwise (sort_merge cmp r1 r2 :: acc) rest
    in
    sort_merge_runs cmp (pairwise [] runs)

let sort_natural_merge cmp lst =
  match lst with
  | ([] | [_]) as l -> l
  | _ -> sort_merge_runs cmp (sort_find_runs cmp lst)

(* ===== Sorting tests ===== *)

let test_sorting () = suite "Sorting" (fun () ->
  let sil = string_of_int_list in

  (* -- is_sorted / is_strictly_sorted -- *)
  assert_true ~msg:"is_sorted empty" (sort_is_sorted compare []);
  assert_true ~msg:"is_sorted singleton" (sort_is_sorted compare [5]);
  assert_true ~msg:"is_sorted asc" (sort_is_sorted compare [1; 2; 3; 4; 5]);
  assert_true ~msg:"is_sorted equal" (sort_is_sorted compare [3; 3; 3]);
  assert_true ~msg:"is_sorted not desc" (not (sort_is_sorted compare [5; 3; 1]));
  assert_true ~msg:"strictly empty" (sort_is_strictly_sorted compare []);
  assert_true ~msg:"strictly asc" (sort_is_strictly_sorted compare [1; 2; 3]);
  assert_true ~msg:"strictly not equal" (not (sort_is_strictly_sorted compare [1; 1; 2]));

  (* -- Insertion sort -- *)
  assert_equal ~msg:"ins empty" "[]" (sil (sort_insertion compare []));
  assert_equal ~msg:"ins [1]" "[1]" (sil (sort_insertion compare [1]));
  assert_equal ~msg:"ins sorted" "[1; 2; 3; 4; 5]"
    (sil (sort_insertion compare [1; 2; 3; 4; 5]));
  assert_equal ~msg:"ins reverse" "[1; 2; 3; 4; 5]"
    (sil (sort_insertion compare [5; 4; 3; 2; 1]));
  assert_equal ~msg:"ins mixed" "[3; 9; 10; 27; 38; 43; 82]"
    (sil (sort_insertion compare [38; 27; 43; 3; 9; 82; 10]));
  assert_equal ~msg:"ins dupes" "[1; 2; 2; 3; 3; 5]"
    (sil (sort_insertion compare [3; 1; 2; 5; 2; 3]));
  assert_equal ~msg:"ins all same" "[7; 7; 7; 7]"
    (sil (sort_insertion compare [7; 7; 7; 7]));
  assert_equal ~msg:"ins desc cmp" "[82; 43; 38; 27; 10; 9; 3]"
    (sil (sort_insertion (fun a b -> compare b a) [38; 27; 43; 3; 9; 82; 10]));
  assert_true ~msg:"ins stable" (sort_is_sorted compare (sort_insertion compare [38; 27; 43; 3; 9; 82; 10]));

  (* -- Selection sort -- *)
  assert_equal ~msg:"sel empty" "[]" (sil (sort_selection compare []));
  assert_equal ~msg:"sel [1]" "[1]" (sil (sort_selection compare [1]));
  assert_equal ~msg:"sel sorted" "[1; 2; 3; 4; 5]"
    (sil (sort_selection compare [1; 2; 3; 4; 5]));
  assert_equal ~msg:"sel reverse" "[1; 2; 3; 4; 5]"
    (sil (sort_selection compare [5; 4; 3; 2; 1]));
  assert_equal ~msg:"sel mixed" "[3; 9; 10; 27; 38; 43; 82]"
    (sil (sort_selection compare [38; 27; 43; 3; 9; 82; 10]));
  assert_equal ~msg:"sel dupes" "[1; 2; 2; 3; 3; 5]"
    (sil (sort_selection compare [3; 1; 2; 5; 2; 3]));
  assert_equal ~msg:"sel desc" "[82; 43; 38; 27; 10; 9; 3]"
    (sil (sort_selection (fun a b -> compare b a) [38; 27; 43; 3; 9; 82; 10]));

  (* -- Quicksort -- *)
  assert_equal ~msg:"qs empty" "[]" (sil (sort_quick compare []));
  assert_equal ~msg:"qs [1]" "[1]" (sil (sort_quick compare [1]));
  assert_equal ~msg:"qs sorted" "[1; 2; 3; 4; 5]"
    (sil (sort_quick compare [1; 2; 3; 4; 5]));
  assert_equal ~msg:"qs reverse" "[1; 2; 3; 4; 5]"
    (sil (sort_quick compare [5; 4; 3; 2; 1]));
  assert_equal ~msg:"qs mixed" "[3; 9; 10; 27; 38; 43; 82]"
    (sil (sort_quick compare [38; 27; 43; 3; 9; 82; 10]));
  assert_equal ~msg:"qs dupes" "[1; 2; 2; 3; 3; 5]"
    (sil (sort_quick compare [3; 1; 2; 5; 2; 3]));
  assert_equal ~msg:"qs all same" "[7; 7; 7; 7]"
    (sil (sort_quick compare [7; 7; 7; 7]));
  assert_equal ~msg:"qs [2;1]" "[1; 2]" (sil (sort_quick compare [2; 1]));
  assert_equal ~msg:"qs desc" "[82; 43; 38; 27; 10; 9; 3]"
    (sil (sort_quick (fun a b -> compare b a) [38; 27; 43; 3; 9; 82; 10]));

  (* -- Heapsort -- *)
  assert_equal ~msg:"hs empty" "[]" (sil (sort_heapsort compare []));
  assert_equal ~msg:"hs [1]" "[1]" (sil (sort_heapsort compare [1]));
  assert_equal ~msg:"hs sorted" "[1; 2; 3; 4; 5]"
    (sil (sort_heapsort compare [1; 2; 3; 4; 5]));
  assert_equal ~msg:"hs reverse" "[1; 2; 3; 4; 5]"
    (sil (sort_heapsort compare [5; 4; 3; 2; 1]));
  assert_equal ~msg:"hs mixed" "[3; 9; 10; 27; 38; 43; 82]"
    (sil (sort_heapsort compare [38; 27; 43; 3; 9; 82; 10]));
  assert_equal ~msg:"hs dupes" "[1; 2; 2; 3; 3; 5]"
    (sil (sort_heapsort compare [3; 1; 2; 5; 2; 3]));
  assert_equal ~msg:"hs desc" "[82; 43; 38; 27; 10; 9; 3]"
    (sil (sort_heapsort (fun a b -> compare b a) [38; 27; 43; 3; 9; 82; 10]));

  (* -- Counting sort -- *)
  assert_equal ~msg:"cs empty" "[]" (sil (sort_counting ~hi:10 []));
  assert_equal ~msg:"cs [5]" "[5]" (sil (sort_counting ~hi:5 [5]));
  assert_equal ~msg:"cs basic" "[1; 2; 3; 4; 5]"
    (sil (sort_counting ~hi:5 [3; 1; 5; 2; 4]));
  assert_equal ~msg:"cs dupes" "[1; 2; 2; 3; 3; 5]"
    (sil (sort_counting ~hi:5 [3; 1; 2; 5; 2; 3]));
  assert_equal ~msg:"cs all same" "[7; 7; 7; 7]"
    (sil (sort_counting ~hi:7 [7; 7; 7; 7]));
  assert_equal ~msg:"cs negative range" "[-3; -2; -1; 0; 1]"
    (sil (sort_counting ~lo:(-3) ~hi:1 [0; -2; 1; -3; -1]));
  assert_equal ~msg:"cs large range" "[0; 50; 100]"
    (sil (sort_counting ~hi:100 [100; 0; 50]));
  assert_raises ~msg:"cs hi < lo" (fun () -> sort_counting ~lo:10 ~hi:5 [1]);
  assert_raises ~msg:"cs out of range" (fun () -> sort_counting ~hi:5 [10]);

  (* -- Natural mergesort -- *)
  assert_equal ~msg:"nm empty" "[]" (sil (sort_natural_merge compare []));
  assert_equal ~msg:"nm [1]" "[1]" (sil (sort_natural_merge compare [1]));
  assert_equal ~msg:"nm sorted" "[1; 2; 3; 4; 5]"
    (sil (sort_natural_merge compare [1; 2; 3; 4; 5]));
  assert_equal ~msg:"nm reverse" "[1; 2; 3; 4; 5]"
    (sil (sort_natural_merge compare [5; 4; 3; 2; 1]));
  assert_equal ~msg:"nm mixed" "[3; 9; 10; 27; 38; 43; 82]"
    (sil (sort_natural_merge compare [38; 27; 43; 3; 9; 82; 10]));
  assert_equal ~msg:"nm dupes" "[1; 2; 2; 3; 3; 5]"
    (sil (sort_natural_merge compare [3; 1; 2; 5; 2; 3]));
  assert_equal ~msg:"nm nearly sorted" "[1; 2; 3; 4; 5; 6; 7]"
    (sil (sort_natural_merge compare [1; 2; 3; 7; 4; 5; 6]));

  (* -- find_runs -- *)
  let runs = sort_find_runs compare [1; 3; 5; 2; 4; 1; 6] in
  assert_equal ~msg:"runs count" "3" (string_of_int (List.length runs));
  assert_equal ~msg:"run 1" "[1; 3; 5]" (sil (List.nth runs 0));
  assert_equal ~msg:"run 2" "[2; 4]" (sil (List.nth runs 1));
  assert_equal ~msg:"run 3" "[1; 6]" (sil (List.nth runs 2));
  assert_equal ~msg:"runs empty" "0" (string_of_int (List.length (sort_find_runs compare [])));
  assert_equal ~msg:"runs sorted" "1" (string_of_int (List.length (sort_find_runs compare [1; 2; 3; 4; 5])));

  (* -- partition3 -- *)
  let (lt, eq, gt) = sort_partition3 compare 5 [3; 5; 8; 1; 5; 9; 2] in
  assert_equal ~msg:"p3 lt" "[1; 2; 3]" (sil (List.sort compare lt));
  assert_equal ~msg:"p3 eq" "[5; 5]" (sil eq);
  assert_equal ~msg:"p3 gt" "[8; 9]" (sil (List.sort compare gt));

  (* -- All algorithms agree on random data -- *)
  Random.init 42;
  let random_data = List.init 100 (fun _ -> Random.int 1000) in
  let expected = List.sort compare random_data in
  assert_equal ~msg:"all agree: insertion" (sil expected) (sil (sort_insertion compare random_data));
  assert_equal ~msg:"all agree: selection" (sil expected) (sil (sort_selection compare random_data));
  assert_equal ~msg:"all agree: quick" (sil expected) (sil (sort_quick compare random_data));
  assert_equal ~msg:"all agree: heapsort" (sil expected) (sil (sort_heapsort compare random_data));
  assert_equal ~msg:"all agree: natural merge" (sil expected) (sil (sort_natural_merge compare random_data));

  (* -- String sorting -- *)
  let words = sort_quick String.compare ["banana"; "apple"; "cherry"; "date"; "apple"] in
  assert_equal ~msg:"qs strings" "apple" (List.hd words);
  assert_equal ~msg:"qs strings last" "date" (List.nth words 4);
  assert_true ~msg:"qs strings sorted" (sort_is_sorted String.compare words);

  (* -- Larger random data -- *)
  let big_data = List.init 500 (fun _ -> Random.int 10000) in
  assert_true ~msg:"big insertion sorted" (sort_is_sorted compare (sort_insertion compare big_data));
  assert_true ~msg:"big quick sorted" (sort_is_sorted compare (sort_quick compare big_data));
  assert_true ~msg:"big heapsort sorted" (sort_is_sorted compare (sort_heapsort compare big_data));
  assert_true ~msg:"big natural merge sorted" (sort_is_sorted compare (sort_natural_merge compare big_data));
  assert_true ~msg:"big counting sorted" (sort_is_sorted compare (sort_counting ~hi:10000 big_data));

  (* -- Edge case: two elements -- *)
  assert_equal ~msg:"two sorted" "[1; 2]" (sil (sort_quick compare [1; 2]));
  assert_equal ~msg:"two reverse" "[1; 2]" (sil (sort_quick compare [2; 1]));
  assert_equal ~msg:"two equal" "[5; 5]" (sil (sort_quick compare [5; 5]));

  (* -- Stability of insertion sort -- *)
  let pairs = [(3, "a"); (1, "b"); (3, "c"); (2, "d"); (1, "e")] in
  let sorted_pairs = sort_insertion (fun (a, _) (b, _) -> compare a b) pairs in
  let first_three = List.filter (fun (k, _) -> k = 3) sorted_pairs in
  assert_equal ~msg:"ins stability" "a" (snd (List.nth first_three 0));
  assert_equal ~msg:"ins stability 2" "c" (snd (List.nth first_three 1));
)

(* ===== Union-Find functions (from union_find.ml) ===== *)

module UfIntMap = Map.Make(Int)

type uf_t = {
  uf_parent : int UfIntMap.t;
  uf_rank   : int UfIntMap.t;
  uf_size   : int UfIntMap.t;
  uf_n      : int;
}

let uf_create n =
  if n < 0 then invalid_arg "UnionFind.create: negative size";
  let parent = ref UfIntMap.empty in
  let rank = ref UfIntMap.empty in
  let size = ref UfIntMap.empty in
  for i = 0 to n - 1 do
    parent := UfIntMap.add i i !parent;
    rank := UfIntMap.add i 0 !rank;
    size := UfIntMap.add i 1 !size;
  done;
  { uf_parent = !parent; uf_rank = !rank; uf_size = !size; uf_n = n }

let rec uf_find uf x =
  if not (UfIntMap.mem x uf.uf_parent) then
    invalid_arg (Printf.sprintf "UnionFind.find: element %d out of range" x);
  let px = UfIntMap.find x uf.uf_parent in
  if px = x then (x, uf)
  else
    let (root, uf') = uf_find uf px in
    let uf'' = { uf' with uf_parent = UfIntMap.add x root uf'.uf_parent } in
    (root, uf'')

let rec uf_find_root uf x =
  if not (UfIntMap.mem x uf.uf_parent) then
    invalid_arg (Printf.sprintf "UnionFind.find_root: element %d out of range" x);
  let px = UfIntMap.find x uf.uf_parent in
  if px = x then x
  else uf_find_root uf px

let uf_connected uf x y =
  uf_find_root uf x = uf_find_root uf y

let uf_union uf x y =
  let (rx, uf1) = uf_find uf x in
  let (ry, uf2) = uf_find uf1 y in
  if rx = ry then uf2
  else
    let rank_rx = UfIntMap.find rx uf2.uf_rank in
    let rank_ry = UfIntMap.find ry uf2.uf_rank in
    let size_rx = UfIntMap.find rx uf2.uf_size in
    let size_ry = UfIntMap.find ry uf2.uf_size in
    let new_size = size_rx + size_ry in
    if rank_rx < rank_ry then
      { uf2 with
        uf_parent = UfIntMap.add rx ry uf2.uf_parent;
        uf_size = UfIntMap.add ry new_size uf2.uf_size }
    else if rank_rx > rank_ry then
      { uf2 with
        uf_parent = UfIntMap.add ry rx uf2.uf_parent;
        uf_size = UfIntMap.add rx new_size uf2.uf_size }
    else
      { uf2 with
        uf_parent = UfIntMap.add ry rx uf2.uf_parent;
        uf_rank = UfIntMap.add rx (rank_rx + 1) uf2.uf_rank;
        uf_size = UfIntMap.add rx new_size uf2.uf_size }

let uf_num_components uf =
  UfIntMap.fold (fun k v count ->
    if k = v then count + 1 else count
  ) uf.uf_parent 0

let uf_component_size uf x =
  let root = uf_find_root uf x in
  UfIntMap.find root uf.uf_size

let uf_roots uf =
  UfIntMap.fold (fun k v acc ->
    if k = v then k :: acc else acc
  ) uf.uf_parent []
  |> List.rev

let uf_component_members uf x =
  let root = uf_find_root uf x in
  UfIntMap.fold (fun k _v acc ->
    if uf_find_root uf k = root then k :: acc else acc
  ) uf.uf_parent []
  |> List.rev

let uf_all_components uf =
  let tbl = Hashtbl.create 16 in
  UfIntMap.iter (fun k _v ->
    let root = uf_find_root uf k in
    let existing = try Hashtbl.find tbl root with Not_found -> [] in
    Hashtbl.replace tbl root (k :: existing)
  ) uf.uf_parent;
  Hashtbl.fold (fun _root members acc ->
    (List.sort compare members) :: acc
  ) tbl []
  |> List.sort compare

let uf_cardinal uf = uf.uf_n

let uf_is_single_component uf = uf_num_components uf = 1

let uf_of_unions n pairs =
  let uf = uf_create n in
  List.fold_left (fun acc (x, y) -> uf_union acc x y) uf pairs

let uf_kruskal n edges =
  let sorted_edges = List.sort (fun (w1, _, _) (w2, _, _) -> compare w1 w2) edges in
  let rec aux uf mst = function
    | [] -> List.rev mst
    | (w, u, v) :: rest ->
      if uf_connected uf u v then
        aux uf mst rest
      else
        let uf' = uf_union uf u v in
        aux uf' ((w, u, v) :: mst) rest
  in
  aux (uf_create n) [] sorted_edges

let uf_would_cycle uf u v = uf_connected uf u v

let uf_to_string uf =
  let components = uf_all_components uf in
  let comp_strs = List.map (fun members ->
    "{" ^ String.concat ", " (List.map string_of_int members) ^ "}"
  ) components in
  Printf.sprintf "UnionFind(%d elems, %d components): %s"
    uf.uf_n (uf_num_components uf) (String.concat " " comp_strs)

(* ===== Union-Find tests ===== *)

let test_union_find () = suite "Union-Find" (fun () ->
  let sil = string_of_int_list in
  let sill lst =
    "[" ^ String.concat "; "
      (List.map (fun l -> "[" ^ String.concat "; " (List.map string_of_int l) ^ "]") lst) ^ "]"
  in

  (* -- create -- *)
  let uf0 = uf_create 0 in
  assert_equal ~msg:"create 0 cardinal" "0" (string_of_int (uf_cardinal uf0));
  assert_equal ~msg:"create 0 components" "0" (string_of_int (uf_num_components uf0));

  let uf1 = uf_create 1 in
  assert_equal ~msg:"create 1 cardinal" "1" (string_of_int (uf_cardinal uf1));
  assert_equal ~msg:"create 1 components" "1" (string_of_int (uf_num_components uf1));

  let uf5 = uf_create 5 in
  assert_equal ~msg:"create 5 cardinal" "5" (string_of_int (uf_cardinal uf5));
  assert_equal ~msg:"create 5 components" "5" (string_of_int (uf_num_components uf5));

  assert_raises ~msg:"create negative" (fun () -> uf_create (-1));

  (* -- find_root on fresh -- *)
  assert_equal ~msg:"find_root fresh 0" "0" (string_of_int (uf_find_root uf5 0));
  assert_equal ~msg:"find_root fresh 4" "4" (string_of_int (uf_find_root uf5 4));

  assert_raises ~msg:"find_root out of range" (fun () -> uf_find_root uf5 5);
  assert_raises ~msg:"find_root negative" (fun () -> uf_find_root uf5 (-1));

  (* -- find with path compression -- *)
  let (r, _uf5') = uf_find uf5 3 in
  assert_equal ~msg:"find fresh 3" "3" (string_of_int r);

  assert_raises ~msg:"find out of range" (fun () -> uf_find uf5 10);

  (* -- connected on fresh -- *)
  assert_true ~msg:"connected self" (uf_connected uf5 0 0);
  assert_true ~msg:"not connected fresh" (not (uf_connected uf5 0 1));
  assert_true ~msg:"not connected fresh 2" (not (uf_connected uf5 2 4));

  (* -- basic union -- *)
  let uf_a = uf_union uf5 0 1 in
  assert_true ~msg:"union 0-1 connected" (uf_connected uf_a 0 1);
  assert_true ~msg:"union 0-1 not 0-2" (not (uf_connected uf_a 0 2));
  assert_equal ~msg:"union 0-1 components" "4" (string_of_int (uf_num_components uf_a));

  (* -- original unchanged (persistence) -- *)
  assert_true ~msg:"persistence: original 5 components"
    (uf_num_components uf5 = 5);
  assert_true ~msg:"persistence: original 0-1 not connected"
    (not (uf_connected uf5 0 1));

  (* -- chain of unions -- *)
  let uf_b = uf_union uf_a 2 3 in
  assert_true ~msg:"chain 2-3 connected" (uf_connected uf_b 2 3);
  assert_true ~msg:"chain 0-1 still connected" (uf_connected uf_b 0 1);
  assert_true ~msg:"chain 0-2 not connected" (not (uf_connected uf_b 0 2));
  assert_equal ~msg:"chain components" "3" (string_of_int (uf_num_components uf_b));

  (* -- merging two groups -- *)
  let uf_c = uf_union uf_b 1 3 in
  assert_true ~msg:"merge 1-3 => 0-2 connected" (uf_connected uf_c 0 2);
  assert_true ~msg:"merge 1-3 => 0-3 connected" (uf_connected uf_c 0 3);
  assert_true ~msg:"merge 1-3 => 1-2 connected" (uf_connected uf_c 1 2);
  assert_true ~msg:"merge 4 isolated" (not (uf_connected uf_c 0 4));
  assert_equal ~msg:"merge components" "2" (string_of_int (uf_num_components uf_c));

  (* -- union of already-connected -- *)
  let uf_d = uf_union uf_c 0 2 in
  assert_equal ~msg:"redundant union same components" "2"
    (string_of_int (uf_num_components uf_d));

  (* -- union all into one -- *)
  let uf_e = uf_union uf_d 0 4 in
  assert_true ~msg:"all one component" (uf_is_single_component uf_e);
  assert_equal ~msg:"single component count" "1" (string_of_int (uf_num_components uf_e));

  (* -- component_size -- *)
  assert_equal ~msg:"size fresh singleton" "1" (string_of_int (uf_component_size uf5 0));
  assert_equal ~msg:"size after union 0-1" "2" (string_of_int (uf_component_size uf_a 0));
  assert_equal ~msg:"size after union 0-1 via 1" "2" (string_of_int (uf_component_size uf_a 1));
  assert_equal ~msg:"size unaffected elem" "1" (string_of_int (uf_component_size uf_a 3));
  assert_equal ~msg:"size merged group" "4" (string_of_int (uf_component_size uf_c 0));
  assert_equal ~msg:"size all merged" "5" (string_of_int (uf_component_size uf_e 2));

  (* -- roots -- *)
  let roots5 = uf_roots uf5 in
  assert_equal ~msg:"roots fresh 5" "[0; 1; 2; 3; 4]" (sil roots5);
  let roots_a = uf_roots uf_a in
  assert_equal ~msg:"roots after union count" "4" (string_of_int (List.length roots_a));

  (* -- component_members -- *)
  let members_fresh = uf_component_members uf5 2 in
  assert_equal ~msg:"members fresh singleton" "[2]" (sil members_fresh);
  let members_a = List.sort compare (uf_component_members uf_a 0) in
  assert_equal ~msg:"members after union 0-1" "[0; 1]" (sil members_a);
  let members_c = List.sort compare (uf_component_members uf_c 3) in
  assert_equal ~msg:"members merged group" "[0; 1; 2; 3]" (sil members_c);

  (* -- all_components -- *)
  let comps_fresh = uf_all_components uf5 in
  assert_equal ~msg:"all_components fresh"
    "[[0]; [1]; [2]; [3]; [4]]" (sill comps_fresh);
  let comps_a = uf_all_components uf_a in
  assert_equal ~msg:"all_components after 0-1"
    "[[0; 1]; [2]; [3]; [4]]" (sill comps_a);
  let comps_c = uf_all_components uf_c in
  assert_equal ~msg:"all_components merged"
    "[[0; 1; 2; 3]; [4]]" (sill comps_c);
  let comps_e = uf_all_components uf_e in
  assert_equal ~msg:"all_components single"
    "[[0; 1; 2; 3; 4]]" (sill comps_e);

  (* -- of_unions -- *)
  let uf_from = uf_of_unions 6 [(0, 1); (2, 3); (4, 5)] in
  assert_equal ~msg:"of_unions components" "3"
    (string_of_int (uf_num_components uf_from));
  assert_true ~msg:"of_unions 0-1 connected" (uf_connected uf_from 0 1);
  assert_true ~msg:"of_unions 2-3 connected" (uf_connected uf_from 2 3);
  assert_true ~msg:"of_unions 4-5 connected" (uf_connected uf_from 4 5);
  assert_true ~msg:"of_unions 0-2 not connected" (not (uf_connected uf_from 0 2));

  let uf_chain = uf_of_unions 4 [(0, 1); (1, 2); (2, 3)] in
  assert_true ~msg:"of_unions chain all connected" (uf_is_single_component uf_chain);

  let uf_empty_pairs = uf_of_unions 3 [] in
  assert_equal ~msg:"of_unions no pairs" "3"
    (string_of_int (uf_num_components uf_empty_pairs));

  (* -- would_cycle -- *)
  assert_true ~msg:"would_cycle same component" (uf_would_cycle uf_a 0 1);
  assert_true ~msg:"would_cycle self" (uf_would_cycle uf5 0 0);
  assert_true ~msg:"no cycle diff components" (not (uf_would_cycle uf_a 0 2));

  (* -- kruskal -- *)
  (* Simple triangle: 0--1 (w=1), 1--2 (w=2), 0--2 (w=3) *)
  let mst_tri = uf_kruskal 3 [(1, 0, 1); (2, 1, 2); (3, 0, 2)] in
  assert_equal ~msg:"kruskal triangle edges" "2" (string_of_int (List.length mst_tri));
  let mst_weight = List.fold_left (fun acc (w, _, _) -> acc + w) 0 mst_tri in
  assert_equal ~msg:"kruskal triangle weight" "3" (string_of_int mst_weight);

  (* Square with diagonal:
       0-1 (1), 1-2 (2), 2-3 (3), 0-3 (4), 0-2 (5)
     MST should pick edges with weight 1+2+3=6 *)
  let mst_sq = uf_kruskal 4 [(1, 0, 1); (2, 1, 2); (3, 2, 3); (4, 0, 3); (5, 0, 2)] in
  assert_equal ~msg:"kruskal square edges" "3" (string_of_int (List.length mst_sq));
  let sq_weight = List.fold_left (fun acc (w, _, _) -> acc + w) 0 mst_sq in
  assert_equal ~msg:"kruskal square weight" "6" (string_of_int sq_weight);

  (* Disconnected graph: 0-1 (1), 2-3 (2) *)
  let mst_disc = uf_kruskal 4 [(1, 0, 1); (2, 2, 3)] in
  assert_equal ~msg:"kruskal disconnected edges" "2" (string_of_int (List.length mst_disc));

  (* Empty graph *)
  let mst_empty = uf_kruskal 3 [] in
  assert_equal ~msg:"kruskal empty" "0" (string_of_int (List.length mst_empty));

  (* Single node *)
  let mst_single = uf_kruskal 1 [] in
  assert_equal ~msg:"kruskal single" "0" (string_of_int (List.length mst_single));

  (* Pre-sorted by weight *)
  let mst_presorted = uf_kruskal 4 [(1, 0, 1); (2, 1, 2); (3, 2, 3); (10, 0, 3)] in
  assert_equal ~msg:"kruskal presorted 3 edges" "3" (string_of_int (List.length mst_presorted));
  let ps_weight = List.fold_left (fun acc (w, _, _) -> acc + w) 0 mst_presorted in
  assert_equal ~msg:"kruskal presorted weight" "6" (string_of_int ps_weight);

  (* -- to_string -- *)
  let s0 = uf_to_string uf5 in
  assert_true ~msg:"to_string contains 5 elems"
    (String.length s0 > 0 && String.sub s0 0 14 = "UnionFind(5 el");
  let s1 = uf_to_string uf_a in
  assert_true ~msg:"to_string after union"
    (String.length s1 > 0 && String.sub s1 0 14 = "UnionFind(5 el");

  (* -- is_single_component -- *)
  assert_true ~msg:"not single fresh 5" (not (uf_is_single_component uf5));
  assert_true ~msg:"single after all unions" (uf_is_single_component uf_e);
  assert_true ~msg:"single create 1" (uf_is_single_component (uf_create 1));

  (* -- larger structure -- *)
  let uf10 = uf_create 10 in
  let uf10 = uf_union uf10 0 5 in
  let uf10 = uf_union uf10 1 6 in
  let uf10 = uf_union uf10 2 7 in
  let uf10 = uf_union uf10 3 8 in
  let uf10 = uf_union uf10 4 9 in
  assert_equal ~msg:"10-elem paired components" "5"
    (string_of_int (uf_num_components uf10));
  assert_true ~msg:"10-elem 0-5 connected" (uf_connected uf10 0 5);
  assert_true ~msg:"10-elem 0-1 not connected" (not (uf_connected uf10 0 1));
  assert_equal ~msg:"10-elem pair size" "2" (string_of_int (uf_component_size uf10 0));

  (* Now merge pairs: {0,5} U {1,6} *)
  let uf10b = uf_union uf10 0 1 in
  assert_true ~msg:"10-elem merged 0-6" (uf_connected uf10b 0 6);
  assert_true ~msg:"10-elem merged 5-1" (uf_connected uf10b 5 1);
  assert_equal ~msg:"10-elem merged size" "4" (string_of_int (uf_component_size uf10b 0));
  assert_equal ~msg:"10-elem merged components" "4" (string_of_int (uf_num_components uf10b));

  (* -- path compression test -- *)
  (* Create a long chain: 0->1->2->3->4->5 *)
  let uf_chain = uf_create 6 in
  let uf_chain = uf_union uf_chain 0 1 in
  let uf_chain = uf_union uf_chain 1 2 in
  let uf_chain = uf_union uf_chain 2 3 in
  let uf_chain = uf_union uf_chain 3 4 in
  let uf_chain = uf_union uf_chain 4 5 in
  assert_true ~msg:"chain all connected" (uf_is_single_component uf_chain);
  (* Find from deep element triggers path compression *)
  let (root5, uf_chain') = uf_find uf_chain 5 in
  ignore uf_chain';
  assert_true ~msg:"chain root found" (root5 >= 0 && root5 <= 5);
  assert_equal ~msg:"chain size" "6" (string_of_int (uf_component_size uf_chain 0));

  (* -- cardinal -- *)
  assert_equal ~msg:"cardinal 0" "0" (string_of_int (uf_cardinal (uf_create 0)));
  assert_equal ~msg:"cardinal 5" "5" (string_of_int (uf_cardinal uf5));
  assert_equal ~msg:"cardinal 10" "10" (string_of_int (uf_cardinal uf10));
  (* cardinal unchanged after unions *)
  assert_equal ~msg:"cardinal after unions" "5" (string_of_int (uf_cardinal uf_e));

  (* -- kruskal with equal weights picks in order -- *)
  let mst_eq = uf_kruskal 3 [(1, 0, 1); (1, 1, 2); (1, 0, 2)] in
  assert_equal ~msg:"kruskal equal weights 2 edges" "2"
    (string_of_int (List.length mst_eq));

  (* -- self-loop edge in kruskal -- *)
  let mst_self = uf_kruskal 3 [(1, 0, 0); (2, 0, 1); (3, 1, 2)] in
  (* Self-loop 0-0 should be skipped (already connected to itself) *)
  assert_equal ~msg:"kruskal self-loop edges" "2"
    (string_of_int (List.length mst_self));

  (* -- union reflexive -- *)
  let uf_ref = uf_union uf5 2 2 in
  assert_equal ~msg:"union self components unchanged" "5"
    (string_of_int (uf_num_components uf_ref));

  (* -- stress: union all pairs 0..9 *)
  let uf_stress = uf_create 10 in
  let uf_stress = List.fold_left (fun acc i ->
    uf_union acc i ((i + 1) mod 10)
  ) uf_stress [0; 1; 2; 3; 4; 5; 6; 7; 8; 9] in
  assert_true ~msg:"stress 10 single component" (uf_is_single_component uf_stress);
  assert_equal ~msg:"stress 10 size" "10" (string_of_int (uf_component_size uf_stress 0));
)

(* ===== Functional Hash Map (from hashmap.ml) ===== *)

type ('k, 'v) hm_t = {
  hm_buckets : ('k * 'v) list array;
  hm_size    : int;
  hm_cap     : int;
}

let hm_default_cap = 16

let hm_create ?(capacity = hm_default_cap) () =
  let cap = max 1 capacity in
  { hm_buckets = Array.make cap []; hm_size = 0; hm_cap = cap }

let hm_empty = hm_create ()

let hm_hash_key cap k =
  (Hashtbl.hash k) mod cap |> abs

let hm_should_resize m =
  m.hm_size > (m.hm_cap * 3 / 4)

let hm_resize m =
  let new_cap = m.hm_cap * 2 in
  let new_b = Array.make new_cap [] in
  Array.iter (fun bucket ->
    List.iter (fun ((k, _) as pair) ->
      let idx = hm_hash_key new_cap k in
      new_b.(idx) <- pair :: new_b.(idx)
    ) bucket
  ) m.hm_buckets;
  { hm_buckets = new_b; hm_size = m.hm_size; hm_cap = new_cap }

let hm_insert k v m =
  let m = if hm_should_resize m then hm_resize m else m in
  let idx = hm_hash_key m.hm_cap k in
  let bucket = m.hm_buckets.(idx) in
  let existed = List.exists (fun (k', _) -> k' = k) bucket in
  let new_bucket =
    if existed then
      List.map (fun (k', v') -> if k' = k then (k, v) else (k', v')) bucket
    else
      (k, v) :: bucket
  in
  let new_b = Array.copy m.hm_buckets in
  new_b.(idx) <- new_bucket;
  { hm_buckets = new_b;
    hm_size = if existed then m.hm_size else m.hm_size + 1;
    hm_cap = m.hm_cap }

let hm_find k m =
  let idx = hm_hash_key m.hm_cap k in
  let rec search = function
    | [] -> None
    | (k', v) :: _ when k' = k -> Some v
    | _ :: rest -> search rest
  in
  search m.hm_buckets.(idx)

let hm_find_exn k m =
  match hm_find k m with
  | Some v -> v
  | None -> raise Not_found

let hm_mem k m =
  hm_find k m <> None

let hm_remove k m =
  let idx = hm_hash_key m.hm_cap k in
  let bucket = m.hm_buckets.(idx) in
  let existed = List.exists (fun (k', _) -> k' = k) bucket in
  if not existed then m
  else begin
    let new_bucket = List.filter (fun (k', _) -> k' <> k) bucket in
    let new_b = Array.copy m.hm_buckets in
    new_b.(idx) <- new_bucket;
    { hm_buckets = new_b;
      hm_size = m.hm_size - 1;
      hm_cap = m.hm_cap }
  end

let hm_size m = m.hm_size

let hm_is_empty m = m.hm_size = 0

let hm_fold f acc m =
  Array.fold_left (fun acc bucket ->
    List.fold_left (fun acc (k, v) -> f acc k v) acc bucket
  ) acc m.hm_buckets

let hm_iter f m =
  Array.iter (fun bucket ->
    List.iter (fun (k, v) -> f k v) bucket
  ) m.hm_buckets

let hm_map f m =
  let new_b = Array.map (fun bucket ->
    List.map (fun (k, v) -> (k, f v)) bucket
  ) m.hm_buckets in
  { m with hm_buckets = new_b }

let hm_mapi f m =
  let new_b = Array.map (fun bucket ->
    List.map (fun (k, v) -> (k, f k v)) bucket
  ) m.hm_buckets in
  { m with hm_buckets = new_b }

let hm_filter f m =
  let new_b = Array.make m.hm_cap [] in
  let new_size = ref 0 in
  Array.iteri (fun i bucket ->
    let filtered = List.filter (fun (k, v) -> f k v) bucket in
    new_b.(i) <- filtered;
    new_size := !new_size + List.length filtered
  ) m.hm_buckets;
  { hm_buckets = new_b; hm_size = !new_size; hm_cap = m.hm_cap }

let hm_keys m =
  hm_fold (fun acc k _v -> k :: acc) [] m

let hm_values m =
  hm_fold (fun acc _k v -> v :: acc) [] m

let hm_bindings m =
  hm_fold (fun acc k v -> (k, v) :: acc) [] m

let hm_of_list pairs =
  List.fold_left (fun m (k, v) -> hm_insert k v m) hm_empty pairs

let hm_to_list m = hm_bindings m

let hm_for_all f m =
  try
    hm_iter (fun k v -> if not (f k v) then raise Exit) m;
    true
  with Exit -> false

let hm_exists f m =
  try
    hm_iter (fun k v -> if f k v then raise Exit) m;
    false
  with Exit -> true

let hm_equal eq m1 m2 =
  m1.hm_size = m2.hm_size &&
  hm_for_all (fun k v ->
    match hm_find k m2 with
    | Some v2 -> eq v v2
    | None -> false
  ) m1

let hm_merge f m1 m2 =
  let result = hm_fold (fun acc k v ->
    match hm_find k m2 with
    | None -> hm_insert k (f k v None) acc
    | Some v2 -> hm_insert k (f k v (Some v2)) acc
  ) (hm_create ()) m1 in
  hm_fold (fun acc k v ->
    if not (hm_mem k m1) then
      hm_insert k (f k v None) acc
    else acc
  ) result m2

let hm_update k f m =
  let old_v = hm_find k m in
  match f old_v with
  | None ->
    (match old_v with
     | None -> m
     | Some _ -> hm_remove k m)
  | Some new_v -> hm_insert k new_v m

let hm_singleton k v = hm_insert k v hm_empty

let hm_union f m1 m2 =
  hm_fold (fun acc k v ->
    match hm_find k acc with
    | None -> hm_insert k v acc
    | Some v' -> hm_insert k (f k v v') acc
  ) m2 m1

let hm_partition f m =
  let yes = ref (hm_create ()) in
  let no = ref (hm_create ()) in
  hm_iter (fun k v ->
    if f k v then yes := hm_insert k v !yes
    else no := hm_insert k v !no
  ) m;
  (!yes, !no)

let hm_cardinal m = m.hm_size

let hm_choose m =
  if hm_is_empty m then raise Not_found
  else begin
    let result = ref None in
    (try
      hm_iter (fun k v -> result := Some (k, v); raise Exit) m
    with Exit -> ());
    match !result with
    | Some pair -> pair
    | None -> raise Not_found
  end

(* ===== Hash Map Tests ===== *)

let test_hashmap () = suite "Hash Map" (fun () ->
  (* -- create and empty -- *)
  let m0 = hm_create () in
  assert_true ~msg:"empty is empty" (hm_is_empty m0);
  assert_equal ~msg:"empty size" "0" (string_of_int (hm_size m0));

  (* -- insert and find -- *)
  let m1 = hm_insert "a" 1 m0 in
  assert_equal ~msg:"find a" "1" (string_of_int (hm_find_exn "a" m1));
  assert_equal ~msg:"size after insert" "1" (string_of_int (hm_size m1));
  assert_true ~msg:"mem a" (hm_mem "a" m1);
  assert_true ~msg:"not mem b" (not (hm_mem "b" m1));

  (* -- original unchanged (persistence) -- *)
  assert_true ~msg:"m0 still empty" (hm_is_empty m0);

  (* -- multiple inserts -- *)
  let m2 = hm_insert "b" 2 (hm_insert "c" 3 m1) in
  assert_equal ~msg:"size 3" "3" (string_of_int (hm_size m2));
  assert_equal ~msg:"find b" "2" (string_of_int (hm_find_exn "b" m2));
  assert_equal ~msg:"find c" "3" (string_of_int (hm_find_exn "c" m2));

  (* -- update existing key -- *)
  let m3 = hm_insert "a" 10 m2 in
  assert_equal ~msg:"update a" "10" (string_of_int (hm_find_exn "a" m3));
  assert_equal ~msg:"size after update" "3" (string_of_int (hm_size m3));
  (* old version still has 1 *)
  assert_equal ~msg:"m2 still has a=1" "1" (string_of_int (hm_find_exn "a" m2));

  (* -- find None for missing -- *)
  assert_true ~msg:"find missing None" (hm_find "z" m2 = None);

  (* -- find_exn raises -- *)
  assert_raises ~msg:"find_exn raises" (fun () -> hm_find_exn "z" m2);

  (* -- remove -- *)
  let m4 = hm_remove "b" m2 in
  assert_equal ~msg:"size after remove" "2" (string_of_int (hm_size m4));
  assert_true ~msg:"b removed" (not (hm_mem "b" m4));
  assert_true ~msg:"a still there" (hm_mem "a" m4);
  assert_true ~msg:"c still there" (hm_mem "c" m4);

  (* -- remove non-existent is identity -- *)
  let m5 = hm_remove "zzz" m2 in
  assert_equal ~msg:"remove missing size" "3" (string_of_int (hm_size m5));

  (* -- of_list and to_list -- *)
  let m6 = hm_of_list [("x", 10); ("y", 20); ("z", 30)] in
  assert_equal ~msg:"of_list size" "3" (string_of_int (hm_size m6));
  assert_equal ~msg:"of_list find x" "10" (string_of_int (hm_find_exn "x" m6));
  assert_equal ~msg:"of_list find y" "20" (string_of_int (hm_find_exn "y" m6));
  let bindings = List.sort compare (hm_to_list m6) in
  assert_equal ~msg:"to_list length" "3" (string_of_int (List.length bindings));

  (* -- keys and values -- *)
  let ks = List.sort compare (hm_keys m6) in
  assert_equal ~msg:"keys" "[x; y; z]" ("[" ^ String.concat "; " ks ^ "]");
  let vs = List.sort compare (hm_values m6) in
  assert_equal ~msg:"values" "[10; 20; 30]" (string_of_int_list vs);

  (* -- fold -- *)
  let sum = hm_fold (fun acc _k v -> acc + v) 0 m6 in
  assert_equal ~msg:"fold sum" "60" (string_of_int sum);

  let concat = hm_fold (fun acc k _v ->
    if acc = "" then k else acc ^ "," ^ k
  ) "" (hm_of_list [("only", 1)]) in
  assert_equal ~msg:"fold single" "only" concat;

  (* -- map -- *)
  let m7 = hm_map (fun v -> v * 2) m6 in
  assert_equal ~msg:"map x*2" "20" (string_of_int (hm_find_exn "x" m7));
  assert_equal ~msg:"map y*2" "40" (string_of_int (hm_find_exn "y" m7));
  assert_equal ~msg:"map z*2" "60" (string_of_int (hm_find_exn "z" m7));
  (* original unchanged *)
  assert_equal ~msg:"map original" "10" (string_of_int (hm_find_exn "x" m6));

  (* -- mapi -- *)
  let m7b = hm_mapi (fun k v -> String.length k + v) m6 in
  assert_equal ~msg:"mapi x" "11" (string_of_int (hm_find_exn "x" m7b)); (* 1 + 10 *)
  assert_equal ~msg:"mapi y" "21" (string_of_int (hm_find_exn "y" m7b)); (* 1 + 20 *)

  (* -- filter -- *)
  let m8 = hm_filter (fun _k v -> v > 15) m6 in
  assert_equal ~msg:"filter size" "2" (string_of_int (hm_size m8));
  assert_true ~msg:"filter keeps y" (hm_mem "y" m8);
  assert_true ~msg:"filter keeps z" (hm_mem "z" m8);
  assert_true ~msg:"filter removes x" (not (hm_mem "x" m8));

  (* -- for_all -- *)
  assert_true ~msg:"for_all >0" (hm_for_all (fun _k v -> v > 0) m6);
  assert_true ~msg:"not for_all >25" (not (hm_for_all (fun _k v -> v > 25) m6));

  (* -- exists -- *)
  assert_true ~msg:"exists =30" (hm_exists (fun _k v -> v = 30) m6);
  assert_true ~msg:"not exists =99" (not (hm_exists (fun _k v -> v = 99) m6));

  (* -- equal -- *)
  let m6copy = hm_of_list [("z", 30); ("x", 10); ("y", 20)] in
  assert_true ~msg:"equal same" (hm_equal (=) m6 m6copy);
  let m6diff = hm_insert "x" 999 m6 in
  assert_true ~msg:"not equal diff val" (not (hm_equal (=) m6 m6diff));
  let m6more = hm_insert "w" 40 m6 in
  assert_true ~msg:"not equal diff size" (not (hm_equal (=) m6 m6more));

  (* -- merge -- *)
  let ma = hm_of_list [("a", 1); ("b", 2)] in
  let mb = hm_of_list [("b", 20); ("c", 30)] in
  let merged = hm_merge (fun _k v opt ->
    match opt with None -> v | Some v2 -> v + v2
  ) ma mb in
  assert_equal ~msg:"merge size" "3" (string_of_int (hm_size merged));
  assert_equal ~msg:"merge a" "1" (string_of_int (hm_find_exn "a" merged));
  assert_equal ~msg:"merge b" "22" (string_of_int (hm_find_exn "b" merged));
  assert_equal ~msg:"merge c" "30" (string_of_int (hm_find_exn "c" merged));

  (* -- union -- *)
  let u = hm_union (fun _k v1 v2 -> v1 + v2) ma mb in
  assert_equal ~msg:"union a" "1" (string_of_int (hm_find_exn "a" u));
  assert_equal ~msg:"union b" "22" (string_of_int (hm_find_exn "b" u));
  assert_equal ~msg:"union c" "30" (string_of_int (hm_find_exn "c" u));

  (* -- update -- *)
  let m9 = hm_update "a" (function None -> Some 42 | Some v -> Some (v + 1)) m2 in
  assert_equal ~msg:"update existing" "2" (string_of_int (hm_find_exn "a" m9));
  let m9b = hm_update "new" (function None -> Some 42 | Some v -> Some (v + 1)) m2 in
  assert_equal ~msg:"update new" "42" (string_of_int (hm_find_exn "new" m9b));
  let m9c = hm_update "a" (fun _ -> None) m2 in
  assert_true ~msg:"update remove" (not (hm_mem "a" m9c));
  let m9d = hm_update "missing" (fun _ -> None) m2 in
  assert_equal ~msg:"update remove missing" "3" (string_of_int (hm_size m9d));

  (* -- singleton -- *)
  let ms = hm_singleton "solo" 99 in
  assert_equal ~msg:"singleton size" "1" (string_of_int (hm_size ms));
  assert_equal ~msg:"singleton val" "99" (string_of_int (hm_find_exn "solo" ms));

  (* -- partition -- *)
  let (yes, no) = hm_partition (fun _k v -> v > 15) m6 in
  assert_equal ~msg:"partition yes size" "2" (string_of_int (hm_size yes));
  assert_equal ~msg:"partition no size" "1" (string_of_int (hm_size no));
  assert_true ~msg:"partition yes has y" (hm_mem "y" yes);
  assert_true ~msg:"partition no has x" (hm_mem "x" no);

  (* -- cardinal == size -- *)
  assert_equal ~msg:"cardinal" "3" (string_of_int (hm_cardinal m6));

  (* -- choose -- *)
  let (ck, cv) = hm_choose m6 in
  assert_true ~msg:"choose is member" (hm_mem ck m6);
  assert_equal ~msg:"choose val matches" (string_of_int cv) (string_of_int (hm_find_exn ck m6));

  (* -- choose empty raises -- *)
  assert_raises ~msg:"choose empty raises" (fun () -> hm_choose (hm_create ()));

  (* -- integer keys -- *)
  let mint = hm_of_list [(1, "one"); (2, "two"); (3, "three")] in
  assert_equal ~msg:"int key find" "two" (hm_find_exn 2 mint);
  assert_equal ~msg:"int key size" "3" (string_of_int (hm_size mint));

  (* -- many insertions (trigger resize) -- *)
  let big = ref (hm_create ~capacity:4 ()) in
  for i = 0 to 99 do
    big := hm_insert i (i * i) !big
  done;
  assert_equal ~msg:"big size" "100" (string_of_int (hm_size !big));
  assert_equal ~msg:"big find 0" "0" (string_of_int (hm_find_exn 0 !big));
  assert_equal ~msg:"big find 50" "2500" (string_of_int (hm_find_exn 50 !big));
  assert_equal ~msg:"big find 99" "9801" (string_of_int (hm_find_exn 99 !big));
  assert_true ~msg:"big not mem 100" (not (hm_mem 100 !big));

  (* -- iter -- *)
  let count = ref 0 in
  hm_iter (fun _k _v -> incr count) m6;
  assert_equal ~msg:"iter count" "3" (string_of_int !count);

  (* -- empty operations -- *)
  assert_true ~msg:"empty fold" (hm_fold (fun _ _ _ -> false) true (hm_create ()));
  assert_true ~msg:"empty for_all" (hm_for_all (fun _ _ -> false) (hm_create ()));
  assert_true ~msg:"empty not exists" (not (hm_exists (fun _ _ -> true) (hm_create ())));
  assert_true ~msg:"empty filter" (hm_is_empty (hm_filter (fun _ _ -> true) (hm_create ())));
  assert_true ~msg:"empty keys" (hm_keys (hm_create ()) = []);
  assert_true ~msg:"empty values" (hm_values (hm_create ()) = []);
  assert_true ~msg:"empty equal" (hm_equal (=) (hm_create ()) (hm_create ()));

  (* -- of_list duplicate keys: last wins -- *)
  let mdup = hm_of_list [("a", 1); ("a", 2); ("a", 3)] in
  assert_equal ~msg:"of_list last wins" "3" (string_of_int (hm_find_exn "a" mdup));
  assert_equal ~msg:"of_list dup size" "1" (string_of_int (hm_size mdup));

  (* -- remove all entries -- *)
  let m_all = hm_of_list [("a", 1); ("b", 2)] in
  let m_none = hm_remove "b" (hm_remove "a" m_all) in
  assert_true ~msg:"remove all empty" (hm_is_empty m_none);

  (* -- persistence chain -- *)
  let p0 = hm_insert "x" 1 hm_empty in
  let p1 = hm_insert "y" 2 p0 in
  let p2 = hm_remove "x" p1 in
  assert_true ~msg:"p0 has x" (hm_mem "x" p0);
  assert_true ~msg:"p0 no y" (not (hm_mem "y" p0));
  assert_true ~msg:"p1 has both" (hm_mem "x" p1 && hm_mem "y" p1);
  assert_true ~msg:"p2 no x" (not (hm_mem "x" p2));
  assert_true ~msg:"p2 has y" (hm_mem "y" p2);

  (* -- custom capacity -- *)
  let mc = hm_create ~capacity:1 () in
  let mc = hm_insert "a" 1 (hm_insert "b" 2 mc) in
  assert_equal ~msg:"tiny cap size" "2" (string_of_int (hm_size mc));
  assert_equal ~msg:"tiny cap find" "1" (string_of_int (hm_find_exn "a" mc));
)

(* ===== Bloom Filter (from bloom_filter.ml) ===== *)

(* -- Bit manipulation helpers -- *)

let bf_get_bit bits i =
  let byte_idx = i / 8 in
  let bit_idx = i mod 8 in
  Char.code (Bytes.get bits byte_idx) land (1 lsl bit_idx) <> 0

let bf_set_bit bits i =
  let byte_idx = i / 8 in
  let bit_idx = i mod 8 in
  let old = Char.code (Bytes.get bits byte_idx) in
  Bytes.set bits byte_idx (Char.chr (old lor (1 lsl bit_idx)))

(* -- Hash functions (double hashing) -- *)

let bf_hash1 x = Hashtbl.hash x
let bf_hash2 x = Hashtbl.hash (x, 0x9e3779b9)

let bf_hash_i m h1 h2 i =
  ((h1 + i * h2) mod m + m) mod m

(* -- Bloom filter type -- *)

type bloom_filter = {
  bf_bits : bytes;
  bf_m    : int;
  bf_k    : int;
  bf_n    : int;
}

let bf_create ?(m = 1024) ?(k = 7) () =
  let m = max 8 m in
  let k = max 1 k in
  let byte_count = (m + 7) / 8 in
  { bf_bits = Bytes.make byte_count '\000'; bf_m = m; bf_k = k; bf_n = 0 }

let bf_create_optimal ~expected_elements ~fp_rate =
  let n_f = float_of_int (max 1 expected_elements) in
  let p = max 0.0001 (min 0.5 fp_rate) in
  let m_f = -.(n_f *. log p) /. (log 2.0 ** 2.0) in
  let m = max 8 (int_of_float (ceil m_f)) in
  let k_f = (float_of_int m /. n_f) *. log 2.0 in
  let k = max 1 (int_of_float (Float.round k_f)) in
  bf_create ~m ~k ()

let bf_add x bf =
  let new_bits = Bytes.copy bf.bf_bits in
  let h1 = bf_hash1 x in
  let h2 = bf_hash2 x in
  for i = 0 to bf.bf_k - 1 do
    let idx = bf_hash_i bf.bf_m h1 h2 i in
    bf_set_bit new_bits idx
  done;
  { bf with bf_bits = new_bits; bf_n = bf.bf_n + 1 }

let bf_mem x bf =
  let h1 = bf_hash1 x in
  let h2 = bf_hash2 x in
  let rec check i =
    if i >= bf.bf_k then true
    else
      let idx = bf_hash_i bf.bf_m h1 h2 i in
      if bf_get_bit bf.bf_bits idx then check (i + 1)
      else false
  in
  check 0

let bf_count bf = bf.bf_n
let bf_size bf = bf.bf_m
let bf_num_hashes bf = bf.bf_k
let bf_is_empty bf = bf.bf_n = 0

let bf_popcount bf =
  let c = ref 0 in
  for i = 0 to bf.bf_m - 1 do
    if bf_get_bit bf.bf_bits i then incr c
  done;
  !c

let bf_saturation bf =
  float_of_int (bf_popcount bf) /. float_of_int bf.bf_m

let bf_false_positive_rate bf =
  if bf.bf_n = 0 then 0.0
  else
    let m_f = float_of_int bf.bf_m in
    let k_f = float_of_int bf.bf_k in
    let n_f = float_of_int bf.bf_n in
    (1.0 -. exp (-. k_f *. n_f /. m_f)) ** k_f

let bf_union bf1 bf2 =
  if bf1.bf_m <> bf2.bf_m || bf1.bf_k <> bf2.bf_k then
    invalid_arg "BloomFilter.union: incompatible filters"
  else begin
    let new_bits = Bytes.copy bf1.bf_bits in
    let byte_count = (bf1.bf_m + 7) / 8 in
    for i = 0 to byte_count - 1 do
      let b1 = Char.code (Bytes.get bf1.bf_bits i) in
      let b2 = Char.code (Bytes.get bf2.bf_bits i) in
      Bytes.set new_bits i (Char.chr (b1 lor b2))
    done;
    { bf_bits = new_bits; bf_m = bf1.bf_m; bf_k = bf1.bf_k;
      bf_n = bf1.bf_n + bf2.bf_n }
  end

let bf_of_list ?(m = 1024) ?(k = 7) lst =
  List.fold_left (fun bf x -> bf_add x bf) (bf_create ~m ~k ()) lst

let bf_mem_all lst bf =
  List.for_all (fun x -> bf_mem x bf) lst

let bf_mem_any lst bf =
  List.exists (fun x -> bf_mem x bf) lst

let bf_clear bf = bf_create ~m:bf.bf_m ~k:bf.bf_k ()

let bf_copy bf = { bf with bf_bits = Bytes.copy bf.bf_bits }

let bf_to_string bf =
  Printf.sprintf "BloomFilter(m=%d, k=%d, n=%d, sat=%.2f%%)"
    bf.bf_m bf.bf_k bf.bf_n (bf_saturation bf *. 100.0)

(* ===== Bloom Filter Tests ===== *)

let test_bloom_filter () = suite "Bloom Filter" (fun () ->
  (* -- create -- *)
  let bf0 = bf_create () in
  assert_true ~msg:"empty is empty" (bf_is_empty bf0);
  assert_equal ~msg:"empty count" "0" (string_of_int (bf_count bf0));
  assert_equal ~msg:"default size" "1024" (string_of_int (bf_size bf0));
  assert_equal ~msg:"default hashes" "7" (string_of_int (bf_num_hashes bf0));

  (* -- add and mem -- *)
  let bf1 = bf_add "hello" bf0 in
  assert_true ~msg:"mem hello" (bf_mem "hello" bf1);
  assert_equal ~msg:"count 1" "1" (string_of_int (bf_count bf1));
  assert_true ~msg:"not empty" (not (bf_is_empty bf1));

  (* -- no false negatives -- *)
  let bf2 = bf_add "world" (bf_add "foo" (bf_add "bar" bf1)) in
  assert_true ~msg:"mem hello still" (bf_mem "hello" bf2);
  assert_true ~msg:"mem world" (bf_mem "world" bf2);
  assert_true ~msg:"mem foo" (bf_mem "foo" bf2);
  assert_true ~msg:"mem bar" (bf_mem "bar" bf2);
  assert_equal ~msg:"count 4" "4" (string_of_int (bf_count bf2));

  (* -- original unchanged (immutability) -- *)
  assert_true ~msg:"bf0 still empty" (bf_is_empty bf0);
  assert_true ~msg:"bf1 still 1" (bf_count bf1 = 1);

  (* -- probably not in set (low FP for large filter) -- *)
  let bf_large = bf_create ~m:8192 ~k:7 () in
  let bf_large = bf_add "alpha" bf_large in
  (* Test several strings that were NOT added *)
  let not_added = ["zzz_unique_1"; "zzz_unique_2"; "zzz_unique_3";
                    "never_added_x"; "never_added_y"] in
  let fp_count = List.length (List.filter (fun s -> bf_mem s bf_large) not_added) in
  assert_true ~msg:"low FP rate" (fp_count <= 2);  (* at most 2/5 false positives *)

  (* -- of_list -- *)
  let bf3 = bf_of_list ["a"; "b"; "c"; "d"; "e"] in
  assert_equal ~msg:"of_list count" "5" (string_of_int (bf_count bf3));
  assert_true ~msg:"of_list mem a" (bf_mem "a" bf3);
  assert_true ~msg:"of_list mem e" (bf_mem "e" bf3);

  (* -- mem_all -- *)
  assert_true ~msg:"mem_all present" (bf_mem_all ["a"; "b"; "c"] bf3);
  (* mem_all with a non-member may or may not return false (probabilistic) *)

  (* -- mem_any -- *)
  assert_true ~msg:"mem_any present" (bf_mem_any ["a"; "zzz_random"] bf3);

  (* -- mem_any all missing -- *)
  let bf_tiny = bf_create ~m:8192 ~k:7 () in
  let bf_tiny = bf_add "only_this" bf_tiny in
  (* With a large filter and few elements, random strings should mostly miss *)

  (* -- popcount -- *)
  assert_equal ~msg:"empty popcount" "0" (string_of_int (bf_popcount bf0));
  let pc1 = bf_popcount bf1 in
  assert_true ~msg:"popcount after add > 0" (pc1 > 0);
  assert_true ~msg:"popcount <= k" (pc1 <= bf_num_hashes bf1);

  (* -- saturation -- *)
  let sat0 = bf_saturation bf0 in
  assert_true ~msg:"empty saturation 0" (sat0 = 0.0);
  let sat1 = bf_saturation bf1 in
  assert_true ~msg:"some saturation > 0" (sat1 > 0.0);
  assert_true ~msg:"saturation <= 1" (sat1 <= 1.0);

  (* -- false_positive_rate -- *)
  let fpr0 = bf_false_positive_rate bf0 in
  assert_true ~msg:"empty FPR 0" (fpr0 = 0.0);
  let fpr1 = bf_false_positive_rate bf1 in
  assert_true ~msg:"FPR > 0 after add" (fpr1 > 0.0);
  assert_true ~msg:"FPR < 1" (fpr1 < 1.0);

  (* -- union -- *)
  let bfA = bf_of_list ~m:512 ~k:5 ["x"; "y"] in
  let bfB = bf_of_list ~m:512 ~k:5 ["z"; "w"] in
  let bfU = bf_union bfA bfB in
  assert_true ~msg:"union mem x" (bf_mem "x" bfU);
  assert_true ~msg:"union mem y" (bf_mem "y" bfU);
  assert_true ~msg:"union mem z" (bf_mem "z" bfU);
  assert_true ~msg:"union mem w" (bf_mem "w" bfU);
  assert_equal ~msg:"union count" "4" (string_of_int (bf_count bfU));

  (* -- union incompatible raises -- *)
  let bfX = bf_create ~m:100 ~k:3 () in
  let bfY = bf_create ~m:200 ~k:3 () in
  assert_raises ~msg:"union incompatible" (fun () -> bf_union bfX bfY);

  (* -- clear -- *)
  let bf4 = bf_of_list ["p"; "q"; "r"] in
  let bf4c = bf_clear bf4 in
  assert_true ~msg:"cleared empty" (bf_is_empty bf4c);
  assert_equal ~msg:"cleared size same" (string_of_int (bf_size bf4))
    (string_of_int (bf_size bf4c));
  assert_equal ~msg:"cleared k same" (string_of_int (bf_num_hashes bf4))
    (string_of_int (bf_num_hashes bf4c));
  (* original unchanged *)
  assert_equal ~msg:"original not cleared" "3" (string_of_int (bf_count bf4));

  (* -- copy -- *)
  let bf5 = bf_of_list ["m"; "n"] in
  let bf5c = bf_copy bf5 in
  assert_true ~msg:"copy mem m" (bf_mem "m" bf5c);
  assert_true ~msg:"copy mem n" (bf_mem "n" bf5c);
  assert_equal ~msg:"copy count" "2" (string_of_int (bf_count bf5c));

  (* -- to_string -- *)
  let s = bf_to_string bf2 in
  assert_true ~msg:"to_string has m" (String.length s > 0);

  (* -- create_optimal -- *)
  let bf_opt = bf_create_optimal ~expected_elements:1000 ~fp_rate:0.01 in
  assert_true ~msg:"optimal m > 0" (bf_size bf_opt > 0);
  assert_true ~msg:"optimal k > 0" (bf_num_hashes bf_opt > 0);
  assert_true ~msg:"optimal m reasonable" (bf_size bf_opt > 1000);
  assert_true ~msg:"optimal k reasonable" (bf_num_hashes bf_opt >= 5 && bf_num_hashes bf_opt <= 10);

  (* -- custom small capacity -- *)
  let bf_small = bf_create ~m:8 ~k:2 () in
  let bf_small = bf_add "x" bf_small in
  assert_true ~msg:"tiny mem x" (bf_mem "x" bf_small);
  assert_equal ~msg:"tiny size" "8" (string_of_int (bf_size bf_small));

  (* -- integer keys -- *)
  let bf_int = bf_of_list [1; 2; 3; 4; 5] in
  assert_true ~msg:"int mem 3" (bf_mem 3 bf_int);
  assert_true ~msg:"int mem 5" (bf_mem 5 bf_int);
  assert_equal ~msg:"int count" "5" (string_of_int (bf_count bf_int));

  (* -- many insertions -- *)
  let bf_big = ref (bf_create ~m:4096 ~k:7 ()) in
  for i = 0 to 99 do
    bf_big := bf_add i !bf_big
  done;
  assert_equal ~msg:"big count" "100" (string_of_int (bf_count !bf_big));
  (* All inserted items should be present (no false negatives) *)
  let all_present = ref true in
  for i = 0 to 99 do
    if not (bf_mem i !bf_big) then all_present := false
  done;
  assert_true ~msg:"big no false negatives" !all_present;

  (* -- saturation grows with insertions -- *)
  let sat_big = bf_saturation !bf_big in
  assert_true ~msg:"big saturation > empty" (sat_big > 0.0);

  (* -- empty mem_all is true (vacuous) -- *)
  assert_true ~msg:"empty mem_all" (bf_mem_all [] bf1);

  (* -- empty mem_any is false -- *)
  assert_true ~msg:"empty mem_any" (not (bf_mem_any [] bf1));

  (* -- FPR increases with more elements -- *)
  let fpr_few = bf_false_positive_rate (bf_of_list ~m:256 ~k:5 [1; 2; 3]) in
  let fpr_many = bf_false_positive_rate (bf_of_list ~m:256 ~k:5
    (List.init 100 (fun i -> i))) in
  assert_true ~msg:"FPR increases" (fpr_many > fpr_few);
)

(* ===== LRU Cache helpers ===== *)

(* Inline module to keep test_all self-contained *)
module LRU = struct
  type ('k, 'v) t = {
    entries  : ('k * 'v) list;
    index    : ('k, 'v) Hashtbl.t;
    capacity : int;
    hits     : int;
    misses   : int;
  }
  let create capacity =
    if capacity < 1 then invalid_arg "LRU: capacity must be >= 1"
    else { entries = []; index = Hashtbl.create capacity;
           capacity; hits = 0; misses = 0 }
  let clear c =
    { entries = []; index = Hashtbl.create c.capacity;
      capacity = c.capacity; hits = 0; misses = 0 }
  let remove_from_list k entries =
    List.filter (fun (k', _) -> k' <> k) entries
  let trim cap entries =
    if List.length entries <= cap then (entries, [])
    else let rec take acc n = function
      | [] -> (List.rev acc, []) | _ when n >= cap -> (List.rev acc, [])
      | x :: rest -> take (x :: acc) (n + 1) rest
    in take [] 0 entries
  let rebuild entries cap =
    let tbl = Hashtbl.create cap in
    List.iter (fun (k, v) -> Hashtbl.replace tbl k v) entries; tbl
  let put k v c =
    let cleaned = remove_from_list k c.entries in
    let updated = (k, v) :: cleaned in
    let (kept, _) = trim c.capacity updated in
    let idx = rebuild kept c.capacity in
    { entries = kept; index = idx; capacity = c.capacity;
      hits = c.hits; misses = c.misses }
  let get k c =
    match Hashtbl.find_opt c.index k with
    | None -> (None, { c with misses = c.misses + 1 })
    | Some v ->
      let entries = (k, v) :: (remove_from_list k c.entries) in
      let idx = rebuild entries c.capacity in
      (Some v, { entries; index = idx; capacity = c.capacity;
                 hits = c.hits + 1; misses = c.misses })
  let peek k c = Hashtbl.find_opt c.index k
  let mem k c = Hashtbl.mem c.index k
  let remove k c =
    if not (Hashtbl.mem c.index k) then c
    else let entries = remove_from_list k c.entries in
      let idx = rebuild entries c.capacity in
      { entries; index = idx; capacity = c.capacity;
        hits = c.hits; misses = c.misses }
  let evict c = match List.rev c.entries with
    | [] -> (None, c)
    | (k, v) :: _ ->
      let entries = remove_from_list k c.entries in
      let idx = rebuild entries c.capacity in
      (Some (k, v), { entries; index = idx; capacity = c.capacity;
                       hits = c.hits; misses = c.misses })
  let size c = List.length c.entries
  let capacity c = c.capacity
  let is_empty c = c.entries = []
  let is_full c = List.length c.entries >= c.capacity
  let to_list c = c.entries
  let keys c = List.map fst c.entries
  let values c = List.map snd c.entries
  let stats c =
    let total = c.hits + c.misses in
    let rate = if total = 0 then 0.0
      else float_of_int c.hits /. float_of_int total in
    (c.hits, c.misses, rate)
  let resize new_cap c =
    if new_cap < 1 then invalid_arg "LRU: capacity must be >= 1"
    else let (kept, _) = trim new_cap c.entries in
      let idx = rebuild kept new_cap in
      { entries = kept; index = idx; capacity = new_cap;
        hits = c.hits; misses = c.misses }
  let of_list cap pairs =
    if cap < 1 then invalid_arg "LRU: capacity must be >= 1"
    else let c = create cap in
      List.fold_left (fun c (k, v) -> put k v c) c (List.rev pairs)
  let fold f init c = List.fold_left (fun acc (k, v) -> f acc k v) init c.entries
  let iter f c = List.iter (fun (k, v) -> f k v) c.entries
  let filter pred c =
    let entries = List.filter (fun (k, v) -> pred k v) c.entries in
    let idx = rebuild entries c.capacity in
    { entries; index = idx; capacity = c.capacity;
      hits = c.hits; misses = c.misses }
  let map_values f c =
    let entries = List.map (fun (k, v) -> (k, f v)) c.entries in
    let idx = rebuild entries c.capacity in
    { entries; index = idx; capacity = c.capacity;
      hits = c.hits; misses = c.misses }
end

let test_lru_cache () = suite "LRU Cache" (fun () ->
  (* create *)
  let c = LRU.create 5 in
  assert_true ~msg:"create: empty" (LRU.is_empty c);
  assert_equal ~msg:"create: capacity" "5" (string_of_int (LRU.capacity c));
  assert_equal ~msg:"create: size 0" "0" (string_of_int (LRU.size c));
  assert_raises ~msg:"create: 0 raises" (fun () -> LRU.create 0);
  assert_raises ~msg:"create: neg raises" (fun () -> LRU.create (-1));

  (* put *)
  let c = LRU.create 3 in
  let c = LRU.put "a" 1 c in
  assert_equal ~msg:"put: size 1" "1" (string_of_int (LRU.size c));
  assert_true ~msg:"put: mem" (LRU.mem "a" c);
  let c = LRU.put "b" 2 c in
  let c = LRU.put "c" 3 c in
  assert_equal ~msg:"put 3: size" "3" (string_of_int (LRU.size c));

  (* eviction on overflow *)
  let c = LRU.create 2 in
  let c = LRU.put "a" 1 c in
  let c = LRU.put "b" 2 c in
  let c = LRU.put "c" 3 c in
  assert_true ~msg:"evict: a gone" (not (LRU.mem "a" c));
  assert_true ~msg:"evict: b present" (LRU.mem "b" c);
  assert_true ~msg:"evict: c present" (LRU.mem "c" c);

  (* put updates value *)
  let c = LRU.create 3 in
  let c = LRU.put "a" 1 c in
  let c = LRU.put "a" 99 c in
  assert_equal ~msg:"update: size 1" "1" (string_of_int (LRU.size c));
  assert_equal ~msg:"update: val" "99"
    (string_of_int (match LRU.peek "a" c with Some v -> v | None -> -1));

  (* put promotes *)
  let c = LRU.create 2 in
  let c = LRU.put "a" 1 c in
  let c = LRU.put "b" 2 c in
  let c = LRU.put "a" 10 c in
  let c = LRU.put "c" 3 c in
  assert_true ~msg:"promote: a survives" (LRU.mem "a" c);
  assert_true ~msg:"promote: b evicted" (not (LRU.mem "b" c));

  (* get *)
  let c = LRU.create 3 in
  let c = LRU.put "x" 42 c in
  let (v, _) = LRU.get "x" c in
  assert_equal ~msg:"get: found" "42"
    (string_of_int (match v with Some x -> x | None -> -1));
  let (v, _) = LRU.get "missing" c in
  assert_true ~msg:"get: miss" (v = None);

  (* get promotes *)
  let c = LRU.create 2 in
  let c = LRU.put "a" 1 c in
  let c = LRU.put "b" 2 c in
  let (_, c) = LRU.get "a" c in
  let c = LRU.put "c" 3 c in
  assert_true ~msg:"get promote: a survives" (LRU.mem "a" c);
  assert_true ~msg:"get promote: b evicted" (not (LRU.mem "b" c));

  (* stats *)
  let c = LRU.create 3 in
  let c = LRU.put "a" 1 c in
  let (_, c) = LRU.get "a" c in
  let (_, c) = LRU.get "miss" c in
  let (h, m, _) = LRU.stats c in
  assert_equal ~msg:"stats: hits" "1" (string_of_int h);
  assert_equal ~msg:"stats: misses" "1" (string_of_int m);

  (* peek does NOT promote *)
  let c = LRU.create 2 in
  let c = LRU.put "a" 1 c in
  let c = LRU.put "b" 2 c in
  let _ = LRU.peek "a" c in
  let c = LRU.put "c" 3 c in
  assert_true ~msg:"peek no promote: a evicted" (not (LRU.mem "a" c));

  (* remove *)
  let c = LRU.create 3 in
  let c = LRU.put "a" 1 c in
  let c = LRU.put "b" 2 c in
  let c = LRU.remove "a" c in
  assert_equal ~msg:"remove: size" "1" (string_of_int (LRU.size c));
  assert_true ~msg:"remove: a gone" (not (LRU.mem "a" c));
  let c = LRU.remove "nonexistent" c in
  assert_equal ~msg:"remove missing: ok" "1" (string_of_int (LRU.size c));

  (* evict *)
  let c = LRU.create 3 in
  let c = LRU.put "a" 1 c in
  let c = LRU.put "b" 2 c in
  let (ev, c) = LRU.evict c in
  assert_equal ~msg:"evict: got a" "a"
    (match ev with Some (k, _) -> k | None -> "none");
  assert_equal ~msg:"evict: size 1" "1" (string_of_int (LRU.size c));
  let c = LRU.create 3 in
  let (ev, _) = LRU.evict c in
  assert_true ~msg:"evict empty: None" (ev = None);

  (* is_full *)
  let c = LRU.create 2 in
  let c = LRU.put "a" 1 c in
  assert_true ~msg:"not full" (not (LRU.is_full c));
  let c = LRU.put "b" 2 c in
  assert_true ~msg:"full" (LRU.is_full c);

  (* to_list order *)
  let c = LRU.create 3 in
  let c = LRU.put "a" 1 c in
  let c = LRU.put "b" 2 c in
  let c = LRU.put "c" 3 c in
  let lst = LRU.to_list c in
  assert_equal ~msg:"to_list: first" "c" (fst (List.nth lst 0));
  assert_equal ~msg:"to_list: last" "a" (fst (List.nth lst 2));

  (* keys / values *)
  let c = LRU.create 3 in
  let c = LRU.put "a" 1 c in
  let c = LRU.put "b" 2 c in
  assert_equal ~msg:"keys: 2" "2" (string_of_int (List.length (LRU.keys c)));
  assert_equal ~msg:"values: 2" "2" (string_of_int (List.length (LRU.values c)));

  (* clear *)
  let c = LRU.create 3 in
  let c = LRU.put "a" 1 c in
  let c = LRU.clear c in
  assert_true ~msg:"clear: empty" (LRU.is_empty c);
  assert_equal ~msg:"clear: cap" "3" (string_of_int (LRU.capacity c));

  (* resize down *)
  let c = LRU.create 5 in
  let c = LRU.put "a" 1 c in
  let c = LRU.put "b" 2 c in
  let c = LRU.put "c" 3 c in
  let c = LRU.resize 2 c in
  assert_equal ~msg:"resize: cap" "2" (string_of_int (LRU.capacity c));
  assert_equal ~msg:"resize: size" "2" (string_of_int (LRU.size c));
  assert_true ~msg:"resize: c kept" (LRU.mem "c" c);
  assert_true ~msg:"resize: a evicted" (not (LRU.mem "a" c));
  assert_raises ~msg:"resize: 0 raises" (fun () -> LRU.resize 0 (LRU.create 3));

  (* of_list *)
  let c = LRU.of_list 3 [("a", 1); ("b", 2); ("c", 3)] in
  assert_equal ~msg:"of_list: size" "3" (string_of_int (LRU.size c));
  let lst = LRU.to_list c in
  assert_equal ~msg:"of_list: first is a" "a" (fst (List.hd lst));
  assert_raises ~msg:"of_list: 0 raises" (fun () -> LRU.of_list 0 [("a", 1)]);

  (* fold *)
  let c = LRU.create 3 in
  let c = LRU.put "a" 1 c in
  let c = LRU.put "b" 2 c in
  let c = LRU.put "c" 3 c in
  let sum = LRU.fold (fun acc _k v -> acc + v) 0 c in
  assert_equal ~msg:"fold: sum" "6" (string_of_int sum);

  (* iter *)
  let count = ref 0 in
  LRU.iter (fun _k _v -> incr count) c;
  assert_equal ~msg:"iter: 3" "3" (string_of_int !count);

  (* filter *)
  let c = LRU.create 5 in
  let c = LRU.put "a" 1 c in
  let c = LRU.put "b" 2 c in
  let c = LRU.put "c" 3 c in
  let filtered = LRU.filter (fun _k v -> v > 1) c in
  assert_equal ~msg:"filter: size" "2" (string_of_int (LRU.size filtered));
  assert_true ~msg:"filter: a gone" (not (LRU.mem "a" filtered));

  (* map_values *)
  let c = LRU.create 3 in
  let c = LRU.put "a" 1 c in
  let c = LRU.put "b" 2 c in
  let doubled = LRU.map_values (fun v -> v * 2) c in
  assert_equal ~msg:"map: a=2" "2"
    (string_of_int (match LRU.peek "a" doubled with Some v -> v | None -> -1));
  assert_equal ~msg:"map: b=4" "4"
    (string_of_int (match LRU.peek "b" doubled with Some v -> v | None -> -1));

  (* stress *)
  let c = LRU.create 100 in
  let c = ref c in
  for i = 0 to 999 do
    c := LRU.put (string_of_int i) i !c
  done;
  assert_equal ~msg:"stress: size" "100" (string_of_int (LRU.size !c));
  assert_true ~msg:"stress: 999 present" (LRU.mem "999" !c);
  assert_true ~msg:"stress: 899 gone" (not (LRU.mem "899" !c));
)

(* ===== Skip List helpers ===== *)

(* Inline module to keep test_all self-contained *)
module SL = struct
  let max_level = 32

  type 'a node = {
    key     : 'a;
    forward : 'a node option array;
  }

  type 'a t = {
    header    : 'a node;
    mutable level : int;
    mutable length : int;
    compare   : 'a -> 'a -> int;
  }

  let make_node key lvl =
    { key; forward = Array.make (lvl + 1) None }

  let random_level () =
    let rec go lvl =
      if lvl >= max_level - 1 then lvl
      else if Random.bool () then go (lvl + 1)
      else lvl
    in
    go 0

  let create ?(compare = Stdlib.compare) () =
    let header = { key = Obj.magic 0; forward = Array.make max_level None } in
    { header; level = 0; length = 0; compare }

  let size sl = sl.length
  let is_empty sl = sl.length = 0
  let height sl = if sl.length = 0 then 0 else sl.level + 1

  let mem key sl =
    let x = ref sl.header in
    for i = sl.level downto 0 do
      let continue_ = ref true in
      while !continue_ do
        match !x.forward.(i) with
        | Some next when sl.compare next.key key < 0 -> x := next
        | _ -> continue_ := false
      done
    done;
    match !x.forward.(0) with
    | Some n -> sl.compare n.key key = 0
    | None   -> false

  let find key sl =
    let x = ref sl.header in
    for i = sl.level downto 0 do
      let continue_ = ref true in
      while !continue_ do
        match !x.forward.(i) with
        | Some next when sl.compare next.key key < 0 -> x := next
        | _ -> continue_ := false
      done
    done;
    match !x.forward.(0) with
    | Some n when sl.compare n.key key = 0 -> Some n.key
    | _ -> None

  let insert key sl =
    let update = Array.make max_level sl.header in
    let x = ref sl.header in
    for i = sl.level downto 0 do
      let continue_ = ref true in
      while !continue_ do
        match !x.forward.(i) with
        | Some next when sl.compare next.key key < 0 -> x := next
        | _ -> continue_ := false
      done;
      update.(i) <- !x
    done;
    let is_dup = match !x.forward.(0) with
      | Some n -> sl.compare n.key key = 0
      | None   -> false
    in
    if not is_dup then begin
      let lvl = random_level () in
      if lvl > sl.level then begin
        for i = sl.level + 1 to lvl do
          update.(i) <- sl.header
        done;
        sl.level <- lvl
      end;
      let new_node = make_node key lvl in
      for i = 0 to lvl do
        new_node.forward.(i) <- update.(i).forward.(i);
        update.(i).forward.(i) <- Some new_node
      done;
      sl.length <- sl.length + 1
    end

  let remove key sl =
    let update = Array.make max_level sl.header in
    let x = ref sl.header in
    for i = sl.level downto 0 do
      let continue_ = ref true in
      while !continue_ do
        match !x.forward.(i) with
        | Some next when sl.compare next.key key < 0 -> x := next
        | _ -> continue_ := false
      done;
      update.(i) <- !x
    done;
    match !x.forward.(0) with
    | Some n when sl.compare n.key key = 0 ->
      for i = 0 to sl.level do
        match update.(i).forward.(i) with
        | Some fwd when fwd == n ->
          update.(i).forward.(i) <- n.forward.(i)
        | _ -> ()
      done;
      while sl.level > 0 && sl.header.forward.(sl.level) = None do
        sl.level <- sl.level - 1
      done;
      sl.length <- sl.length - 1;
      true
    | _ -> false

  let to_list sl =
    let acc = ref [] in
    let x = ref sl.header.forward.(0) in
    while !x <> None do
      (match !x with
       | Some n -> acc := n.key :: !acc; x := n.forward.(0)
       | None -> ())
    done;
    List.rev !acc

  let iter f sl =
    let x = ref sl.header.forward.(0) in
    while !x <> None do
      (match !x with
       | Some n -> f n.key; x := n.forward.(0)
       | None -> ())
    done

  let fold f acc sl =
    let result = ref acc in
    let x = ref sl.header.forward.(0) in
    while !x <> None do
      (match !x with
       | Some n -> result := f !result n.key; x := n.forward.(0)
       | None -> ())
    done;
    !result

  let min_elt sl =
    match sl.header.forward.(0) with
    | Some n -> Some n.key
    | None   -> None

  let max_elt sl =
    if sl.length = 0 then None
    else begin
      let x = ref sl.header in
      for i = sl.level downto 0 do
        let continue_ = ref true in
        while !continue_ do
          match !x.forward.(i) with
          | Some next -> x := next
          | None -> continue_ := false
        done
      done;
      Some !x.key
    end

  let range_query ~lo ~hi sl =
    if sl.compare lo hi > 0 then []
    else begin
      let x = ref sl.header in
      for i = sl.level downto 0 do
        let continue_ = ref true in
        while !continue_ do
          match !x.forward.(i) with
          | Some next when sl.compare next.key lo < 0 -> x := next
          | _ -> continue_ := false
        done
      done;
      let acc = ref [] in
      let cur = ref !x.forward.(0) in
      let stop = ref false in
      while not !stop do
        match !cur with
        | Some n when sl.compare n.key hi <= 0 ->
          if sl.compare n.key lo >= 0 then
            acc := n.key :: !acc;
          cur := n.forward.(0)
        | _ -> stop := true
      done;
      List.rev !acc
    end

  let floor key sl =
    let x = ref sl.header in
    for i = sl.level downto 0 do
      let continue_ = ref true in
      while !continue_ do
        match !x.forward.(i) with
        | Some next when sl.compare next.key key <= 0 -> x := next
        | _ -> continue_ := false
      done
    done;
    if !x == sl.header then None
    else Some !x.key

  let ceil key sl =
    let x = ref sl.header in
    for i = sl.level downto 0 do
      let continue_ = ref true in
      while !continue_ do
        match !x.forward.(i) with
        | Some next when sl.compare next.key key < 0 -> x := next
        | _ -> continue_ := false
      done
    done;
    match !x.forward.(0) with
    | Some n when sl.compare n.key key >= 0 -> Some n.key
    | _ -> None

  let of_list ?(compare = Stdlib.compare) lst =
    let sl = create ~compare () in
    List.iter (fun k -> insert k sl) lst;
    sl
end

(* ===== Skip List tests ===== *)

let test_skip_list () =
  current_suite := "SkipList";
  Printf.printf "Testing SkipList...\n";

  (* -- Empty skip list -- *)
  let sl = SL.create () in
  assert_true ~msg:"empty: is_empty" (SL.is_empty sl);
  assert_equal ~msg:"empty: size" "0" (string_of_int (SL.size sl));
  assert_equal ~msg:"empty: height" "0" (string_of_int (SL.height sl));
  assert_true ~msg:"empty: to_list" (SL.to_list sl = []);
  assert_true ~msg:"empty: min_elt" (SL.min_elt sl = None);
  assert_true ~msg:"empty: max_elt" (SL.max_elt sl = None);
  assert_true ~msg:"empty: mem 0" (not (SL.mem 0 sl));
  assert_true ~msg:"empty: find 0" (SL.find 0 sl = None);
  assert_true ~msg:"empty: floor 5" (SL.floor 5 sl = None);
  assert_true ~msg:"empty: ceil 5" (SL.ceil 5 sl = None);
  assert_true ~msg:"empty: range" (SL.range_query ~lo:0 ~hi:10 sl = []);
  assert_true ~msg:"empty: remove" (not (SL.remove 1 sl));

  (* -- Single element -- *)
  SL.insert 42 sl;
  assert_true ~msg:"single: not empty" (not (SL.is_empty sl));
  assert_equal ~msg:"single: size" "1" (string_of_int (SL.size sl));
  assert_true ~msg:"single: height >= 1" (SL.height sl >= 1);
  assert_true ~msg:"single: mem 42" (SL.mem 42 sl);
  assert_true ~msg:"single: find 42" (SL.find 42 sl = Some 42);
  assert_true ~msg:"single: not mem 99" (not (SL.mem 99 sl));
  assert_true ~msg:"single: to_list" (SL.to_list sl = [42]);
  assert_true ~msg:"single: min_elt" (SL.min_elt sl = Some 42);
  assert_true ~msg:"single: max_elt" (SL.max_elt sl = Some 42);

  (* -- Duplicate insert -- *)
  SL.insert 42 sl;
  assert_equal ~msg:"dup: size still 1" "1" (string_of_int (SL.size sl));
  assert_true ~msg:"dup: to_list" (SL.to_list sl = [42]);

  (* -- Multiple elements, sorted order -- *)
  SL.insert 10 sl;
  SL.insert 30 sl;
  SL.insert 20 sl;
  SL.insert 50 sl;
  SL.insert 40 sl;
  assert_equal ~msg:"multi: size" "6" (string_of_int (SL.size sl));
  assert_true ~msg:"multi: sorted"
    (SL.to_list sl = [10; 20; 30; 40; 42; 50]);
  assert_true ~msg:"multi: min" (SL.min_elt sl = Some 10);
  assert_true ~msg:"multi: max" (SL.max_elt sl = Some 50);
  assert_true ~msg:"multi: mem 30" (SL.mem 30 sl);
  assert_true ~msg:"multi: mem 42" (SL.mem 42 sl);
  assert_true ~msg:"multi: not mem 25" (not (SL.mem 25 sl));

  (* -- Remove -- *)
  assert_true ~msg:"remove 30: found" (SL.remove 30 sl);
  assert_equal ~msg:"remove 30: size" "5" (string_of_int (SL.size sl));
  assert_true ~msg:"remove 30: not mem" (not (SL.mem 30 sl));
  assert_true ~msg:"remove 30: list"
    (SL.to_list sl = [10; 20; 40; 42; 50]);
  assert_true ~msg:"remove missing" (not (SL.remove 99 sl));
  assert_equal ~msg:"remove missing: size" "5" (string_of_int (SL.size sl));

  (* Remove head element *)
  assert_true ~msg:"remove head" (SL.remove 10 sl);
  assert_true ~msg:"remove head: min" (SL.min_elt sl = Some 20);
  assert_true ~msg:"remove head: list"
    (SL.to_list sl = [20; 40; 42; 50]);

  (* Remove tail element *)
  assert_true ~msg:"remove tail" (SL.remove 50 sl);
  assert_true ~msg:"remove tail: max" (SL.max_elt sl = Some 42);
  assert_true ~msg:"remove tail: list"
    (SL.to_list sl = [20; 40; 42]);

  (* Remove all *)
  assert_true ~msg:"remove all 1" (SL.remove 20 sl);
  assert_true ~msg:"remove all 2" (SL.remove 40 sl);
  assert_true ~msg:"remove all 3" (SL.remove 42 sl);
  assert_true ~msg:"remove all: empty" (SL.is_empty sl);
  assert_true ~msg:"remove all: height 0" (SL.height sl = 0);

  (* -- Range queries -- *)
  let sl2 = SL.create () in
  List.iter (fun x -> SL.insert x sl2) [5; 10; 15; 20; 25; 30; 35; 40];
  assert_true ~msg:"range [10,30]"
    (SL.range_query ~lo:10 ~hi:30 sl2 = [10; 15; 20; 25; 30]);
  assert_true ~msg:"range [12,28]"
    (SL.range_query ~lo:12 ~hi:28 sl2 = [15; 20; 25]);
  assert_true ~msg:"range [5,5]"
    (SL.range_query ~lo:5 ~hi:5 sl2 = [5]);
  assert_true ~msg:"range [40,40]"
    (SL.range_query ~lo:40 ~hi:40 sl2 = [40]);
  assert_true ~msg:"range [6,9]"
    (SL.range_query ~lo:6 ~hi:9 sl2 = []);
  assert_true ~msg:"range [0,100]"
    (SL.range_query ~lo:0 ~hi:100 sl2 =
     [5; 10; 15; 20; 25; 30; 35; 40]);
  assert_true ~msg:"range inverted"
    (SL.range_query ~lo:30 ~hi:10 sl2 = []);

  (* -- Floor and ceil -- *)
  assert_true ~msg:"floor 10" (SL.floor 10 sl2 = Some 10);
  assert_true ~msg:"floor 12" (SL.floor 12 sl2 = Some 10);
  assert_true ~msg:"floor 4" (SL.floor 4 sl2 = None);
  assert_true ~msg:"floor 40" (SL.floor 40 sl2 = Some 40);
  assert_true ~msg:"floor 100" (SL.floor 100 sl2 = Some 40);
  assert_true ~msg:"ceil 10" (SL.ceil 10 sl2 = Some 10);
  assert_true ~msg:"ceil 12" (SL.ceil 12 sl2 = Some 15);
  assert_true ~msg:"ceil 41" (SL.ceil 41 sl2 = None);
  assert_true ~msg:"ceil 1" (SL.ceil 1 sl2 = Some 5);
  assert_true ~msg:"ceil 40" (SL.ceil 40 sl2 = Some 40);

  (* -- Fold -- *)
  let sum = SL.fold (fun acc x -> acc + x) 0 sl2 in
  assert_equal ~msg:"fold sum" "180" (string_of_int sum);
  let product = SL.fold (fun acc x -> acc * x) 1 sl2 in
  assert_equal ~msg:"fold product"
    (string_of_int (5 * 10 * 15 * 20 * 25 * 30 * 35 * 40))
    (string_of_int product);

  (* -- Iter -- *)
  let iter_acc = ref [] in
  SL.iter (fun x -> iter_acc := x :: !iter_acc) sl2;
  assert_true ~msg:"iter order"
    (List.rev !iter_acc = [5; 10; 15; 20; 25; 30; 35; 40]);

  (* -- of_list -- *)
  let sl3 = SL.of_list [9; 3; 7; 1; 5] in
  assert_equal ~msg:"of_list: size" "5" (string_of_int (SL.size sl3));
  assert_true ~msg:"of_list: sorted"
    (SL.to_list sl3 = [1; 3; 5; 7; 9]);

  (* of_list with duplicates *)
  let sl4 = SL.of_list [5; 3; 5; 1; 3; 1] in
  assert_equal ~msg:"of_list dup: size" "3" (string_of_int (SL.size sl4));
  assert_true ~msg:"of_list dup: sorted"
    (SL.to_list sl4 = [1; 3; 5]);

  (* -- Custom compare (reverse order) -- *)
  let rev_sl = SL.create ~compare:(fun a b -> compare b a) () in
  List.iter (fun x -> SL.insert x rev_sl) [10; 30; 20];
  assert_true ~msg:"reverse: to_list"
    (SL.to_list rev_sl = [30; 20; 10]);
  assert_true ~msg:"reverse: min_elt" (SL.min_elt rev_sl = Some 30);
  assert_true ~msg:"reverse: max_elt" (SL.max_elt rev_sl = Some 10);

  (* -- String skip list -- *)
  let str_sl = SL.create ~compare:String.compare () in
  List.iter (fun s -> SL.insert s str_sl) ["cherry"; "apple"; "banana"; "date"];
  assert_equal ~msg:"string: size" "4" (string_of_int (SL.size str_sl));
  assert_true ~msg:"string: sorted"
    (SL.to_list str_sl = ["apple"; "banana"; "cherry"; "date"]);
  assert_true ~msg:"string: mem banana" (SL.mem "banana" str_sl);
  assert_true ~msg:"string: floor 'c'" (SL.floor "c" str_sl = Some "banana");
  assert_true ~msg:"string: ceil 'c'" (SL.ceil "c" str_sl = Some "cherry");

  (* -- Stress test: insert + verify sorted + remove all -- *)
  let stress_sl = SL.create () in
  let n = 500 in
  (* Shuffle: insert 0..499 in random order *)
  let arr = Array.init n (fun i -> i) in
  for i = n - 1 downto 1 do
    let j = Random.int (i + 1) in
    let tmp = arr.(i) in
    arr.(i) <- arr.(j);
    arr.(j) <- tmp
  done;
  Array.iter (fun x -> SL.insert x stress_sl) arr;
  assert_equal ~msg:"stress: size" "500" (string_of_int (SL.size stress_sl));

  let sorted = SL.to_list stress_sl in
  let expected = List.init n (fun i -> i) in
  assert_true ~msg:"stress: sorted order" (sorted = expected);
  assert_true ~msg:"stress: min" (SL.min_elt stress_sl = Some 0);
  assert_true ~msg:"stress: max" (SL.max_elt stress_sl = Some 499);
  assert_true ~msg:"stress: mem 250" (SL.mem 250 stress_sl);
  assert_true ~msg:"stress: not mem 500" (not (SL.mem 500 stress_sl));

  (* Range query on stress list *)
  let range = SL.range_query ~lo:100 ~hi:199 stress_sl in
  assert_equal ~msg:"stress range: length" "100" (string_of_int (List.length range));
  assert_true ~msg:"stress range: first" (List.hd range = 100);
  assert_true ~msg:"stress range: last"
    (List.nth range 99 = 199);

  (* Floor/ceil on stress list *)
  assert_true ~msg:"stress: floor 250" (SL.floor 250 stress_sl = Some 250);
  assert_true ~msg:"stress: ceil 250" (SL.ceil 250 stress_sl = Some 250);

  (* Remove even numbers *)
  for i = 0 to 249 do
    ignore (SL.remove (i * 2) stress_sl)
  done;
  assert_equal ~msg:"stress remove: size" "250" (string_of_int (SL.size stress_sl));
  assert_true ~msg:"stress remove: no evens" (not (SL.mem 0 stress_sl));
  assert_true ~msg:"stress remove: has odds" (SL.mem 1 stress_sl);
  assert_true ~msg:"stress remove: min" (SL.min_elt stress_sl = Some 1);
  assert_true ~msg:"stress remove: max" (SL.max_elt stress_sl = Some 499);

  (* Remove all remaining *)
  let remaining = SL.to_list stress_sl in
  List.iter (fun x -> ignore (SL.remove x stress_sl)) remaining;
  assert_true ~msg:"stress remove all: empty" (SL.is_empty stress_sl);
  assert_equal ~msg:"stress remove all: size" "0" (string_of_int (SL.size stress_sl));

  (* -- Re-insert after clearing -- *)
  SL.insert 100 stress_sl;
  SL.insert 50 stress_sl;
  assert_equal ~msg:"reuse: size" "2" (string_of_int (SL.size stress_sl));
  assert_true ~msg:"reuse: sorted" (SL.to_list stress_sl = [50; 100]);

  Printf.printf "  SkipList: done\n";
()

(* ===== Main ===== *)

let () =
  Printf.printf "\n=== OCaml Sample Code Test Suite ===\n\n";
  test_bst ();
  test_factors ();
  test_fibonacci ();
  test_mergesort ();
  test_heap ();
  test_list_last ();
  test_graph ();
  test_trie ();
  test_parser ();
  test_regex ();
  test_stream ();
  test_rbtree ();
  test_sorting ();
  test_union_find ();
  test_hashmap ();
  test_bloom_filter ();
  test_lru_cache ();
  test_skip_list ();
  Printf.printf "\n=== Results ===\n";
  Printf.printf "Total: %d | Passed: %d | Failed: %d\n"
    !tests_run !tests_passed !tests_failed;
  if !tests_failed > 0 then begin
    Printf.printf "STATUS: SOME TESTS FAILED\n";
    exit 1
  end else begin
    Printf.printf "STATUS: ALL TESTS PASSED ✓\n";
    exit 0
  end
