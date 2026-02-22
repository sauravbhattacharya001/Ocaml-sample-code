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
