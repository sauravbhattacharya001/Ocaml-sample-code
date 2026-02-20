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
  String.init (List.length chars) (List.nth chars)

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
    | ParseError (_, epos1) ->
      if epos1 = pos then p2 input pos
      else p1 input pos

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
