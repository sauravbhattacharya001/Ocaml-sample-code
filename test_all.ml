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
