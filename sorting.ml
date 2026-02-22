(* Sorting algorithms in OCaml *)
(* Demonstrates: comparison sorts, non-comparison sorts, stability,
   tail recursion, higher-order functions, pattern matching *)

(* ===== Predicates ===== *)

(** Check whether a list is sorted according to a comparator. *)
let is_sorted cmp lst =
  let rec aux = function
    | [] | [_] -> true
    | x :: (y :: _ as rest) -> cmp x y <= 0 && aux rest
  in
  aux lst

(** Check whether a list is sorted in strictly ascending order. *)
let is_strictly_sorted cmp lst =
  let rec aux = function
    | [] | [_] -> true
    | x :: (y :: _ as rest) -> cmp x y < 0 && aux rest
  in
  aux lst

(* ===== Insertion Sort ===== *)
(* Stable, O(n²) worst/average, O(n) best (already sorted).
   Simple and efficient for small inputs or nearly-sorted data. *)

(** Insert an element into its correct position in a sorted list. *)
let rec insert cmp x = function
  | [] -> [x]
  | h :: t as lst ->
    if cmp x h <= 0 then x :: lst
    else h :: insert cmp x t

(** Sort a list using insertion sort. Stable. *)
let insertion_sort cmp lst =
  List.fold_left (fun acc x -> insert cmp x acc) [] lst

(* ===== Selection Sort ===== *)
(* Not stable, O(n²) always. Minimal swaps — useful when writes are expensive. *)

(** Find and remove the minimum element from a list. *)
let select_min cmp = function
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

(** Sort a list using selection sort. Not stable. *)
let selection_sort cmp lst =
  let rec aux acc = function
    | [] -> List.rev acc
    | remaining ->
      let (min_val, rest) = select_min cmp remaining in
      aux (min_val :: acc) rest
  in
  aux [] lst

(* ===== Quicksort ===== *)
(* Not stable (this version), O(n log n) average, O(n²) worst.
   Uses median-of-three pivot selection to avoid worst case on
   sorted/reverse-sorted inputs. *)

(** Partition a list into (less, equal, greater) relative to a pivot. *)
let partition3 cmp pivot lst =
  let rec aux lt eq gt = function
    | [] -> (List.rev lt, List.rev eq, List.rev gt)
    | x :: rest ->
      let c = cmp x pivot in
      if c < 0 then aux (x :: lt) eq gt rest
      else if c = 0 then aux lt (x :: eq) gt rest
      else aux lt eq (x :: gt) rest
  in
  aux [] [] [] lst

(** Choose median-of-three pivot from first, middle, last elements. *)
let median_of_three cmp lst =
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

(** Sort a list using quicksort with median-of-three pivot. *)
let rec quicksort cmp = function
  | ([] | [_]) as l -> l
  | lst ->
    let pivot = median_of_three cmp lst in
    let (lt, eq, gt) = partition3 cmp pivot lst in
    quicksort cmp lt @ eq @ quicksort cmp gt

(* ===== Heapsort ===== *)
(* Not stable, O(n log n) always. Uses a functional min-heap
   (leftist heap) for extraction. *)

type 'a heap =
  | Empty
  | HNode of int * 'a * 'a heap * 'a heap

let heap_rank = function
  | Empty -> 0
  | HNode (r, _, _, _) -> r

let heap_make x a b =
  if heap_rank a >= heap_rank b then HNode (heap_rank b + 1, x, a, b)
  else HNode (heap_rank a + 1, x, b, a)

let rec heap_merge cmp h1 h2 =
  match h1, h2 with
  | Empty, h | h, Empty -> h
  | HNode (_, x, a1, b1), HNode (_, y, _, _) ->
    if cmp x y <= 0 then heap_make x a1 (heap_merge cmp b1 h2)
    else heap_merge cmp h2 h1

let heap_insert cmp x h = heap_merge cmp (HNode (1, x, Empty, Empty)) h

let heap_extract_min cmp = function
  | Empty -> None
  | HNode (_, x, left, right) -> Some (x, heap_merge cmp left right)

(** Sort a list using heapsort (leftist min-heap). *)
let heapsort cmp lst =
  let h = List.fold_left (fun h x -> heap_insert cmp x h) Empty lst in
  let rec drain acc h =
    match heap_extract_min cmp h with
    | None -> List.rev acc
    | Some (x, h') -> drain (x :: acc) h'
  in
  drain [] h

(* ===== Counting Sort ===== *)
(* Stable, O(n + k) where k = max - min + 1.
   Only works on integers within a bounded range. *)

(** Sort a list of integers using counting sort.
    Requires [lo] and [hi] bounds (inclusive). *)
let counting_sort ?(lo=0) ~hi lst =
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

(* ===== Timsort-style merge for nearly-sorted data ===== *)
(* Detects existing sorted runs and merges them. More efficient
   than pure mergesort on partially sorted data. *)

(** Detect ascending runs (natural runs) in a list. *)
let find_runs cmp lst =
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

(** Merge two sorted lists. Tail-recursive. *)
let merge cmp l1 l2 =
  let rec aux acc l1 l2 =
    match l1, l2 with
    | [], l | l, [] -> List.rev_append acc l
    | h1 :: t1, h2 :: t2 ->
      if cmp h1 h2 <= 0 then aux (h1 :: acc) t1 l2
      else aux (h2 :: acc) l1 t2
  in
  aux [] l1 l2

(** Merge a list of sorted runs pairwise until one remains. *)
let rec merge_runs cmp = function
  | [] -> []
  | [single] -> single
  | runs ->
    let rec pairwise acc = function
      | [] -> List.rev acc
      | [r] -> List.rev (r :: acc)
      | r1 :: r2 :: rest -> pairwise (merge cmp r1 r2 :: acc) rest
    in
    merge_runs cmp (pairwise [] runs)

(** Natural merge sort — finds existing sorted runs, then merges them.
    O(n log n) worst, O(n) best on already-sorted data. Stable. *)
let natural_mergesort cmp lst =
  match lst with
  | ([] | [_]) as l -> l
  | _ -> merge_runs cmp (find_runs cmp lst)

(* ===== Utilities ===== *)

(** Apply a sort function and return (sorted_list, time_in_seconds). *)
let timed sort_fn cmp lst =
  let t0 = Sys.time () in
  let result = sort_fn cmp lst in
  let t1 = Sys.time () in
  (result, t1 -. t0)

(** Generate a list of n random integers in [lo, hi]. *)
let random_list n lo hi =
  List.init n (fun _ -> lo + Random.int (hi - lo + 1))

(** Generate a list [0; 1; ...; n-1]. *)
let ascending_list n = List.init n Fun.id

(** Generate a list [n-1; n-2; ...; 0]. *)
let descending_list n = List.init n (fun i -> n - 1 - i)

(** Generate a list of n identical values. *)
let constant_list n v = List.init n (fun _ -> v)

(* Pretty print *)
let string_of_int_list lst =
  "[" ^ String.concat "; " (List.map string_of_int lst) ^ "]"

(* ===== Demo ===== *)

let () =
  let data = [38; 27; 43; 3; 9; 82; 10] in
  Printf.printf "Original:     %s\n" (string_of_int_list data);
  Printf.printf "Insertion:    %s\n" (string_of_int_list (insertion_sort compare data));
  Printf.printf "Selection:    %s\n" (string_of_int_list (selection_sort compare data));
  Printf.printf "Quicksort:    %s\n" (string_of_int_list (quicksort compare data));
  Printf.printf "Heapsort:     %s\n" (string_of_int_list (heapsort compare data));
  Printf.printf "Natural MS:   %s\n" (string_of_int_list (natural_mergesort compare data));
  Printf.printf "Counting:     %s\n" (string_of_int_list (counting_sort ~hi:82 data));
  Printf.printf "Is sorted?    %b\n" (is_sorted compare data);
  Printf.printf "After sort?   %b\n" (is_sorted compare (quicksort compare data));

  (* Benchmark *)
  Random.self_init ();
  let n = 5000 in
  let big = random_list n 0 10000 in
  Printf.printf "\nBenchmark (%d random ints):\n" n;
  let run name sort_fn =
    let (_, t) = timed sort_fn compare big in
    Printf.printf "  %-18s %.4fs\n" name t
  in
  run "Insertion sort" insertion_sort;
  run "Selection sort" selection_sort;
  run "Quicksort" quicksort;
  run "Heapsort" heapsort;
  run "Natural mergesort" natural_mergesort
