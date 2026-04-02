(* test_heap.ml — Tests for Leftist Min-Heap *)
(* Run: ocaml test_heap.ml *)

#use "test_framework.ml";;
#use "heap.ml";;

let cmp = compare

let () = Printf.printf "Testing Heap (Leftist Min-Heap)...\n"

(* ============================================================ *)
(* Empty heap                                                    *)
(* ============================================================ *)
let () = suite "empty" (fun () ->
  assert_true  ~msg:"empty is_empty" (is_empty empty);
  assert_true  ~msg:"empty find_min is None" (find_min empty = None);
  assert_true  ~msg:"empty size is 0" (size empty = 0);
  assert_true  ~msg:"empty depth is 0" (depth empty = 0);
  assert_true  ~msg:"delete_min empty is empty" (is_empty (delete_min cmp empty));
  assert_true  ~msg:"empty is_leftist" (is_leftist empty);
  assert_true  ~msg:"empty is_min_heap" (is_min_heap cmp empty);
  assert_true  ~msg:"to_sorted_list empty" (to_sorted_list cmp empty = []);
  assert_true  ~msg:"to_list empty" (to_list empty = [])
)

(* ============================================================ *)
(* Single element                                                *)
(* ============================================================ *)
let () = suite "singleton" (fun () ->
  let h = insert cmp 42 empty in
  assert_false ~msg:"not empty" (is_empty h);
  assert_true  ~msg:"size 1" (size h = 1);
  assert_true  ~msg:"find_min" (find_min h = Some 42);
  assert_true  ~msg:"is_leftist" (is_leftist h);
  assert_true  ~msg:"is_min_heap" (is_min_heap cmp h);
  assert_true  ~msg:"delete_min gives empty" (is_empty (delete_min cmp h));
  assert_true  ~msg:"to_sorted_list" (to_sorted_list cmp h = [42])
)

(* ============================================================ *)
(* Insert & ordering                                             *)
(* ============================================================ *)
let () = suite "insert ordering" (fun () ->
  let h = from_list cmp [5; 3; 8; 1; 4; 7; 2; 6] in
  assert_true  ~msg:"size 8" (size h = 8);
  assert_true  ~msg:"min is 1" (find_min h = Some 1);
  assert_true  ~msg:"is_leftist" (is_leftist h);
  assert_true  ~msg:"is_min_heap" (is_min_heap cmp h);
  assert_true  ~msg:"sorted extraction" (to_sorted_list cmp h = [1; 2; 3; 4; 5; 6; 7; 8])
)

(* ============================================================ *)
(* Duplicate elements                                            *)
(* ============================================================ *)
let () = suite "duplicates" (fun () ->
  let h = from_list cmp [3; 1; 4; 1; 5; 9; 2; 6; 5; 3] in
  assert_true  ~msg:"size 10" (size h = 10);
  assert_true  ~msg:"min is 1" (find_min h = Some 1);
  assert_true  ~msg:"sorted list preserves dups"
    (to_sorted_list cmp h = [1; 1; 2; 3; 3; 4; 5; 5; 6; 9]);
  assert_true  ~msg:"is_leftist" (is_leftist h);
  assert_true  ~msg:"is_min_heap" (is_min_heap cmp h)
)

(* ============================================================ *)
(* delete_min                                                    *)
(* ============================================================ *)
let () = suite "delete_min" (fun () ->
  let h = from_list cmp [5; 1; 3; 2; 4] in
  let h1 = delete_min cmp h in
  assert_true  ~msg:"after first delete, min is 2" (find_min h1 = Some 2);
  assert_true  ~msg:"size decreases" (size h1 = 4);
  let h2 = delete_min cmp h1 in
  assert_true  ~msg:"after second delete, min is 3" (find_min h2 = Some 3);
  assert_true  ~msg:"is_leftist after deletes" (is_leftist h2);
  assert_true  ~msg:"is_min_heap after deletes" (is_min_heap cmp h2)
)

(* ============================================================ *)
(* Merge                                                         *)
(* ============================================================ *)
let () = suite "merge" (fun () ->
  let h1 = from_list cmp [1; 5; 9] in
  let h2 = from_list cmp [2; 4; 8] in
  let h = merge cmp h1 h2 in
  assert_true  ~msg:"merged size" (size h = 6);
  assert_true  ~msg:"merged min" (find_min h = Some 1);
  assert_true  ~msg:"merged sorted"
    (to_sorted_list cmp h = [1; 2; 4; 5; 8; 9]);
  assert_true  ~msg:"merged is_leftist" (is_leftist h);
  assert_true  ~msg:"merged is_min_heap" (is_min_heap cmp h);
  let h3 = merge cmp h1 empty in
  assert_true  ~msg:"merge with empty (right)" (to_sorted_list cmp h3 = [1; 5; 9]);
  let h4 = merge cmp empty h2 in
  assert_true  ~msg:"merge with empty (left)" (to_sorted_list cmp h4 = [2; 4; 8])
)

(* ============================================================ *)
(* from_list_fast                                                *)
(* ============================================================ *)
let () = suite "from_list_fast" (fun () ->
  let lst = [7; 2; 9; 1; 5; 3; 8; 4; 6] in
  let h = from_list_fast cmp lst in
  assert_true  ~msg:"size" (size h = 9);
  assert_true  ~msg:"min" (find_min h = Some 1);
  assert_true  ~msg:"sorted" (to_sorted_list cmp h = [1; 2; 3; 4; 5; 6; 7; 8; 9]);
  assert_true  ~msg:"is_leftist" (is_leftist h);
  assert_true  ~msg:"is_min_heap" (is_min_heap cmp h);
  let h2 = from_list_fast cmp [] in
  assert_true  ~msg:"from empty" (is_empty h2)
)

(* ============================================================ *)
(* heap_sort                                                     *)
(* ============================================================ *)
let () = suite "heap_sort" (fun () ->
  assert_true  ~msg:"sort random" (heap_sort cmp [5; 3; 8; 1; 4; 7; 2; 6] = [1; 2; 3; 4; 5; 6; 7; 8]);
  assert_true  ~msg:"sort empty" (heap_sort cmp [] = []);
  assert_true  ~msg:"sort singleton" (heap_sort cmp [42] = [42]);
  assert_true  ~msg:"sort already sorted" (heap_sort cmp [1; 2; 3; 4; 5] = [1; 2; 3; 4; 5]);
  assert_true  ~msg:"sort reverse" (heap_sort cmp [5; 4; 3; 2; 1] = [1; 2; 3; 4; 5]);
  assert_true  ~msg:"sort with duplicates" (heap_sort cmp [3; 1; 2; 1; 3] = [1; 1; 2; 3; 3])
)

(* ============================================================ *)
(* take_min                                                      *)
(* ============================================================ *)
let () = suite "take_min" (fun () ->
  let h = from_list cmp [5; 1; 3; 9; 2; 7; 4] in
  assert_true  ~msg:"take 3" (take_min cmp 3 h = [1; 2; 3]);
  assert_true  ~msg:"take 0" (take_min cmp 0 h = []);
  assert_true  ~msg:"take more than size" (take_min cmp 100 h = [1; 2; 3; 4; 5; 7; 9]);
  assert_true  ~msg:"take from empty" (take_min cmp 5 empty = [])
)

(* ============================================================ *)
(* Stress: leftist property                                      *)
(* ============================================================ *)
let () = suite "stress leftist property" (fun () ->
  let h = ref empty in
  for i = 100 downto 1 do
    h := insert cmp i !h
  done;
  assert_true  ~msg:"100 elements is_leftist" (is_leftist !h);
  assert_true  ~msg:"100 elements is_min_heap" (is_min_heap cmp !h);
  assert_true  ~msg:"100 elements min" (find_min !h = Some 1);
  assert_true  ~msg:"100 elements size" (size !h = 100);
  let sorted = to_sorted_list cmp !h in
  assert_true  ~msg:"100 elements sorted" (sorted = List.init 100 (fun i -> i + 1))
)

(* ============================================================ *)
(* Persistence                                                   *)
(* ============================================================ *)
let () = suite "persistence" (fun () ->
  let h0 = from_list cmp [3; 1; 4; 1; 5] in
  let h1 = insert cmp 0 h0 in
  let h2 = delete_min cmp h0 in
  assert_true  ~msg:"original unchanged after insert" (find_min h0 = Some 1);
  assert_true  ~msg:"original size unchanged" (size h0 = 5);
  assert_true  ~msg:"insert version min" (find_min h1 = Some 0);
  assert_true  ~msg:"insert version size" (size h1 = 6);
  assert_true  ~msg:"delete version min" (find_min h2 = Some 1);
  assert_true  ~msg:"delete version size" (size h2 = 4)
)

(* ============================================================ *)
(* Negative and zero values                                      *)
(* ============================================================ *)
let () = suite "negative values" (fun () ->
  let h = from_list cmp [-5; 0; 3; -10; 7; -1] in
  assert_true  ~msg:"min is -10" (find_min h = Some (-10));
  assert_true  ~msg:"sorted"
    (to_sorted_list cmp h = [-10; -5; -1; 0; 3; 7])
)

(* ============================================================ *)
(* Rank validation                                               *)
(* ============================================================ *)
let () = suite "rank" (fun () ->
  assert_true  ~msg:"rank of empty is 0" (rank empty = 0);
  let h = insert cmp 1 empty in
  assert_true  ~msg:"rank of singleton is 1" (rank h = 1);
  let h2 = merge cmp (insert cmp 1 empty) (insert cmp 2 empty) in
  assert_true  ~msg:"rank after merge <= 2" (rank h2 <= 2);
  assert_true  ~msg:"depth >= 1" (depth h2 >= 1)
)

let () = test_summary ()
