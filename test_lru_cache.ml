(* test_lru_cache.ml — Tests for LRU Cache module *)
(* Run: ocaml test_lru_cache.ml *)

#use "lru_cache.ml";;

open LRUCache

let tests_run = ref 0
let tests_passed = ref 0
let tests_failed = ref 0

let assert_true ~msg cond =
  incr tests_run;
  if cond then incr tests_passed
  else begin
    incr tests_failed;
    Printf.printf "  FAIL: %s\n" msg
  end

let assert_equal ~msg expected actual =
  incr tests_run;
  if expected = actual then incr tests_passed
  else begin
    incr tests_failed;
    Printf.printf "  FAIL: %s (expected %s, got %s)\n" msg expected actual
  end

let assert_raises ~msg f =
  incr tests_run;
  try ignore (f ()); incr tests_failed;
      Printf.printf "  FAIL: %s: expected exception\n" msg
  with _ -> incr tests_passed

(* ============================================================ *)
(* Create                                                        *)
(* ============================================================ *)
let () = Printf.printf "Testing LRU Cache...\n"

let () =
  let c = create 5 in
  assert_true ~msg:"create: empty" (is_empty c);
  assert_equal ~msg:"create: capacity" "5" (string_of_int (capacity c));
  assert_equal ~msg:"create: size 0" "0" (string_of_int (size c))

let () =
  assert_raises ~msg:"create: capacity 0 raises" (fun () -> create 0)

let () =
  assert_raises ~msg:"create: negative capacity raises" (fun () -> create (-3))

let () =
  let c = create 1 in
  assert_equal ~msg:"create: capacity 1" "1" (string_of_int (capacity c))

(* ============================================================ *)
(* Put                                                           *)
(* ============================================================ *)
let () =
  let c = create 3 in
  let c = put "a" 1 c in
  assert_equal ~msg:"put: size 1" "1" (string_of_int (size c));
  assert_true ~msg:"put: mem" (mem "a" c)

let () =
  let c = create 3 in
  let c = put "a" 1 c in
  let c = put "b" 2 c in
  let c = put "c" 3 c in
  assert_equal ~msg:"put 3: size" "3" (string_of_int (size c));
  assert_true ~msg:"put 3: mem a" (mem "a" c);
  assert_true ~msg:"put 3: mem b" (mem "b" c);
  assert_true ~msg:"put 3: mem c" (mem "c" c)

(* put triggers eviction *)
let () =
  let c = create 2 in
  let c = put "a" 1 c in
  let c = put "b" 2 c in
  let c = put "c" 3 c in
  assert_equal ~msg:"eviction: size 2" "2" (string_of_int (size c));
  assert_true ~msg:"eviction: a gone" (not (mem "a" c));
  assert_true ~msg:"eviction: b present" (mem "b" c);
  assert_true ~msg:"eviction: c present" (mem "c" c)

(* put updates existing key *)
let () =
  let c = create 3 in
  let c = put "a" 1 c in
  let c = put "a" 99 c in
  assert_equal ~msg:"update: size stays 1" "1" (string_of_int (size c));
  assert_equal ~msg:"update: value changed" "99"
    (string_of_int (match peek "a" c with Some v -> v | None -> -1))

(* put update promotes to front *)
let () =
  let c = create 2 in
  let c = put "a" 1 c in
  let c = put "b" 2 c in
  let c = put "a" 10 c in  (* promote "a" *)
  let c = put "c" 3 c in   (* should evict "b", not "a" *)
  assert_true ~msg:"promote: a survives" (mem "a" c);
  assert_true ~msg:"promote: b evicted" (not (mem "b" c));
  assert_true ~msg:"promote: c present" (mem "c" c)

(* capacity 1 *)
let () =
  let c = create 1 in
  let c = put "a" 1 c in
  let c = put "b" 2 c in
  assert_equal ~msg:"cap 1: size" "1" (string_of_int (size c));
  assert_true ~msg:"cap 1: only b" (mem "b" c);
  assert_true ~msg:"cap 1: a gone" (not (mem "a" c))

(* ============================================================ *)
(* Get                                                           *)
(* ============================================================ *)
let () =
  let c = create 3 in
  let c = put "x" 42 c in
  let (v, _) = get "x" c in
  assert_equal ~msg:"get: found" "42"
    (string_of_int (match v with Some x -> x | None -> -1))

let () =
  let c = create 3 in
  let (v, _) = get "missing" c in
  assert_true ~msg:"get: miss returns None" (v = None)

(* get promotes entry *)
let () =
  let c = create 2 in
  let c = put "a" 1 c in
  let c = put "b" 2 c in
  let (_, c) = get "a" c in   (* promote "a" *)
  let c = put "c" 3 c in      (* should evict "b" *)
  assert_true ~msg:"get promote: a survives" (mem "a" c);
  assert_true ~msg:"get promote: b evicted" (not (mem "b" c))

(* get updates hit counter *)
let () =
  let c = create 3 in
  let c = put "a" 1 c in
  let (_, c) = get "a" c in
  let (hits, misses, _) = stats c in
  assert_equal ~msg:"get: hit count" "1" (string_of_int hits);
  assert_equal ~msg:"get: miss count 0" "0" (string_of_int misses)

(* get updates miss counter *)
let () =
  let c = create 3 in
  let (_, c) = get "nope" c in
  let (hits, misses, _) = stats c in
  assert_equal ~msg:"miss: hit 0" "0" (string_of_int hits);
  assert_equal ~msg:"miss: miss 1" "1" (string_of_int misses)

(* ============================================================ *)
(* Peek                                                          *)
(* ============================================================ *)
let () =
  let c = create 3 in
  let c = put "a" 1 c in
  assert_equal ~msg:"peek: found" "1"
    (string_of_int (match peek "a" c with Some v -> v | None -> -1))

let () =
  let c = create 3 in
  assert_true ~msg:"peek: miss" (peek "nope" c = None)

(* peek does NOT promote *)
let () =
  let c = create 2 in
  let c = put "a" 1 c in
  let c = put "b" 2 c in
  let _ = peek "a" c in      (* should NOT promote *)
  let c = put "c" 3 c in     (* should evict "a", not "b" *)
  assert_true ~msg:"peek no promote: a evicted" (not (mem "a" c));
  assert_true ~msg:"peek no promote: b present" (mem "b" c)

(* ============================================================ *)
(* Mem                                                           *)
(* ============================================================ *)
let () =
  let c = create 3 in
  assert_true ~msg:"mem: empty false" (not (mem "x" c));
  let c = put "x" 1 c in
  assert_true ~msg:"mem: present true" (mem "x" c)

(* ============================================================ *)
(* Remove                                                        *)
(* ============================================================ *)
let () =
  let c = create 3 in
  let c = put "a" 1 c in
  let c = put "b" 2 c in
  let c = remove "a" c in
  assert_equal ~msg:"remove: size" "1" (string_of_int (size c));
  assert_true ~msg:"remove: a gone" (not (mem "a" c));
  assert_true ~msg:"remove: b stays" (mem "b" c)

let () =
  let c = create 3 in
  let c = remove "nonexistent" c in
  assert_equal ~msg:"remove missing: no error" "0" (string_of_int (size c))

(* ============================================================ *)
(* Evict                                                         *)
(* ============================================================ *)
let () =
  let c = create 3 in
  let c = put "a" 1 c in
  let c = put "b" 2 c in
  let c = put "c" 3 c in
  let (evicted, c) = evict c in
  assert_equal ~msg:"evict: got LRU key" "a"
    (match evicted with Some (k, _) -> k | None -> "none");
  assert_equal ~msg:"evict: size 2" "2" (string_of_int (size c));
  assert_true ~msg:"evict: a gone" (not (mem "a" c))

let () =
  let c = create 3 in
  let (evicted, _) = evict c in
  assert_true ~msg:"evict empty: None" (evicted = None)

(* ============================================================ *)
(* is_empty / is_full                                            *)
(* ============================================================ *)
let () =
  let c = create 2 in
  assert_true ~msg:"is_empty: true" (is_empty c);
  let c = put "a" 1 c in
  assert_true ~msg:"is_empty: false after put" (not (is_empty c))

let () =
  let c = create 2 in
  let c = put "a" 1 c in
  assert_true ~msg:"is_full: false" (not (is_full c));
  let c = put "b" 2 c in
  assert_true ~msg:"is_full: true" (is_full c)

(* ============================================================ *)
(* to_list / keys / values                                       *)
(* ============================================================ *)
let () =
  let c = create 3 in
  let c = put "a" 1 c in
  let c = put "b" 2 c in
  let c = put "c" 3 c in
  let lst = to_list c in
  assert_equal ~msg:"to_list: length" "3" (string_of_int (List.length lst));
  (* Most recent first *)
  assert_equal ~msg:"to_list: first is c" "c" (fst (List.nth lst 0));
  assert_equal ~msg:"to_list: second is b" "b" (fst (List.nth lst 1));
  assert_equal ~msg:"to_list: third is a" "a" (fst (List.nth lst 2))

let () =
  let c = create 3 in
  let c = put "a" 1 c in
  let c = put "b" 2 c in
  assert_equal ~msg:"keys: count" "2" (string_of_int (List.length (keys c)));
  assert_equal ~msg:"values: count" "2" (string_of_int (List.length (values c)))

(* ============================================================ *)
(* Stats                                                         *)
(* ============================================================ *)
let () =
  let c = create 3 in
  let (h, m, r) = stats c in
  assert_equal ~msg:"stats empty: hits" "0" (string_of_int h);
  assert_equal ~msg:"stats empty: misses" "0" (string_of_int m);
  assert_true ~msg:"stats empty: rate 0" (r = 0.0)

let () =
  let c = create 3 in
  let c = put "a" 1 c in
  let c = put "b" 2 c in
  let (_, c) = get "a" c in
  let (_, c) = get "a" c in
  let (_, c) = get "miss" c in
  let (h, m, r) = stats c in
  assert_equal ~msg:"stats: 2 hits" "2" (string_of_int h);
  assert_equal ~msg:"stats: 1 miss" "1" (string_of_int m);
  assert_true ~msg:"stats: rate ~0.667"
    (r > 0.66 && r < 0.68)

(* ============================================================ *)
(* Clear                                                         *)
(* ============================================================ *)
let () =
  let c = create 3 in
  let c = put "a" 1 c in
  let c = put "b" 2 c in
  let c = clear c in
  assert_true ~msg:"clear: empty" (is_empty c);
  assert_equal ~msg:"clear: capacity preserved" "3"
    (string_of_int (capacity c))

(* ============================================================ *)
(* Resize                                                        *)
(* ============================================================ *)
let () =
  let c = create 5 in
  let c = put "a" 1 c in
  let c = put "b" 2 c in
  let c = put "c" 3 c in
  let c = resize 2 c in
  assert_equal ~msg:"resize: capacity" "2" (string_of_int (capacity c));
  assert_equal ~msg:"resize: size trimmed" "2" (string_of_int (size c));
  assert_true ~msg:"resize: most recent kept" (mem "c" c);
  assert_true ~msg:"resize: second recent kept" (mem "b" c);
  assert_true ~msg:"resize: oldest evicted" (not (mem "a" c))

let () =
  let c = create 2 in
  let c = put "a" 1 c in
  let c = resize 5 c in
  assert_equal ~msg:"resize up: capacity" "5" (string_of_int (capacity c));
  assert_equal ~msg:"resize up: size preserved" "1" (string_of_int (size c))

let () =
  assert_raises ~msg:"resize: 0 raises" (fun () -> resize 0 (create 3))

(* ============================================================ *)
(* of_list                                                       *)
(* ============================================================ *)
let () =
  let c = of_list 3 [("a", 1); ("b", 2); ("c", 3)] in
  assert_equal ~msg:"of_list: size" "3" (string_of_int (size c));
  assert_true ~msg:"of_list: mem a" (mem "a" c);
  assert_true ~msg:"of_list: mem c" (mem "c" c);
  (* "a" should be most recent (first in list) *)
  let lst = to_list c in
  assert_equal ~msg:"of_list: order" "a" (fst (List.hd lst))

let () =
  let c = of_list 2 [("a", 1); ("b", 2); ("c", 3)] in
  assert_equal ~msg:"of_list overflow: size 2" "2" (string_of_int (size c));
  assert_true ~msg:"of_list overflow: a present" (mem "a" c);
  assert_true ~msg:"of_list overflow: b present" (mem "b" c)

let () =
  assert_raises ~msg:"of_list: 0 cap raises" (fun () -> of_list 0 [("a", 1)])

(* ============================================================ *)
(* Fold                                                          *)
(* ============================================================ *)
let () =
  let c = create 3 in
  let c = put "a" 1 c in
  let c = put "b" 2 c in
  let c = put "c" 3 c in
  let total = fold (fun acc _k v -> acc + v) 0 c in
  assert_equal ~msg:"fold: sum" "6" (string_of_int total)

let () =
  let c = create 3 in
  let result = fold (fun acc _k _v -> acc + 1) 0 c in
  assert_equal ~msg:"fold empty: 0" "0" (string_of_int result)

(* ============================================================ *)
(* Iter                                                          *)
(* ============================================================ *)
let () =
  let c = create 3 in
  let c = put "a" 1 c in
  let c = put "b" 2 c in
  let count = ref 0 in
  iter (fun _k _v -> incr count) c;
  assert_equal ~msg:"iter: count" "2" (string_of_int !count)

(* ============================================================ *)
(* Filter                                                        *)
(* ============================================================ *)
let () =
  let c = create 5 in
  let c = put "a" 1 c in
  let c = put "b" 2 c in
  let c = put "c" 3 c in
  let c = put "d" 4 c in
  let filtered = filter (fun _k v -> v > 2) c in
  assert_equal ~msg:"filter: size" "2" (string_of_int (size filtered));
  assert_true ~msg:"filter: c present" (mem "c" filtered);
  assert_true ~msg:"filter: d present" (mem "d" filtered);
  assert_true ~msg:"filter: a gone" (not (mem "a" filtered))

let () =
  let c = create 3 in
  let c = put "a" 1 c in
  let filtered = filter (fun _k _v -> false) c in
  assert_true ~msg:"filter all: empty" (is_empty filtered)

(* ============================================================ *)
(* Map values                                                    *)
(* ============================================================ *)
let () =
  let c = create 3 in
  let c = put "a" 1 c in
  let c = put "b" 2 c in
  let doubled = map_values (fun v -> v * 2) c in
  assert_equal ~msg:"map_values: a doubled" "2"
    (string_of_int (match peek "a" doubled with Some v -> v | None -> -1));
  assert_equal ~msg:"map_values: b doubled" "4"
    (string_of_int (match peek "b" doubled with Some v -> v | None -> -1))

(* ============================================================ *)
(* Stress tests                                                  *)
(* ============================================================ *)
let () =
  let c = create 100 in
  let c = ref c in
  for i = 0 to 999 do
    c := put (string_of_int i) i !c
  done;
  assert_equal ~msg:"stress: size capped at 100" "100"
    (string_of_int (size !c));
  (* Most recent 100 entries (900-999) should be present *)
  assert_true ~msg:"stress: 999 present" (mem "999" !c);
  assert_true ~msg:"stress: 900 present" (mem "900" !c);
  assert_true ~msg:"stress: 899 evicted" (not (mem "899" !c));
  assert_true ~msg:"stress: 0 evicted" (not (mem "0" !c))

(* Mixed get/put *)
let () =
  let c = create 3 in
  let c = put "a" 1 c in
  let c = put "b" 2 c in
  let c = put "c" 3 c in
  let (_, c) = get "a" c in  (* promote a *)
  let c = put "d" 4 c in     (* evicts b *)
  let c = put "e" 5 c in     (* evicts c *)
  assert_true ~msg:"mixed: a alive" (mem "a" c);
  assert_true ~msg:"mixed: d alive" (mem "d" c);
  assert_true ~msg:"mixed: e alive" (mem "e" c);
  assert_true ~msg:"mixed: b dead" (not (mem "b" c));
  assert_true ~msg:"mixed: c dead" (not (mem "c" c))

(* Multiple evictions in sequence *)
let () =
  let c = create 2 in
  let c = put "a" 1 c in
  let c = put "b" 2 c in
  let (ev1, c) = evict c in
  let (ev2, c) = evict c in
  let (ev3, _) = evict c in
  assert_equal ~msg:"multi-evict: first is a" "a"
    (match ev1 with Some (k, _) -> k | None -> "none");
  assert_equal ~msg:"multi-evict: second is b" "b"
    (match ev2 with Some (k, _) -> k | None -> "none");
  assert_true ~msg:"multi-evict: third is None" (ev3 = None)

(* Integer keys *)
let () =
  let c = create 3 in
  let c = put 1 "one" c in
  let c = put 2 "two" c in
  let c = put 3 "three" c in
  assert_equal ~msg:"int keys: peek 2" "two"
    (match peek 2 c with Some v -> v | None -> "none");
  let c = put 4 "four" c in
  assert_true ~msg:"int keys: 1 evicted" (not (mem 1 c))

(* ============================================================ *)
(* Summary                                                       *)
(* ============================================================ *)
let () =
  Printf.printf "\n%d/%d tests passed (%d failed)\n"
    !tests_passed !tests_run !tests_failed;
  if !tests_failed > 0 then exit 1
