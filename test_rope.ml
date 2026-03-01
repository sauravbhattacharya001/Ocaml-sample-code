(* test_rope.ml — Tests for Rope module *)
(* Run: ocaml test_rope.ml *)

#use "rope.ml";;

open Rope

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
(* Construction                                                  *)
(* ============================================================ *)
let () = Printf.printf "Testing Rope...\n"

let () =
  let r = empty in
  assert_equal ~msg:"empty length" "0" (string_of_int (length r));
  assert_equal ~msg:"empty to_string" "" (to_string r);
  assert_equal ~msg:"empty depth" "0" (string_of_int (depth r))

let () =
  let r = of_string "hello" in
  assert_equal ~msg:"of_string length" "5" (string_of_int (length r));
  assert_equal ~msg:"of_string to_string" "hello" (to_string r)

let () =
  let r = of_string "" in
  assert_equal ~msg:"of_string empty length" "0" (string_of_int (length r));
  assert_equal ~msg:"of_string empty to_string" "" (to_string r)

(* Large string triggers tree splitting *)
let () =
  let s = String.make 2000 'x' in
  let r = of_string s in
  assert_equal ~msg:"large of_string length" "2000" (string_of_int (length r));
  assert_true ~msg:"large of_string has depth > 0" (depth r > 0);
  assert_equal ~msg:"large of_string roundtrip" s (to_string r)

(* ============================================================ *)
(* Concatenation                                                 *)
(* ============================================================ *)
let () =
  let a = of_string "hello" in
  let b = of_string " world" in
  let r = concat a b in
  assert_equal ~msg:"concat length" "11" (string_of_int (length r));
  assert_equal ~msg:"concat to_string" "hello world" (to_string r)

let () =
  let r = concat empty (of_string "abc") in
  assert_equal ~msg:"concat empty left" "abc" (to_string r)

let () =
  let r = concat (of_string "abc") empty in
  assert_equal ~msg:"concat empty right" "abc" (to_string r)

let () =
  let r = concat empty empty in
  assert_equal ~msg:"concat empty both" "" (to_string r)

(* Multiple concatenations *)
let () =
  let r = List.fold_left (fun acc s -> concat acc (of_string s))
    empty ["a"; "b"; "c"; "d"; "e"] in
  assert_equal ~msg:"multi concat" "abcde" (to_string r);
  assert_equal ~msg:"multi concat length" "5" (string_of_int (length r))

(* ============================================================ *)
(* Prepend / Append                                              *)
(* ============================================================ *)
let () =
  let r = of_string "world" in
  let r2 = prepend "hello " r in
  assert_equal ~msg:"prepend" "hello world" (to_string r2)

let () =
  let r = of_string "abc" in
  let r2 = append_char r 'd' in
  assert_equal ~msg:"append_char" "abcd" (to_string r2)

(* ============================================================ *)
(* Indexing                                                      *)
(* ============================================================ *)
let () =
  let r = of_string "abcdef" in
  assert_equal ~msg:"index 0" "a" (String.make 1 (index r 0));
  assert_equal ~msg:"index 3" "d" (String.make 1 (index r 3));
  assert_equal ~msg:"index 5" "f" (String.make 1 (index r 5))

let () =
  let r = concat (of_string "abc") (of_string "def") in
  assert_equal ~msg:"index across concat 0" "a" (String.make 1 (index r 0));
  assert_equal ~msg:"index across concat 3" "d" (String.make 1 (index r 3));
  assert_equal ~msg:"index across concat 5" "f" (String.make 1 (index r 5))

let () =
  let r = of_string "abc" in
  assert_raises ~msg:"index negative" (fun () -> index r (-1));
  assert_raises ~msg:"index out of bounds" (fun () -> index r 3)

(* ============================================================ *)
(* Split                                                         *)
(* ============================================================ *)
let () =
  let r = of_string "abcdef" in
  let (l, r2) = split r 3 in
  assert_equal ~msg:"split left" "abc" (to_string l);
  assert_equal ~msg:"split right" "def" (to_string r2)

let () =
  let r = of_string "abcdef" in
  let (l, r2) = split r 0 in
  assert_equal ~msg:"split at 0 left" "" (to_string l);
  assert_equal ~msg:"split at 0 right" "abcdef" (to_string r2)

let () =
  let r = of_string "abcdef" in
  let (l, r2) = split r 6 in
  assert_equal ~msg:"split at end left" "abcdef" (to_string l);
  assert_equal ~msg:"split at end right" "" (to_string r2)

(* Split on a concat boundary *)
let () =
  let r = concat (of_string "abc") (of_string "def") in
  let (l, r2) = split r 3 in
  assert_equal ~msg:"split at boundary left" "abc" (to_string l);
  assert_equal ~msg:"split at boundary right" "def" (to_string r2)

(* Split within left child *)
let () =
  let r = concat (of_string "abcde") (of_string "fghij") in
  let (l, r2) = split r 2 in
  assert_equal ~msg:"split within left" "ab" (to_string l);
  assert_equal ~msg:"split within left right" "cdefghij" (to_string r2)

(* Split within right child *)
let () =
  let r = concat (of_string "abcde") (of_string "fghij") in
  let (l, r2) = split r 7 in
  assert_equal ~msg:"split within right left" "abcdefg" (to_string l);
  assert_equal ~msg:"split within right right" "hij" (to_string r2)

(* ============================================================ *)
(* Substring                                                     *)
(* ============================================================ *)
let () =
  let r = of_string "hello world" in
  let sub = substring r 6 5 in
  assert_equal ~msg:"substring" "world" (to_string sub)

let () =
  let r = of_string "abcdef" in
  let sub = substring r 0 6 in
  assert_equal ~msg:"substring full" "abcdef" (to_string sub)

let () =
  let r = of_string "abcdef" in
  let sub = substring r 2 0 in
  assert_equal ~msg:"substring zero len" "" (to_string sub)

let () =
  let r = of_string "abc" in
  assert_raises ~msg:"substring out of bounds" (fun () -> substring r 2 3)

let () =
  let r = of_string "abc" in
  assert_raises ~msg:"substring negative start" (fun () -> substring r (-1) 1)

(* ============================================================ *)
(* Insert                                                        *)
(* ============================================================ *)
let () =
  let r = of_string "helloworld" in
  let r2 = insert r 5 " " in
  assert_equal ~msg:"insert middle" "hello world" (to_string r2)

let () =
  let r = of_string "world" in
  let r2 = insert r 0 "hello " in
  assert_equal ~msg:"insert at start" "hello world" (to_string r2)

let () =
  let r = of_string "hello" in
  let r2 = insert r 5 " world" in
  assert_equal ~msg:"insert at end" "hello world" (to_string r2)

let () =
  let r = of_string "abc" in
  assert_raises ~msg:"insert negative" (fun () -> insert r (-1) "x");
  assert_raises ~msg:"insert past end" (fun () -> insert r 4 "x")

(* ============================================================ *)
(* Delete                                                        *)
(* ============================================================ *)
let () =
  let r = of_string "hello cruel world" in
  let r2 = delete r 5 6 in
  assert_equal ~msg:"delete middle" "hello world" (to_string r2)

let () =
  let r = of_string "xxxhello" in
  let r2 = delete r 0 3 in
  assert_equal ~msg:"delete from start" "hello" (to_string r2)

let () =
  let r = of_string "helloyyy" in
  let r2 = delete r 5 3 in
  assert_equal ~msg:"delete from end" "hello" (to_string r2)

let () =
  let r = of_string "abc" in
  let r2 = delete r 1 0 in
  assert_equal ~msg:"delete zero len" "abc" (to_string r2)

let () =
  let r = of_string "abc" in
  assert_raises ~msg:"delete out of bounds" (fun () -> delete r 2 3)

(* ============================================================ *)
(* Iteration                                                     *)
(* ============================================================ *)
let () =
  let buf = Buffer.create 10 in
  iter (Buffer.add_char buf) (of_string "hello");
  assert_equal ~msg:"iter chars" "hello" (Buffer.contents buf)

let () =
  let r = concat (of_string "ab") (of_string "cd") in
  let leaves = ref [] in
  iter_leaves (fun s -> leaves := s :: !leaves) r;
  let ls = List.rev !leaves in
  assert_equal ~msg:"iter_leaves count" "2" (string_of_int (List.length ls));
  assert_equal ~msg:"iter_leaves first" "ab" (List.nth ls 0);
  assert_equal ~msg:"iter_leaves second" "cd" (List.nth ls 1)

(* ============================================================ *)
(* Fold                                                          *)
(* ============================================================ *)
let () =
  let r = of_string "hello" in
  let n = fold (fun acc _ -> acc + 1) 0 r in
  assert_equal ~msg:"fold count" "5" (string_of_int n)

let () =
  let r = of_string "aabbc" in
  let n = fold (fun acc c -> if c = 'b' then acc + 1 else acc) 0 r in
  assert_equal ~msg:"fold count b" "2" (string_of_int n)

(* ============================================================ *)
(* Map                                                           *)
(* ============================================================ *)
let () =
  let r = of_string "hello" in
  let r2 = map Char.uppercase_ascii r in
  assert_equal ~msg:"map uppercase" "HELLO" (to_string r2)

let () =
  let r = of_string "" in
  let r2 = map Char.uppercase_ascii r in
  assert_equal ~msg:"map empty" "" (to_string r2)

let () =
  let r = concat (of_string "ab") (of_string "cd") in
  let r2 = map Char.uppercase_ascii r in
  assert_equal ~msg:"map across concat" "ABCD" (to_string r2)

(* ============================================================ *)
(* Lines                                                         *)
(* ============================================================ *)
let () =
  let r = of_string "line1\nline2\nline3" in
  assert_equal ~msg:"line_count" "3" (string_of_int (line_count r))

let () =
  let r = of_string "no newlines" in
  assert_equal ~msg:"line_count no newlines" "1" (string_of_int (line_count r))

let () =
  let r = of_string "a\nb\nc" in
  let ls = lines r in
  assert_equal ~msg:"lines count" "3" (string_of_int (List.length ls));
  assert_equal ~msg:"line 0" "a" (to_string (List.nth ls 0));
  assert_equal ~msg:"line 1" "b" (to_string (List.nth ls 1));
  assert_equal ~msg:"line 2" "c" (to_string (List.nth ls 2))

let () =
  let r = of_string "a\nb\nc" in
  let l = get_line r 1 in
  assert_equal ~msg:"get_line 1" "b" (to_string l)

let () =
  let r = of_string "abc" in
  assert_raises ~msg:"get_line out of bounds" (fun () -> get_line r 1)

let () =
  let r = of_string "abc" in
  assert_raises ~msg:"get_line negative" (fun () -> get_line r (-1))

(* Trailing newline *)
let () =
  let r = of_string "a\n" in
  assert_equal ~msg:"trailing newline line_count" "2" (string_of_int (line_count r));
  let ls = lines r in
  assert_equal ~msg:"trailing newline lines" "2" (string_of_int (List.length ls));
  assert_equal ~msg:"trailing newline line 0" "a" (to_string (List.nth ls 0));
  assert_equal ~msg:"trailing newline line 1" "" (to_string (List.nth ls 1))

(* ============================================================ *)
(* Search                                                        *)
(* ============================================================ *)
let () =
  let r = of_string "abcdef" in
  (match find_char 'c' r with
   | Some p -> assert_equal ~msg:"find_char c" "2" (string_of_int p)
   | None -> assert_true ~msg:"find_char c found" false)

let () =
  let r = of_string "abcdef" in
  (match find_char 'z' r with
   | Some _ -> assert_true ~msg:"find_char z not found" false
   | None -> assert_true ~msg:"find_char z is None" true)

let () =
  let r = of_string "abcabc" in
  (match find_char ~from:3 'a' r with
   | Some p -> assert_equal ~msg:"find_char from 3" "3" (string_of_int p)
   | None -> assert_true ~msg:"find_char from 3 found" false)

let () =
  let r = of_string "aabbbcc" in
  assert_equal ~msg:"count_char b" "3" (string_of_int (count_char 'b' r))

let () =
  let r = of_string "abc" in
  assert_equal ~msg:"count_char z" "0" (string_of_int (count_char 'z' r))

(* ============================================================ *)
(* Equality and Comparison                                       *)
(* ============================================================ *)
let () =
  let a = of_string "hello" in
  let b = of_string "hello" in
  assert_true ~msg:"equal same content" (equal a b)

let () =
  let a = of_string "hello" in
  let b = concat (of_string "hel") (of_string "lo") in
  assert_true ~msg:"equal different structure" (equal a b)

let () =
  let a = of_string "abc" in
  let b = of_string "xyz" in
  assert_true ~msg:"not equal" (not (equal a b))

let () =
  let a = of_string "abc" in
  let b = of_string "ab" in
  assert_true ~msg:"not equal different length" (not (equal a b))

let () =
  let a = of_string "abc" in
  let b = of_string "abd" in
  assert_true ~msg:"compare less" (compare a b < 0)

let () =
  let a = of_string "xyz" in
  let b = of_string "abc" in
  assert_true ~msg:"compare greater" (compare a b > 0)

let () =
  let a = of_string "abc" in
  let b = of_string "abc" in
  assert_true ~msg:"compare equal" (compare a b = 0)

(* ============================================================ *)
(* Balancing                                                     *)
(* ============================================================ *)
let () =
  let r = of_string "hello" in
  assert_true ~msg:"small rope is balanced" (is_balanced r)

let () =
  (* Build a degenerate right-leaning rope *)
  let r = ref empty in
  for i = 0 to 99 do
    r := concat !r (of_string (String.make 1 (Char.chr (65 + (i mod 26)))))
  done;
  let orig_depth = depth !r in
  let balanced = balance !r in
  assert_true ~msg:"balanced rope has less depth" (depth balanced <= orig_depth);
  assert_true ~msg:"balanced content matches" (equal !r balanced);
  assert_true ~msg:"balanced rope is balanced" (is_balanced balanced)

(* ============================================================ *)
(* Edge cases                                                    *)
(* ============================================================ *)

(* Single character *)
let () =
  let r = of_string "x" in
  assert_equal ~msg:"single char length" "1" (string_of_int (length r));
  assert_equal ~msg:"single char index" "x" (String.make 1 (index r 0));
  assert_equal ~msg:"single char to_string" "x" (to_string r)

(* Deeply nested concats *)
let () =
  let r = ref (of_string "a") in
  for _ = 1 to 50 do
    r := concat !r (of_string "b")
  done;
  assert_equal ~msg:"deep concat length" "51" (string_of_int (length !r));
  assert_true ~msg:"deep concat starts with a" (index !r 0 = 'a');
  assert_true ~msg:"deep concat ends with b" (index !r 50 = 'b')

(* Insert into empty *)
let () =
  let r = insert empty 0 "hello" in
  assert_equal ~msg:"insert into empty" "hello" (to_string r)

(* Delete everything *)
let () =
  let r = of_string "abc" in
  let r2 = delete r 0 3 in
  assert_equal ~msg:"delete everything" "" (to_string r2);
  assert_equal ~msg:"delete everything length" "0" (string_of_int (length r2))

(* Repeated split and concat preserves content *)
let () =
  let original = "the quick brown fox jumps over the lazy dog" in
  let r = of_string original in
  let (l, r2) = split r 10 in
  let rejoined = concat l r2 in
  assert_equal ~msg:"split/concat roundtrip" original (to_string rejoined)

(* ============================================================ *)
(* Summary                                                       *)
(* ============================================================ *)
let () =
  Printf.printf "\nRope tests: %d passed, %d failed, %d total\n"
    !tests_passed !tests_failed !tests_run;
  if !tests_failed > 0 then exit 1
