(* test_gap_buffer.ml — Tests for the Gap Buffer module *)
(* Run: ocaml test_gap_buffer.ml *)

#use "test_framework.ml";;
#use "gap_buffer.ml";;

open GapBuffer

let () = Printf.printf "Testing Gap Buffer...\n"

(* ============================================================ *)
(* Construction & basic queries                                 *)
(* ============================================================ *)
let () =
  let b = create () in
  assert_true  ~msg:"create: empty" (is_empty b);
  assert_equal ~msg:"create: length 0" "0" (string_of_int (length b));
  assert_equal ~msg:"create: cursor 0" "0" (string_of_int (cursor b));
  assert_equal ~msg:"create: to_string empty" "" (to_string b)

let () =
  let b = of_string "hello" in
  assert_false ~msg:"of_string: not empty" (is_empty b);
  assert_equal ~msg:"of_string: length" "5" (string_of_int (length b));
  assert_equal ~msg:"of_string: text" "hello" (to_string b);
  (* cursor lands at the end of the document *)
  assert_equal ~msg:"of_string: cursor at end" "5" (string_of_int (cursor b))

let () =
  let b = of_string "" in
  assert_true  ~msg:"of_string empty: empty" (is_empty b);
  assert_equal ~msg:"of_string empty: text" "" (to_string b)

(* ============================================================ *)
(* Insertion at the cursor                                      *)
(* ============================================================ *)
let () =
  let b = create () in
  insert_char b 'a';
  insert_char b 'b';
  insert_char b 'c';
  assert_equal ~msg:"insert_char: text" "abc" (to_string b);
  assert_equal ~msg:"insert_char: cursor" "3" (string_of_int (cursor b))

let () =
  let b = create () in
  insert_string b "hello";
  assert_equal ~msg:"insert_string: text" "hello" (to_string b);
  assert_equal ~msg:"insert_string: cursor" "5" (string_of_int (cursor b))

let () =
  let b = create () in
  insert_string b "";
  assert_equal ~msg:"insert_string empty: text" "" (to_string b);
  assert_equal ~msg:"insert_string empty: cursor" "0" (string_of_int (cursor b))

(* insert in the middle after moving the cursor *)
let () =
  let b = of_string "world" in
  move_to_start b;
  insert_string b "hello ";
  assert_equal ~msg:"insert at start: text" "hello world" (to_string b);
  assert_equal ~msg:"insert at start: cursor after inserted" "6"
    (string_of_int (cursor b))

let () =
  let b = of_string "helloworld" in
  move_to b 5;
  insert_char b ' ';
  assert_equal ~msg:"insert in middle: text" "hello world" (to_string b)

(* ============================================================ *)
(* Cursor movement                                              *)
(* ============================================================ *)
let () =
  let b = of_string "abcde" in
  move_to_start b;
  assert_equal ~msg:"move_to_start: cursor" "0" (string_of_int (cursor b));
  assert_equal ~msg:"move_to_start: text intact" "abcde" (to_string b);
  move_to_end b;
  assert_equal ~msg:"move_to_end: cursor" "5" (string_of_int (cursor b));
  assert_equal ~msg:"move_to_end: text intact" "abcde" (to_string b)

let () =
  let b = of_string "abcde" in
  move_to_start b;
  move_right b;
  move_right b;
  assert_equal ~msg:"move_right: cursor" "2" (string_of_int (cursor b));
  move_left b;
  assert_equal ~msg:"move_left: cursor" "1" (string_of_int (cursor b))

(* clamping: moving past the ends is a clamp, not a crash *)
let () =
  let b = of_string "ab" in
  move_to b (-5);
  assert_equal ~msg:"move_to clamp low" "0" (string_of_int (cursor b));
  move_to b 999;
  assert_equal ~msg:"move_to clamp high" "2" (string_of_int (cursor b));
  move_to_start b;
  move_left b;  (* already at start, stays put *)
  assert_equal ~msg:"move_left at start clamps" "0" (string_of_int (cursor b))

(* round-trip: moving the cursor never changes the text *)
let () =
  let b = of_string "the quick brown fox" in
  move_to b 4;
  move_to b 0;
  move_to b 19;
  move_to b 10;
  assert_equal ~msg:"movement preserves text" "the quick brown fox" (to_string b)

(* ============================================================ *)
(* Deletion                                                     *)
(* ============================================================ *)
let () =
  let b = of_string "hello" in
  (* cursor at end -> backspace removes 'o' *)
  assert_true  ~msg:"delete_before returns true" (delete_before b);
  assert_equal ~msg:"delete_before: text" "hell" (to_string b);
  assert_equal ~msg:"delete_before: cursor moved" "4" (string_of_int (cursor b))

let () =
  let b = of_string "hello" in
  move_to_start b;
  assert_false ~msg:"delete_before at start returns false" (delete_before b);
  assert_equal ~msg:"delete_before at start: text unchanged" "hello" (to_string b)

let () =
  let b = of_string "hello" in
  move_to_start b;
  assert_true  ~msg:"delete_after returns true" (delete_after b);
  assert_equal ~msg:"delete_after: text" "ello" (to_string b);
  assert_equal ~msg:"delete_after: cursor stays" "0" (string_of_int (cursor b))

let () =
  let b = of_string "hello" in
  (* cursor at end -> nothing to forward-delete *)
  assert_false ~msg:"delete_after at end returns false" (delete_after b)

let () =
  let b = of_string "hello world" in
  move_to_start b;
  let n = delete b 6 in
  assert_equal ~msg:"delete n: count" "6" (string_of_int n);
  assert_equal ~msg:"delete n: text" "world" (to_string b)

let () =
  let b = of_string "abc" in
  move_to_start b;
  let n = delete b 100 in  (* over-delete is clamped *)
  assert_equal ~msg:"delete over-count clamps" "3" (string_of_int n);
  assert_true  ~msg:"delete all -> empty" (is_empty b)

let () =
  let b = of_string "abcdef" in
  let n = delete_range b 2 3 in
  assert_equal ~msg:"delete_range: count" "3" (string_of_int n);
  assert_equal ~msg:"delete_range: text" "abf" (to_string b)

let () =
  let b = of_string "abc" in
  clear b;
  assert_true  ~msg:"clear: empty" (is_empty b);
  assert_equal ~msg:"clear: text" "" (to_string b);
  (* still usable after clear *)
  insert_string b "xyz";
  assert_equal ~msg:"usable after clear" "xyz" (to_string b)

(* ============================================================ *)
(* Random access: char_at / sub                                *)
(* ============================================================ *)
let () =
  let b = of_string "hello" in
  move_to b 2;  (* gap sits in the middle so both branches of phys_index run *)
  assert_equal ~msg:"char_at 0" "h" (String.make 1 (char_at b 0));
  assert_equal ~msg:"char_at 4" "o" (String.make 1 (char_at b 4));
  assert_raises ~msg:"char_at oob high" (fun () -> char_at b 5);
  assert_raises ~msg:"char_at oob low"  (fun () -> char_at b (-1))

let () =
  let b = of_string "hello world" in
  move_to b 6;
  assert_equal ~msg:"sub spanning gap" "lo wo" (sub b 3 5);
  assert_equal ~msg:"sub at start" "hello" (sub b 0 5);
  assert_equal ~msg:"sub empty" "" (sub b 2 0);
  assert_raises ~msg:"sub oob" (fun () -> sub b 8 10)

(* ============================================================ *)
(* iter / fold                                                  *)
(* ============================================================ *)
let () =
  let b = of_string "abc" in
  move_to b 1;
  let buf = Buffer.create 4 in
  iter (fun c -> Buffer.add_char buf c) b;
  assert_equal ~msg:"iter visits text in order" "abc" (Buffer.contents buf)

let () =
  let b = of_string "abcd" in
  move_to b 2;
  let count = fold_left (fun acc _ -> acc + 1) 0 b in
  assert_equal ~msg:"fold_left counts chars" "4" (string_of_int count);
  let concat = fold_left (fun acc c -> acc ^ String.make 1 c) "" b in
  assert_equal ~msg:"fold_left concatenates" "abcd" concat

(* ============================================================ *)
(* Search                                                       *)
(* ============================================================ *)
let () =
  let b = of_string "the quick brown fox" in
  (match find b "quick" with
   | Some i -> assert_equal ~msg:"find quick" "4" (string_of_int i)
   | None   -> assert_true ~msg:"find quick (should be Some)" false);
  (match find b "fox" with
   | Some i -> assert_equal ~msg:"find fox" "16" (string_of_int i)
   | None   -> assert_true ~msg:"find fox (should be Some)" false);
  assert_true ~msg:"find missing -> None" (find b "cat" = None);
  (* empty pattern matches at start position *)
  assert_true ~msg:"find empty pat -> Some 0" (find b "" = Some 0)

let () =
  let b = of_string "ababab" in
  (match find b "ab" with
   | Some i -> assert_equal ~msg:"find first ab" "0" (string_of_int i)
   | None   -> assert_true ~msg:"find ab (should be Some)" false);
  (match find ~start:1 b "ab" with
   | Some i -> assert_equal ~msg:"find ab from index 1" "2" (string_of_int i)
   | None   -> assert_true ~msg:"find ab from 1 (should be Some)" false)

(* search must be agnostic to where the gap currently sits *)
let () =
  let b = of_string "needle in haystack" in
  move_to b 3;
  (match find b "haystack" with
   | Some i -> assert_equal ~msg:"find across gap" "10" (string_of_int i)
   | None   -> assert_true ~msg:"find across gap (should be Some)" false)

(* ============================================================ *)
(* replace_all                                                  *)
(* ============================================================ *)
let () =
  let b = of_string "a-b-c-d" in
  let n = replace_all b "-" "_" in
  assert_equal ~msg:"replace_all: count" "3" (string_of_int n);
  assert_equal ~msg:"replace_all: text" "a_b_c_d" (to_string b)

let () =
  let b = of_string "aaaa" in
  let n = replace_all b "aa" "b" in  (* non-overlapping *)
  assert_equal ~msg:"replace_all non-overlap count" "2" (string_of_int n);
  assert_equal ~msg:"replace_all non-overlap text" "bb" (to_string b)

let () =
  let b = of_string "hello" in
  let n = replace_all b "xyz" "q" in
  assert_equal ~msg:"replace_all no match count" "0" (string_of_int n);
  assert_equal ~msg:"replace_all no match text" "hello" (to_string b)

let () =
  let b = of_string "cat" in
  let n = replace_all b "cat" "elephant" in  (* replacement longer than pat *)
  assert_equal ~msg:"replace_all grow count" "1" (string_of_int n);
  assert_equal ~msg:"replace_all grow text" "elephant" (to_string b);
  (* buffer remains fully functional after the internal rebuild *)
  move_to_end b;
  insert_char b '!';
  assert_equal ~msg:"usable after replace_all" "elephant!" (to_string b)

let () =
  let b = of_string "abc" in
  let n = replace_all b "" "x" in
  assert_equal ~msg:"replace_all empty pat count" "0" (string_of_int n);
  assert_equal ~msg:"replace_all empty pat text" "abc" (to_string b)

(* ============================================================ *)
(* Growth / capacity behaviour                                  *)
(* ============================================================ *)
let () =
  let b = create () in
  for i = 0 to 999 do
    insert_char b (Char.chr (Char.code 'a' + (i mod 26)))
  done;
  assert_equal ~msg:"growth: length" "1000" (string_of_int (length b));
  assert_true  ~msg:"growth: capacity grew" (capacity b >= 1000);
  assert_equal ~msg:"growth: to_string length" "1000"
    (string_of_int (String.length (to_string b)))

(* interleave inserts and cursor moves, the editor stress pattern *)
let () =
  let b = create () in
  insert_string b "0123456789";
  move_to b 5;
  insert_string b "XYZ";
  move_to b 0;
  insert_char b '<';
  move_to_end b;
  insert_char b '>';
  assert_equal ~msg:"interleaved edits" "<01234XYZ56789>" (to_string b);
  let (len, _cap, _gap, _cur) = stats b in
  assert_equal ~msg:"stats length matches" (string_of_int (String.length (to_string b)))
    (string_of_int len)

(* ============================================================ *)
(* to_string_with_cursor                                        *)
(* ============================================================ *)
let () =
  let b = of_string "hello" in
  move_to b 3;
  assert_equal ~msg:"cursor render mid" "hel|lo" (to_string_with_cursor b);
  move_to_start b;
  assert_equal ~msg:"cursor render start" "|hello" (to_string_with_cursor b);
  move_to_end b;
  assert_equal ~msg:"cursor render end" "hello|" (to_string_with_cursor b)

let () = test_summary ()
