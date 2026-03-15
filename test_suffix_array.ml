(* test_suffix_array.ml — Tests for Suffix Array module *)
(* Compile: ocamlopt suffix_array.ml test_suffix_array.ml -o test_sa *)

#use "test_framework.ml";;

let current_suite = ref ""

let assert_equal_int ~msg expected actual =
  incr tests_run;
  if expected = actual then incr tests_passed
  else begin incr tests_failed;
    Printf.printf "  FAIL [%s] %s: expected %d, got %d\n"
      !current_suite msg expected actual end

let assert_equal_str ~msg expected actual =
  incr tests_run;
  if expected = actual then incr tests_passed
  else begin incr tests_failed;
    Printf.printf "  FAIL [%s] %s: expected \"%s\", got \"%s\"\n"
      !current_suite msg expected actual end

let assert_list_equal ~msg expected actual =
  incr tests_run;
  if expected = actual then incr tests_passed
  else begin incr tests_failed;
    let show l = "[" ^ String.concat "; " (List.map string_of_int l) ^ "]" in
    Printf.printf "  FAIL [%s] %s: expected %s, got %s\n"
      !current_suite msg (show expected) (show actual) end

let assert_none ~msg opt =
  incr tests_run;
  match opt with None -> incr tests_passed
  | Some _ -> incr tests_failed;
    Printf.printf "  FAIL [%s] %s: expected None\n" !current_suite msg

let assert_some ~msg opt =
  incr tests_run;
  match opt with Some _ -> incr tests_passed
  | None -> incr tests_failed;
    Printf.printf "  FAIL [%s] %s: expected Some\n" !current_suite msg

let suite name f =
  current_suite := name;
  Printf.printf "Testing %s...\n" name; f ()

open Suffix_array

let test_build () = suite "Suffix Array Build" (fun () ->
  let sa = build "" in
  assert_equal_int ~msg:"empty length" 0 (Array.length sa);
  let sa = build "a" in
  assert_equal_int ~msg:"single length" 1 (Array.length sa);
  assert_equal_int ~msg:"single pos" 0 sa.(0);
  let sa = build "banana" in
  assert_equal_int ~msg:"banana length" 6 (Array.length sa);
  assert_equal_int ~msg:"banana sa[0]" 5 sa.(0);
  assert_equal_int ~msg:"banana sa[1]" 3 sa.(1);
  assert_equal_int ~msg:"banana sa[2]" 1 sa.(2);
  assert_equal_int ~msg:"banana sa[3]" 0 sa.(3);
  assert_equal_int ~msg:"banana sa[4]" 4 sa.(4);
  assert_equal_int ~msg:"banana sa[5]" 2 sa.(5);
  let sa = build "aaaa" in
  assert_equal_int ~msg:"aaaa sa[0]" 3 sa.(0);
  assert_equal_int ~msg:"aaaa sa[1]" 2 sa.(1);
  assert_equal_int ~msg:"aaaa sa[2]" 1 sa.(2);
  assert_equal_int ~msg:"aaaa sa[3]" 0 sa.(3);
  let sa = build "abcd" in
  assert_equal_int ~msg:"abcd sa[0]" 0 sa.(0);
  assert_equal_int ~msg:"abcd sa[1]" 1 sa.(1);
  assert_equal_int ~msg:"abcd sa[2]" 2 sa.(2);
  assert_equal_int ~msg:"abcd sa[3]" 3 sa.(3);
  let sa = build "dcba" in
  assert_equal_int ~msg:"dcba sa[0]" 3 sa.(0);
  assert_equal_int ~msg:"dcba sa[1]" 2 sa.(1);
  assert_equal_int ~msg:"dcba sa[2]" 1 sa.(2);
  assert_equal_int ~msg:"dcba sa[3]" 0 sa.(3);
  let text = "mississippi" in
  let sa = build text in
  let n = String.length text in
  for i = 0 to n - 2 do
    let s1 = String.sub text sa.(i) (n - sa.(i)) in
    let s2 = String.sub text sa.(i + 1) (n - sa.(i + 1)) in
    assert_true ~msg:(Printf.sprintf "sorted %d<%d" i (i+1))
      (String.compare s1 s2 < 0)
  done)

let test_lcp () = suite "LCP Array" (fun () ->
  let sa = build "" in
  let lcp = build_lcp "" sa in
  assert_equal_int ~msg:"empty" 0 (Array.length lcp);
  let sa = build "a" in
  let lcp = build_lcp "a" sa in
  assert_equal_int ~msg:"single" 0 lcp.(0);
  let t = "banana" in let sa = build t in let lcp = build_lcp t sa in
  assert_equal_int ~msg:"b lcp0" 0 lcp.(0);
  assert_equal_int ~msg:"b lcp1" 1 lcp.(1);
  assert_equal_int ~msg:"b lcp2" 3 lcp.(2);
  assert_equal_int ~msg:"b lcp3" 0 lcp.(3);
  assert_equal_int ~msg:"b lcp4" 0 lcp.(4);
  assert_equal_int ~msg:"b lcp5" 2 lcp.(5);
  let t = "aaaa" in let sa = build t in let lcp = build_lcp t sa in
  assert_equal_int ~msg:"a lcp0" 0 lcp.(0);
  assert_equal_int ~msg:"a lcp1" 1 lcp.(1);
  assert_equal_int ~msg:"a lcp2" 2 lcp.(2);
  assert_equal_int ~msg:"a lcp3" 3 lcp.(3);
  let t = "abcd" in let sa = build t in let lcp = build_lcp t sa in
  for i = 0 to 3 do
    assert_equal_int ~msg:(Printf.sprintf "abcd lcp[%d]" i) 0 lcp.(i)
  done)

let test_search () = suite "Pattern Search" (fun () ->
  let t = "banana" in let sa = build t in
  assert_list_equal ~msg:"ana" [1;3] (search t sa "ana");
  assert_list_equal ~msg:"a" [1;3;5] (search t sa "a");
  assert_list_equal ~msg:"ban" [0] (search t sa "ban");
  assert_list_equal ~msg:"banana" [0] (search t sa "banana");
  assert_list_equal ~msg:"nan" [2] (search t sa "nan");
  assert_list_equal ~msg:"xyz" [] (search t sa "xyz");
  assert_list_equal ~msg:"empty" [] (search t sa "");
  assert_list_equal ~msg:"longer" [] (search t sa "bananana");
  let t2 = "mississippi" in let sa2 = build t2 in
  assert_list_equal ~msg:"issi" [1;4] (search t2 sa2 "issi");
  assert_list_equal ~msg:"ss" [2;5] (search t2 sa2 "ss");
  assert_list_equal ~msg:"p" [8;9] (search t2 sa2 "p"))

let test_count () = suite "Count & Contains" (fun () ->
  let t = "abcabcabc" in let sa = build t in
  assert_equal_int ~msg:"abc" 3 (count t sa "abc");
  assert_equal_int ~msg:"cab" 2 (count t sa "cab");
  assert_equal_int ~msg:"xyz" 0 (count t sa "xyz");
  assert_equal_int ~msg:"a" 3 (count t sa "a");
  assert_equal_int ~msg:"empty" 0 (count t sa "");
  assert_true ~msg:"contains abc" (contains t sa "abc");
  assert_true ~msg:"not xyz" (not (contains t sa "xyz")))

let test_lrs () = suite "Longest Repeated Substring" (fun () ->
  let t = "banana" in let sa = build t in let lcp = build_lcp t sa in
  (match longest_repeated_substring t sa lcp with
   | None -> assert_true ~msg:"banana has repeat" false
   | Some (s,_,l) -> assert_equal_str ~msg:"banana lrs" "ana" s;
     assert_equal_int ~msg:"banana lrs len" 3 l);
  let t = "abcabcabc" in let sa = build t in let lcp = build_lcp t sa in
  (match longest_repeated_substring t sa lcp with
   | None -> assert_true ~msg:"abc3 has repeat" false
   | Some (s,_,l) -> assert_equal_str ~msg:"abc3 lrs" "abcabc" s;
     assert_equal_int ~msg:"abc3 lrs len" 6 l);
  let t = "abcd" in let sa = build t in let lcp = build_lcp t sa in
  assert_none ~msg:"abcd none" (longest_repeated_substring t sa lcp);
  let sa = build "" in let lcp = build_lcp "" sa in
  assert_none ~msg:"empty none" (longest_repeated_substring "" sa lcp);
  let t = "aaaa" in let sa = build t in let lcp = build_lcp t sa in
  assert_some ~msg:"aaaa some" (longest_repeated_substring t sa lcp);
  (match longest_repeated_substring t sa lcp with
   | Some (s,_,l) -> assert_equal_str ~msg:"aaaa lrs" "aaa" s;
     assert_equal_int ~msg:"aaaa len" 3 l | None -> ()))

let test_distinct () = suite "Distinct Substrings" (fun () ->
  let chk t e = let sa = build t in let lcp = build_lcp t sa in
    assert_equal_int ~msg:(t^" distinct") e (count_distinct_substrings t sa lcp) in
  chk "a" 1; chk "ab" 3; chk "aa" 2; chk "abc" 6;
  let sa = build "" in let lcp = build_lcp "" sa in
  assert_equal_int ~msg:"empty" 0 (count_distinct_substrings "" sa lcp))

let test_kth () = suite "K-th Substring" (fun () ->
  let t = "abc" in let sa = build t in let lcp = build_lcp t sa in
  (match kth_substring t sa lcp 1 with Some s -> assert_equal_str ~msg:"1st" "a" s
   | None -> assert_true ~msg:"1st exists" false);
  (match kth_substring t sa lcp 2 with Some s -> assert_equal_str ~msg:"2nd" "ab" s
   | None -> assert_true ~msg:"2nd exists" false);
  (match kth_substring t sa lcp 3 with Some s -> assert_equal_str ~msg:"3rd" "abc" s
   | None -> assert_true ~msg:"3rd exists" false);
  (match kth_substring t sa lcp 4 with Some s -> assert_equal_str ~msg:"4th" "b" s
   | None -> assert_true ~msg:"4th exists" false);
  (match kth_substring t sa lcp 6 with Some s -> assert_equal_str ~msg:"6th" "c" s
   | None -> assert_true ~msg:"6th exists" false);
  assert_none ~msg:"7th" (kth_substring t sa lcp 7);
  assert_none ~msg:"0th" (kth_substring t sa lcp 0);
  assert_none ~msg:"neg" (kth_substring t sa lcp (-1)))

let test_bwt () = suite "BWT" (fun () ->
  let t = "banana" in let sa = build t in let b = bwt t sa in
  assert_equal_int ~msg:"bwt len" 6 (String.length b);
  let st = String.to_seq t |> List.of_seq |> List.sort compare in
  let sb = String.to_seq b |> List.of_seq |> List.sort compare in
  assert_true ~msg:"bwt chars" (st = sb);
  let b = bwt "" (build "") in assert_equal_str ~msg:"bwt empty" "" b)

let test_edge () = suite "Edge Cases" (fun () ->
  let sa = build "ab" in
  assert_equal_int ~msg:"ab[0]" 0 sa.(0);
  assert_equal_int ~msg:"ab[1]" 1 sa.(1);
  let t = "a" in let sa = build t in let lcp = build_lcp t sa in
  assert_none ~msg:"single no repeat" (longest_repeated_substring t sa lcp);
  let t = "ababababab" in let sa = build t in
  assert_equal_int ~msg:"ab x5" 5 (count t sa "ab");
  assert_equal_int ~msg:"ba x4" 4 (count t sa "ba");
  assert_equal_int ~msg:"abab x4" 4 (count t sa "abab");
  let t = "xyzxyz" in let sa = build t in
  assert_list_equal ~msg:"xyz pos" [0;3] (search t sa "xyz");
  assert_list_equal ~msg:"z pos" [2;5] (search t sa "z"))

let () =
  Printf.printf "\n=== Suffix Array Test Suite ===\n\n";
  test_build (); test_lcp (); test_search (); test_count ();
  test_lrs (); test_distinct (); test_kth (); test_bwt (); test_edge ();
  test_summary ()