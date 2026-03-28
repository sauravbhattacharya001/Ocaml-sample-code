(* test_huffman.ml — Tests for Huffman coding implementation.
 *
 * Compile and run:
 *   ocamlfind ocamlopt -package str -linkpkg test_framework.ml huffman.ml test_huffman.ml -o test_huffman && ./test_huffman
 *
 * Or interpreted:
 *   #use "test_framework.ml";;
 *   #use "huffman.ml";;
 *   #use "test_huffman.ml";;
 *)

(* ---- helpers ---- *)

let has_prefix_property codes =
  (* Verify no code is a prefix of another — essential for Huffman *)
  let sorted = List.sort compare codes in
  let rec check = function
    | [] | [_] -> true
    | a :: (b :: _ as rest) ->
      let la = String.length a in
      let lb = String.length b in
      if la <= lb && String.sub b 0 la = a then false
      else check rest
  in
  check sorted

(* ---- suites ---- *)

let () = suite "char_frequencies" (fun () ->
  let f = char_frequencies "" in
  assert_true ~msg:"empty string yields empty freq list" (f = []);

  let f = char_frequencies "aaa" in
  assert_true ~msg:"single char freq" (f = [('a', 3)]);

  let f = char_frequencies "abcabc" in
  assert_true ~msg:"uniform frequencies length" (List.length f = 3);
  List.iter (fun (_, count) ->
    assert_true ~msg:"each char appears twice" (count = 2)
  ) f;

  let f = char_frequencies "aaabbc" in
  (* sorted by frequency ascending, then char *)
  let first_char, first_freq = List.hd f in
  assert_true ~msg:"lowest freq char first" (first_freq = 1 && first_char = 'c');
)

let () = suite "build_tree" (fun () ->
  assert_true ~msg:"empty freqs gives None" (build_tree [] = None);

  (match build_tree [('x', 5)] with
   | Some (Node _) -> assert_true ~msg:"single char wraps in Node" true
   | _ -> assert_true ~msg:"single char wraps in Node" false);

  (match build_tree [('a', 3); ('b', 2); ('c', 1)] with
   | Some tree ->
     let f = freq tree in
     assert_true ~msg:"root freq = sum of all" (f = 6)
   | None -> assert_true ~msg:"multi-char tree not None" false);
)

let () = suite "code_table — prefix-free" (fun () ->
  let texts = [
    "hello world";
    "aaaaaabbbbccd";
    "the quick brown fox jumps over the lazy dog";
    String.make 100 'z';
    "ab";
  ] in
  List.iter (fun text ->
    match build_tree_from_string text with
    | None -> ()
    | Some tree ->
      let tbl = build_code_table tree in
      let codes = Hashtbl.fold (fun _ code acc -> code :: acc) tbl [] in
      assert_true ~msg:("prefix-free property: " ^ String.sub text 0 (min 20 (String.length text)))
        (has_prefix_property codes);
      (* All codes are non-empty strings of 0/1 *)
      List.iter (fun code ->
        assert_true ~msg:"code is non-empty" (String.length code > 0);
        String.iter (fun c ->
          assert_true ~msg:"code contains only 0/1" (c = '0' || c = '1')
        ) code
      ) codes
  ) texts
)

let () = suite "encode / decode round-trip" (fun () ->
  let cases = [
    "";
    "a";
    "aaa";
    "ab";
    "hello world";
    "aaaaaabbbbccd";
    "the quick brown fox jumps over the lazy dog";
    String.init 256 (fun i -> Char.chr i);  (* all byte values *)
    String.make 1000 'x' ^ "y";            (* heavily skewed *)
  ] in
  List.iter (fun text ->
    let ok = verify_roundtrip text in
    assert_true ~msg:("round-trip: len=" ^ string_of_int (String.length text)) ok
  ) cases
)

let () = suite "decode with deserialized tree" (fun () ->
  let text = "huffman coding is fun" in
  match build_tree_from_string text with
  | None -> assert_true ~msg:"should build tree" false
  | Some tree ->
    let tbl = build_code_table tree in
    let bits = encode tbl text in
    let ser = serialize_tree tree in
    let tree2 = deserialize_tree ser in
    let decoded = decode tree2 bits in
    assert_true ~msg:"decode via deserialized tree" (decoded = text)
)

let () = suite "serialize / deserialize round-trip" (fun () ->
  let text = "abracadabra" in
  match build_tree_from_string text with
  | None -> assert_true ~msg:"tree exists" false
  | Some tree ->
    let ser = serialize_tree tree in
    let tree2 = deserialize_tree ser in
    (* Both trees should produce identical code tables *)
    let tbl1 = code_table_to_list (build_code_table tree) in
    let tbl2 = code_table_to_list (build_code_table tree2) in
    assert_true ~msg:"code tables match after deserialization"
      (List.length tbl1 = List.length tbl2 &&
       List.for_all2 (fun (c1, code1) (c2, code2) -> c1 = c2 && code1 = code2) tbl1 tbl2)
)

let () = suite "deserialize_tree errors" (fun () ->
  assert_raises ~msg:"empty input" (fun () -> ignore (deserialize_tree ""));
  assert_raises ~msg:"truncated leaf" (fun () -> ignore (deserialize_tree "L"));
  assert_raises ~msg:"invalid tag" (fun () -> ignore (deserialize_tree "X"));
)

let () = suite "compression_stats" (fun () ->
  let text = "aaaaaabbbbccd" in
  match build_tree_from_string text with
  | None -> assert_true ~msg:"tree exists" false
  | Some tree ->
    let tbl = build_code_table tree in
    let bits = encode tbl text in
    let stats = compression_stats text (String.length bits) tbl in
    assert_true ~msg:"original_bits = 8 * len" (stats.original_bits = String.length text * 8);
    assert_true ~msg:"encoded < original for skewed text" (stats.encoded_bits < stats.original_bits);
    assert_true ~msg:"ratio < 1" (stats.ratio < 1.0);
    assert_true ~msg:"savings > 0" (stats.savings_pct > 0.0);
    assert_true ~msg:"unique_chars = 4" (stats.unique_chars = 4);
    assert_true ~msg:"avg_code_length > 0" (stats.avg_code_length > 0.0);
)

let () = suite "encode_string convenience" (fun () ->
  let (bits, tree_opt) = encode_string "" in
  assert_true ~msg:"empty string -> empty bits" (bits = "");
  assert_true ~msg:"empty string -> None tree" (tree_opt = None);

  let text = "banana" in
  let (bits, tree_opt) = encode_string text in
  assert_true ~msg:"non-empty bits" (String.length bits > 0);
  (match tree_opt with
   | Some tree ->
     let decoded = decode tree bits in
     assert_true ~msg:"encode_string round-trip" (decoded = text)
   | None -> assert_true ~msg:"tree should exist" false);
)

let () = suite "lookup_code — missing char raises" (fun () ->
  match build_tree_from_string "abc" with
  | None -> assert_true ~msg:"tree exists" false
  | Some tree ->
    let tbl = build_code_table tree in
    assert_raises ~msg:"lookup missing char 'z'" (fun () -> ignore (lookup_code tbl 'z'));
)

let () = suite "optimality — frequent chars get shorter codes" (fun () ->
  (* 'a' is most frequent, should get shortest (or equal shortest) code *)
  let text = String.make 100 'a' ^ String.make 10 'b' ^ "c" in
  match build_tree_from_string text with
  | None -> assert_true ~msg:"tree exists" false
  | Some tree ->
    let tbl = build_code_table tree in
    let code_a = Hashtbl.find tbl 'a' in
    let code_b = Hashtbl.find tbl 'b' in
    let code_c = Hashtbl.find tbl 'c' in
    assert_true ~msg:"a code <= b code length"
      (String.length code_a <= String.length code_b);
    assert_true ~msg:"b code <= c code length"
      (String.length code_b <= String.length code_c);
)

let () = test_summary ()
