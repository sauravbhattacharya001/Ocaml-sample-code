(* test_compression.ml - Tests for the LZ77 [compression.ml] implementation.
 *
 * Build & run:
 *   ocamlopt test_framework.ml compression.ml test_compression.ml \
 *       -o test_compression && ./test_compression
 *
 * Or interpreted:
 *   #use "test_framework.ml";;
 *   #use "compression.ml";;
 *   #use "test_compression.ml";;
 *
 * The tests focus on the contracts that callers actually rely on:
 *   - compress >> decompress is the identity for arbitrary byte strings
 *     (including ones with NUL bytes, parens, commas, and high bytes)
 *   - encode_tokens >> decode_tokens roundtrips losslessly
 *   - decompress raises [Corrupt_stream] on malformed input rather than
 *     [Division_by_zero] or [Invalid_argument "String.sub"]
 *)

(* When compiled (rather than #use'd), each .ml file becomes its own
   module. Bring [compress], [decompress], etc. (from compression.ml)
   and the assertion helpers (from test_framework.ml) into scope. *)
[@@@ocaml.warning "-33"]
open Test_framework
open Compression

(* ---- Helpers ---- *)

let roundtrip s =
  let toks = compress s in
  decompress toks

let serialize_roundtrip s =
  let toks = compress s in
  let encoded = encode_tokens toks in
  let toks' = decode_tokens encoded in
  decompress toks'

(* ---- Suites ---- *)

let () = suite "compress_decompress_basic" (fun () ->
  assert_equal ~msg:"empty string" "" (roundtrip "");
  assert_equal ~msg:"single char" "a" (roundtrip "a");
  assert_equal ~msg:"two chars" "ab" (roundtrip "ab");
  assert_equal ~msg:"all same"
    (String.make 32 'x') (roundtrip (String.make 32 'x'));
  assert_equal ~msg:"unique chars"
    "abcdefghij" (roundtrip "abcdefghij");
  assert_equal ~msg:"abracadabra"
    "abracadabra" (roundtrip "abracadabra");
  assert_equal ~msg:"longer phrase"
    "the quick brown fox jumps over the lazy dog"
    (roundtrip "the quick brown fox jumps over the lazy dog");
)

let () = suite "compress_decompress_repetition" (fun () ->
  (* Trigger the length>offset overlap path in [decompress]. *)
  assert_equal ~msg:"highly repetitive"
    (String.make 200 'q') (roundtrip (String.make 200 'q'));
  let pattern = "abcabcabcabcabc" in
  assert_equal ~msg:"overlapping pattern"
    pattern (roundtrip pattern);
  let big =
    let b = Buffer.create 2000 in
    for _ = 1 to 100 do Buffer.add_string b "the quick brown fox " done;
    Buffer.contents b
  in
  assert_equal ~msg:"long repetitive stream"
    big (roundtrip big);
)

(* These three were the originally reported bugs: NUL bytes were used as
   a sentinel, and ')' / '(' / ',' collided with the textual encoding. *)
let () = suite "compress_decompress_tricky_bytes" (fun () ->
  let with_nul = "embedded\000nul\000bytes" in
  assert_equal ~msg:"NUL bytes survive roundtrip"
    with_nul (roundtrip with_nul);

  let with_parens = "data with ) parens and , commas (and more)" in
  assert_equal ~msg:"parens & commas survive roundtrip"
    with_parens (roundtrip with_parens);

  (* All 256 byte values. *)
  let all_bytes = String.init 256 Char.chr in
  assert_equal ~msg:"all 256 byte values roundtrip"
    all_bytes (roundtrip all_bytes);

  (* End-of-input is exactly the trailing literal. *)
  assert_equal ~msg:"trailing NUL preserved"
    "abc\000" (roundtrip "abc\000");
  assert_equal ~msg:"trailing close-paren preserved"
    "abc)" (roundtrip "abc)");
)

let () = suite "encode_decode_tokens_roundtrip" (fun () ->
  let cases = [
    "";
    "a";
    "hello hello hello";
    "abracadabra";
    String.make 50 'z';
    "data with ) parens and , commas";
    "embedded\000nul\000bytes";
    String.init 256 Char.chr;
  ] in
  List.iter (fun s ->
    assert_equal
      ~msg:(Printf.sprintf "encode>decode>decompress on %S" s)
      s (serialize_roundtrip s)
  ) cases
)

let () = suite "compress_window_lookahead" (fun () ->
  let s = "abcdefabcdefabcdef" in
  (* Tiny window forces literal-only emission for the second copy. *)
  let toks_small = compress ~window_size:1 ~lookahead_size:1 s in
  assert_equal ~msg:"tiny window still roundtrips"
    s (decompress toks_small);
  (* Large window should find a back-reference. *)
  let toks_big = compress ~window_size:4096 ~lookahead_size:18 s in
  assert_true ~msg:"large window produces fewer tokens than bytes"
    (List.length toks_big < String.length s);
  assert_equal ~msg:"large window still roundtrips"
    s (decompress toks_big);
  assert_raises ~msg:"window_size < 0 rejected"
    (fun () -> compress ~window_size:(-1) "abc");
  assert_raises ~msg:"lookahead_size 0 rejected"
    (fun () -> compress ~lookahead_size:0 "abc");
)

let () = suite "decompress_rejects_malformed" (fun () ->
  (* offset=0, length>0 used to crash with Division_by_zero. *)
  assert_raises ~msg:"length>0 with offset=0 rejected"
    (fun () ->
      decompress [{ offset = 0; length = 5; next = Some 'a' }]);

  (* offset larger than the produced buffer used to crash with
     [Invalid_argument "String.sub / Bytes.sub"]. *)
  assert_raises ~msg:"offset exceeds buffer rejected"
    (fun () ->
      decompress [{ offset = 10; length = 1; next = Some 'a' }]);

  assert_raises ~msg:"negative length rejected"
    (fun () ->
      decompress [{ offset = 1; length = -3; next = None }]);

  assert_raises ~msg:"negative offset rejected"
    (fun () ->
      decompress [{ offset = -1; length = 1; next = None }]);
)

let () = suite "decode_tokens_rejects_malformed" (fun () ->
  assert_raises ~msg:"missing open paren"
    (fun () -> decode_tokens "0,0,2a)");
  assert_raises ~msg:"missing close paren"
    (fun () -> decode_tokens "(0,0,2a");
  assert_raises ~msg:"non-integer offset"
    (fun () -> decode_tokens "(xx,0,2a)");
  assert_raises ~msg:"bad hex digit"
    (fun () -> decode_tokens "(0,0,zz)");
  assert_raises ~msg:"truncated hex byte"
    (fun () -> decode_tokens "(0,0,2)");
)

let () = suite "decode_tokens_well_formed" (fun () ->
  let toks = decode_tokens "(0,0,61)(0,0,62)(0,0,-)" in
  assert_true ~msg:"three tokens parsed" (List.length toks = 3);
  assert_equal ~msg:"decompresses to 'ab'"
    "ab" (decompress toks);

  (* The decoder should tolerate whitespace between tokens (useful for
     pretty-printed dumps). *)
  let toks2 = decode_tokens "(0,0,61)\n(0,0,62)\n(0,0,-)" in
  assert_equal ~msg:"whitespace-tolerant" "ab" (decompress toks2);

  (* Hex byte uses lower-case in serialization; decoder also accepts upper. *)
  let toks3 = decode_tokens "(0,0,2A)" in
  assert_equal ~msg:"upper-case hex accepted"
    "*" (decompress toks3);
)

let () = suite "compression_ratio_sane" (fun () ->
  let r_empty = compression_ratio "" [] in
  assert_float_eq ~msg:"empty input -> 1.0" 1.0 r_empty;
  let s = String.make 1000 'a' in
  let toks = compress s in
  let r = compression_ratio s toks in
  assert_true ~msg:"highly compressible input has ratio > 1"
    (r > 1.0);
)

let () = test_summary ()
