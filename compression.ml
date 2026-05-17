(* compression.ml - LZ77 Compression & Decompression
 *
 * Implements the LZ77 sliding-window compression algorithm in pure OCaml.
 * Includes both compression and decompression, plus a CLI for compressing
 * and decompressing strings or files.
 *
 * Usage:
 *   ocaml compression.ml compress "hello hello hello"
 *   ocaml compression.ml decompress <encoded_string>
 *   ocaml compression.ml demo
 *   ocaml compression.ml bench <size>
 *)

(* --- LZ77 Token ---
 *
 * A token represents either a back-reference + a following literal byte,
 * or (for the last token in a stream) a back-reference with no trailing
 * literal. We model the trailing literal as [char option] so the compressor
 * can faithfully roundtrip any byte sequence, including ones containing
 * [\000]. Previously [\000] was abused as a sentinel for "no trailing
 * char", which silently corrupted inputs containing a real NUL byte.
 *)

type token = {
  offset : int;          (* how far back to look (0 if no match) *)
  length : int;          (* how many chars to copy from the window *)
  next   : char option;  (* literal byte after the match, or None at EOF *)
}

(* Hex-encode the trailing byte (or '-') so the textual serialization
   roundtrips for *every* byte value, including ')' and '\000' that
   would otherwise collide with the surrounding delimiters. *)
let token_to_string t =
  match t.next with
  | None   -> Printf.sprintf "(%d,%d,-)" t.offset t.length
  | Some c -> Printf.sprintf "(%d,%d,%02x)" t.offset t.length (Char.code c)

(* --- Compression --- *)

let compress ?(window_size=4096) ?(lookahead_size=18) input =
  if window_size < 0 then invalid_arg "compress: window_size must be >= 0";
  if lookahead_size < 1 then invalid_arg "compress: lookahead_size must be >= 1";
  let n = String.length input in
  let tokens = ref [] in
  let pos = ref 0 in
  while !pos < n do
    let search_start = max 0 (!pos - window_size) in
    let best_offset = ref 0 in
    let best_length = ref 0 in
    (* Search for the longest match in the sliding window. We cap the
       match at [lookahead_size] and leave at least one byte for the
       trailing literal (unless we are at EOF, in which case we'll emit
       [next = None]). *)
    let max_len = min lookahead_size (n - !pos - 1) in
    let max_len = max 0 max_len in
    let i = ref search_start in
    while !i < !pos do
      let len = ref 0 in
      while !len < max_len
            && !pos + !len < n
            && String.get input (!i + !len) = String.get input (!pos + !len) do
        incr len
      done;
      if !len > !best_length then begin
        best_length := !len;
        best_offset := !pos - !i
      end;
      incr i
    done;
    let next_opt =
      if !pos + !best_length < n then
        Some (String.get input (!pos + !best_length))
      else
        None
    in
    let consumed =
      !best_length + (match next_opt with Some _ -> 1 | None -> 0)
    in
    (* Safety: even if no progress would have been made (shouldn't happen
       because we always either match a literal or end the loop), force
       at least one byte of progress to avoid an infinite loop. *)
    let consumed = if consumed = 0 then 1 else consumed in
    tokens := { offset = !best_offset; length = !best_length; next = next_opt } :: !tokens;
    pos := !pos + consumed
  done;
  List.rev !tokens

(* --- Decompression --- *)

exception Corrupt_stream of string

let decompress tokens =
  let buf = Buffer.create 256 in
  List.iter (fun t ->
    if t.length < 0 then
      raise (Corrupt_stream (Printf.sprintf "negative length %d" t.length));
    if t.offset < 0 then
      raise (Corrupt_stream (Printf.sprintf "negative offset %d" t.offset));
    if t.length > 0 then begin
      if t.offset = 0 then
        raise (Corrupt_stream "length>0 but offset=0 (nothing to copy)");
      let start = Buffer.length buf - t.offset in
      if start < 0 then
        raise (Corrupt_stream
          (Printf.sprintf "offset %d exceeds buffer length %d"
             t.offset (Buffer.length buf)));
      (* Extract the source pattern once. When length > offset the
         pattern repeats (the classic LZ77 run-length trick), so we
         cycle through it with [i mod offset]. This avoids the old
         O(n^2) behaviour of calling Buffer.contents on every char. *)
      let pattern = Buffer.sub buf start t.offset in
      for i = 0 to t.length - 1 do
        Buffer.add_char buf pattern.[i mod t.offset]
      done
    end;
    (match t.next with
     | Some c -> Buffer.add_char buf c
     | None   -> ())
  ) tokens;
  Buffer.contents buf

(* --- Encoding tokens to/from strings --- *)

let encode_tokens tokens =
  let parts = List.map token_to_string tokens in
  String.concat "" parts

(* Parse a non-negative decimal integer starting at [!i]; advance [!i]
   past the digits and return its value. Stops at the first non-digit.  *)
let parse_int s i =
  let start = !i in
  let n = String.length s in
  while !i < n && s.[!i] >= '0' && s.[!i] <= '9' do incr i done;
  if !i = start then raise (Corrupt_stream "expected integer")
  else int_of_string (String.sub s start (!i - start))

let hex_digit c =
  match c with
  | '0'..'9' -> Char.code c - Char.code '0'
  | 'a'..'f' -> Char.code c - Char.code 'a' + 10
  | 'A'..'F' -> Char.code c - Char.code 'A' + 10
  | _ -> raise (Corrupt_stream (Printf.sprintf "bad hex digit %C" c))

let expect s i ch =
  if !i >= String.length s || s.[!i] <> ch then
    raise (Corrupt_stream (Printf.sprintf "expected %C at offset %d" ch !i));
  incr i

let decode_tokens s =
  let tokens = ref [] in
  let i = ref 0 in
  let n = String.length s in
  while !i < n do
    (* Skip any stray whitespace between tokens. *)
    while !i < n && (s.[!i] = ' ' || s.[!i] = '\n' || s.[!i] = '\t') do
      incr i
    done;
    if !i < n then begin
      expect s i '(';
      let offset = parse_int s i in
      expect s i ',';
      let length = parse_int s i in
      expect s i ',';
      let next =
        if !i < n && s.[!i] = '-' then begin
          incr i;
          None
        end else begin
          if !i + 1 >= n then raise (Corrupt_stream "truncated hex byte");
          let hi = hex_digit s.[!i] in
          let lo = hex_digit s.[!i + 1] in
          i := !i + 2;
          Some (Char.chr ((hi lsl 4) lor lo))
        end
      in
      expect s i ')';
      tokens := { offset; length; next } :: !tokens
    end
  done;
  List.rev !tokens

(* --- Statistics --- *)

let compression_ratio input tokens =
  let original = String.length input in
  (* Each token is roughly 3 ints worth; approximate encoded size *)
  let compressed = List.length tokens * 3 in
  if original = 0 then 1.0
  else float_of_int original /. float_of_int (max 1 compressed)

(* --- Demo --- *)

let demo () =
  let examples = [
    "abracadabra";
    "hello hello hello world world";
    "aaaaaaaaaaaaaaaa";
    "the quick brown fox jumps over the lazy dog";
    "abcabcabcabcabc";
    (* Edge-cases that the old encoding silently corrupted: *)
    "data with ) parens and , commas";
    "embedded\000nul\000bytes";
  ] in
  Printf.printf "=== LZ77 Compression Demo ===\n\n";
  List.iter (fun input ->
    let tokens = compress input in
    let decoded = decompress tokens in
    let ratio = compression_ratio input tokens in
    Printf.printf "Input:    %S\n" input;
    Printf.printf "Tokens:   %s\n" (encode_tokens tokens);
    Printf.printf "Decoded:  %S\n" decoded;
    Printf.printf "Ratio:    %.2fx (%d tokens for %d chars)\n" ratio (List.length tokens) (String.length input);
    Printf.printf "Match:    %s\n\n" (if input = decoded then "OK" else "MISMATCH!")
  ) examples

(* --- Benchmark --- *)

let bench size =
  (* Generate repetitive data that compresses well *)
  let pattern = "the quick brown fox " in
  let buf = Buffer.create size in
  while Buffer.length buf < size do
    Buffer.add_string buf pattern
  done;
  let input = Buffer.sub buf 0 size in
  let t0 = Sys.time () in
  let tokens = compress input in
  let t1 = Sys.time () in
  let decoded = decompress tokens in
  let t2 = Sys.time () in
  Printf.printf "=== LZ77 Benchmark (%d bytes) ===\n" size;
  Printf.printf "Compress:   %.4fs (%d tokens)\n" (t1 -. t0) (List.length tokens);
  Printf.printf "Decompress: %.4fs\n" (t2 -. t1);
  Printf.printf "Ratio:      %.2fx\n" (compression_ratio input tokens);
  Printf.printf "Correct:    %s\n" (if input = decoded then "OK" else "MISMATCH")

(* --- CLI --- *)

let () =
  if Array.length Sys.argv < 2 then begin
    Printf.printf "Usage: ocaml compression.ml <command> [args]\n";
    Printf.printf "Commands: compress <text>, decompress <encoded>, demo, bench <size>\n"
  end else
    match Sys.argv.(1) with
    | "compress" ->
      if Array.length Sys.argv < 3 then
        Printf.printf "Usage: ocaml compression.ml compress <text>\n"
      else begin
        let input = Sys.argv.(2) in
        let tokens = compress input in
        Printf.printf "%s\n" (encode_tokens tokens)
      end
    | "decompress" ->
      if Array.length Sys.argv < 3 then
        Printf.printf "Usage: ocaml compression.ml decompress <encoded>\n"
      else begin
        let encoded = Sys.argv.(2) in
        let tokens = decode_tokens encoded in
        Printf.printf "%s\n" (decompress tokens)
      end
    | "demo" -> demo ()
    | "bench" ->
      let size = if Array.length Sys.argv >= 3 then int_of_string Sys.argv.(2) else 10000 in
      bench size
    | cmd ->
      Printf.printf "Unknown command: %s\n" cmd
