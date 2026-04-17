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

(* --- LZ77 Token --- *)

type token = {
  offset : int;    (* how far back to look *)
  length : int;    (* how many chars to copy *)
  next   : char;   (* next literal character *)
}

let token_to_string t =
  Printf.sprintf "(%d,%d,%c)" t.offset t.length t.next

(* --- Compression --- *)

let compress ?(window_size=4096) ?(lookahead_size=18) input =
  let n = String.length input in
  let tokens = ref [] in
  let pos = ref 0 in
  while !pos < n do
    let search_start = max 0 (!pos - window_size) in
    let best_offset = ref 0 in
    let best_length = ref 0 in
    (* Search for longest match in the sliding window *)
    let i = ref search_start in
    while !i < !pos do
      let len = ref 0 in
      let max_len = min lookahead_size (n - !pos - 1) in
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
    let next_char =
      if !pos + !best_length < n then
        String.get input (!pos + !best_length)
      else
        '\000'
    in
    tokens := { offset = !best_offset; length = !best_length; next = next_char } :: !tokens;
    pos := !pos + !best_length + 1
  done;
  List.rev !tokens

(* --- Decompression --- *)

let decompress tokens =
  let buf = Buffer.create 256 in
  List.iter (fun t ->
    if t.length > 0 then begin
      let start = Buffer.length buf - t.offset in
      (* Extract the source pattern once.  When length > offset the
         pattern repeats (LZ77 run-length trick), so we cycle through
         it with [i mod offset].  This avoids the old code's O(n²)
         behavior of calling Buffer.contents on every character. *)
      let pattern = Buffer.sub buf start t.offset in
      for i = 0 to t.length - 1 do
        Buffer.add_char buf pattern.[i mod t.offset]
      done
    end;
    if t.next <> '\000' then
      Buffer.add_char buf t.next
  ) tokens;
  Buffer.contents buf

(* --- Encoding tokens to/from strings --- *)

let encode_tokens tokens =
  let parts = List.map token_to_string tokens in
  String.concat "" parts

let decode_tokens s =
  let tokens = ref [] in
  let i = ref 0 in
  let n = String.length s in
  while !i < n do
    if s.[!i] = '(' then begin
      incr i;
      (* read offset *)
      let off_start = !i in
      while !i < n && s.[!i] <> ',' do incr i done;
      let offset = int_of_string (String.sub s off_start (!i - off_start)) in
      incr i; (* skip comma *)
      (* read length *)
      let len_start = !i in
      while !i < n && s.[!i] <> ',' do incr i done;
      let length = int_of_string (String.sub s len_start (!i - len_start)) in
      incr i; (* skip comma *)
      (* read next char *)
      let next = s.[!i] in
      incr i; (* skip char *)
      incr i; (* skip ')' *)
      tokens := { offset; length; next } :: !tokens
    end else
      incr i
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
  ] in
  Printf.printf "=== LZ77 Compression Demo ===\n\n";
  List.iter (fun input ->
    let tokens = compress input in
    let decoded = decompress tokens in
    let ratio = compression_ratio input tokens in
    Printf.printf "Input:    \"%s\"\n" input;
    Printf.printf "Tokens:   %s\n" (encode_tokens tokens);
    Printf.printf "Decoded:  \"%s\"\n" decoded;
    Printf.printf "Ratio:    %.2fx (%d tokens for %d chars)\n" ratio (List.length tokens) (String.length input);
    Printf.printf "Match:    %s\n\n" (if input = decoded then "✓ OK" else "✗ MISMATCH!")
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
  Printf.printf "Correct:    %s\n" (if input = decoded then "✓" else "✗")

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
