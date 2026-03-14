(* crypto.ml — Classical Ciphers
   Demonstrates: string manipulation, modular arithmetic, higher-order
   functions, pattern matching, option types, ASCII encoding/decoding.

   Ciphers implemented:
   - ROT13 (special case of Caesar)
   - Caesar cipher (encrypt/decrypt with arbitrary shift)
   - Vigenère cipher (polyalphabetic substitution)
   - XOR cipher (byte-level symmetric encryption)
   - Rail Fence cipher (transposition cipher)
   - Frequency analysis (for breaking substitution ciphers)

   Compile: ocamlfind ocamlopt -package str -linkpkg crypto.ml -o crypto
   Run:     ./crypto
*)

(* ── Helpers ─────────────────────────────────────────────────────── *)

let is_alpha c = (c >= 'a' && c <= 'z') || (c >= 'A' && c <= 'Z')
let is_upper c = c >= 'A' && c <= 'Z'
let is_lower c = c >= 'a' && c <= 'z'

let char_shift base c n =
  let offset = Char.code c - Char.code base in
  let shifted = ((offset + n) mod 26 + 26) mod 26 in
  Char.chr (Char.code base + shifted)

let string_map_i f s =
  String.init (String.length s) (fun i -> f i s.[i])

(* ── ROT13 ───────────────────────────────────────────────────────── *)

let rot13_char c =
  if is_upper c then char_shift 'A' c 13
  else if is_lower c then char_shift 'a' c 13
  else c

let rot13 s = String.map rot13_char s

(* ── Caesar Cipher ───────────────────────────────────────────────── *)

let caesar_encrypt shift s =
  String.map (fun c ->
    if is_upper c then char_shift 'A' c shift
    else if is_lower c then char_shift 'a' c shift
    else c
  ) s

let caesar_decrypt shift s = caesar_encrypt (26 - (shift mod 26)) s

(* Brute-force all 26 Caesar shifts *)
let caesar_brute_force s =
  List.init 26 (fun shift -> (shift, caesar_decrypt shift s))

(* ── Vigenère Cipher ─────────────────────────────────────────────── *)

let vigenere_encrypt key plaintext =
  if String.length key = 0 then
    invalid_arg "vigenere_encrypt: key must not be empty"
  else
  let key_upper = String.uppercase_ascii key in
  let key_len = String.length key_upper in
  let ki = ref 0 in
  String.map (fun c ->
    if is_alpha c then begin
      let shift = Char.code key_upper.[!ki mod key_len] - Char.code 'A' in
      ki := !ki + 1;
      if is_upper c then char_shift 'A' c shift
      else char_shift 'a' c shift
    end else c
  ) plaintext

let vigenere_decrypt key ciphertext =
  if String.length key = 0 then
    invalid_arg "vigenere_decrypt: key must not be empty"
  else
  let key_upper = String.uppercase_ascii key in
  let inv_key = String.map (fun c ->
    Char.chr (Char.code 'A' + (26 - (Char.code c - Char.code 'A')) mod 26)
  ) key_upper in
  vigenere_encrypt inv_key ciphertext

(* ── XOR Cipher ──────────────────────────────────────────────────── *)

let xor_cipher key data =
  if String.length key = 0 then
    invalid_arg "xor_cipher: key must not be empty"
  else
    let key_len = String.length key in
    string_map_i (fun i c ->
      Char.chr (Char.code c lxor Char.code key.[i mod key_len])
    ) data

let bytes_to_hex s =
  let buf = Buffer.create (String.length s * 2) in
  String.iter (fun c -> Printf.bprintf buf "%02x" (Char.code c)) s;
  Buffer.contents buf

(** Convert a hex digit character to its integer value (0-15).
    Raises Invalid_argument for non-hex characters. *)
let hex_char_value c =
  if c >= '0' && c <= '9' then Char.code c - Char.code '0'
  else if c >= 'a' && c <= 'f' then 10 + Char.code c - Char.code 'a'
  else if c >= 'A' && c <= 'F' then 10 + Char.code c - Char.code 'A'
  else invalid_arg (Printf.sprintf "hex_to_bytes: invalid hex character '%c' (0x%02x)" c (Char.code c))

let hex_to_bytes hex =
  let hex_len = String.length hex in
  if hex_len mod 2 <> 0 then
    invalid_arg (Printf.sprintf "hex_to_bytes: odd-length hex string (%d chars)" hex_len)
  else
    let len = hex_len / 2 in
    String.init len (fun i ->
      let hi = hex_char_value hex.[i * 2] in
      let lo = hex_char_value hex.[i * 2 + 1] in
      Char.chr ((hi lsl 4) lor lo)
    )

(** Constant-time byte-string comparison.
    Prevents timing side-channel attacks when comparing secrets
    (e.g., MACs, password hashes, authentication tokens).
    Returns true iff [a] and [b] have the same length and contents. *)
let constant_time_equal a b =
  let len_a = String.length a in
  let len_b = String.length b in
  if len_a <> len_b then false
  else begin
    let diff = ref 0 in
    for i = 0 to len_a - 1 do
      diff := !diff lor (Char.code a.[i] lxor Char.code b.[i])
    done;
    !diff = 0
  end

(* ── Rail Fence Cipher ───────────────────────────────────────────── *)

let rail_fence_encrypt rails plaintext =
  if rails <= 1 then plaintext
  else begin
    let n = String.length plaintext in
    let rows = Array.make rails (Buffer.create 16) in
    Array.iteri (fun i _ -> rows.(i) <- Buffer.create (n / rails + 1)) rows;
    let rail = ref 0 in
    let dir = ref 1 in
    for i = 0 to n - 1 do
      Buffer.add_char rows.(!rail) plaintext.[i];
      if !rail = 0 then dir := 1
      else if !rail = rails - 1 then dir := -1;
      rail := !rail + !dir
    done;
    let result = Buffer.create n in
    Array.iter (fun b -> Buffer.add_buffer result b) rows;
    Buffer.contents result
  end

let rail_fence_decrypt rails ciphertext =
  if rails <= 1 then ciphertext
  else begin
    let n = String.length ciphertext in
    let pattern = Array.make n 0 in
    let rail = ref 0 in
    let dir = ref 1 in
    for i = 0 to n - 1 do
      pattern.(i) <- !rail;
      if !rail = 0 then dir := 1
      else if !rail = rails - 1 then dir := -1;
      rail := !rail + !dir
    done;
    let result = Array.make n ' ' in
    let ci = ref 0 in
    for r = 0 to rails - 1 do
      for i = 0 to n - 1 do
        if pattern.(i) = r then begin
          result.(i) <- ciphertext.[!ci];
          ci := !ci + 1
        end
      done
    done;
    String.init n (fun i -> result.(i))
  end

(* ── Frequency Analysis ──────────────────────────────────────────── *)

let frequency_analysis text =
  let counts = Array.make 26 0 in
  let total = ref 0 in
  String.iter (fun c ->
    if is_alpha c then begin
      let idx = Char.code (Char.lowercase_ascii c) - Char.code 'a' in
      counts.(idx) <- counts.(idx) + 1;
      incr total
    end
  ) text;
  if !total = 0 then [||]
  else begin
    let freqs = Array.init 26 (fun i ->
      (Char.chr (Char.code 'a' + i),
       float_of_int counts.(i) /. float_of_int !total *. 100.0)
    ) in
    (* Sort by frequency descending *)
    Array.sort (fun (_, a) (_, b) -> compare b a) freqs;
    freqs
  end

(* Guess Caesar shift by comparing most frequent letter to 'e' *)
let guess_caesar_shift ciphertext =
  let freqs = frequency_analysis ciphertext in
  if Array.length freqs = 0 then 0
  else begin
    let top_char, _ = freqs.(0) in
    (Char.code top_char - Char.code 'e' + 26) mod 26
  end

(* ── Atbash Cipher ───────────────────────────────────────────────── *)

let atbash c =
  if is_upper c then Char.chr (Char.code 'Z' - (Char.code c - Char.code 'A'))
  else if is_lower c then Char.chr (Char.code 'z' - (Char.code c - Char.code 'a'))
  else c

let atbash_cipher s = String.map atbash s

(* ── Demo ────────────────────────────────────────────────────────── *)

let () =
  let sep () = Printf.printf "\n%s\n\n" (String.make 60 '─') in

  (* ROT13 *)
  Printf.printf "🔐 Classical Ciphers in OCaml\n";
  sep ();
  Printf.printf "═══ ROT13 ═══\n";
  let msg = "Hello, World!" in
  let enc = rot13 msg in
  Printf.printf "  Original:  %s\n" msg;
  Printf.printf "  Encoded:   %s\n" enc;
  Printf.printf "  Decoded:   %s\n" (rot13 enc);
  Printf.printf "  Self-inverse: %b\n" (rot13 (rot13 msg) = msg);

  (* Caesar *)
  sep ();
  Printf.printf "═══ Caesar Cipher (shift=3) ═══\n";
  let msg = "The quick brown fox jumps over the lazy dog" in
  let enc = caesar_encrypt 3 msg in
  Printf.printf "  Plaintext:  %s\n" msg;
  Printf.printf "  Encrypted:  %s\n" enc;
  Printf.printf "  Decrypted:  %s\n" (caesar_decrypt 3 enc);

  Printf.printf "\n  Brute force (first 5 shifts):\n";
  let attempts = caesar_brute_force enc in
  List.iter (fun (shift, text) ->
    if shift < 5 then
      Printf.printf "    shift=%d: %s\n" shift text
  ) attempts;

  (* Frequency analysis *)
  sep ();
  Printf.printf "═══ Frequency Analysis ═══\n";
  let secret = caesar_encrypt 7 "In cryptography a substitution cipher is a method of encrypting in which units of plaintext are replaced with ciphertext" in
  Printf.printf "  Ciphertext: %s\n" secret;
  let guessed = guess_caesar_shift secret in
  Printf.printf "  Guessed shift: %d\n" guessed;
  Printf.printf "  Decrypted:  %s\n" (caesar_decrypt guessed secret);
  Printf.printf "\n  Letter frequencies (top 10):\n";
  let freqs = frequency_analysis secret in
  Array.iteri (fun i (c, pct) ->
    if i < 10 then Printf.printf "    '%c': %.1f%%\n" c pct
  ) freqs;

  (* Vigenère *)
  sep ();
  Printf.printf "═══ Vigenère Cipher (key=\"LEMON\") ═══\n";
  let msg = "Attack at dawn" in
  let key = "LEMON" in
  let enc = vigenere_encrypt key msg in
  Printf.printf "  Plaintext:  %s\n" msg;
  Printf.printf "  Key:        %s\n" key;
  Printf.printf "  Encrypted:  %s\n" enc;
  Printf.printf "  Decrypted:  %s\n" (vigenere_decrypt key enc);

  (* XOR *)
  sep ();
  Printf.printf "═══ XOR Cipher ═══\n";
  let msg = "Secret message" in
  let key = "key" in
  let enc = xor_cipher key msg in
  Printf.printf "  Plaintext:  %s\n" msg;
  Printf.printf "  Key:        %s\n" key;
  Printf.printf "  Hex:        %s\n" (bytes_to_hex enc);
  Printf.printf "  Decrypted:  %s\n" (xor_cipher key enc);
  Printf.printf "  Symmetric:  %b\n" (xor_cipher key (xor_cipher key msg) = msg);

  (* Rail Fence *)
  sep ();
  Printf.printf "═══ Rail Fence Cipher (3 rails) ═══\n";
  let msg = "WE ARE DISCOVERED FLEE AT ONCE" in
  let enc = rail_fence_encrypt 3 msg in
  Printf.printf "  Plaintext:  %s\n" msg;
  Printf.printf "  Encrypted:  %s\n" enc;
  Printf.printf "  Decrypted:  %s\n" (rail_fence_decrypt 3 enc);

  (* Atbash *)
  sep ();
  Printf.printf "═══ Atbash Cipher ═══\n";
  let msg = "Hello World" in
  let enc = atbash_cipher msg in
  Printf.printf "  Plaintext:  %s\n" msg;
  Printf.printf "  Encrypted:  %s\n" enc;
  Printf.printf "  Decrypted:  %s\n" (atbash_cipher enc);
  Printf.printf "  Self-inverse: %b\n" (atbash_cipher (atbash_cipher msg) = msg);

  sep ();
  (* --- Security: hex_to_bytes validation --- *)
  sep ();
  Printf.printf "\xf0\x9f\x94\x90 Security Tests\n";
  assert (hex_to_bytes "48656c6c6f" = "Hello");
  assert (hex_to_bytes "" = "");
  (try ignore (hex_to_bytes "zz"); assert false
   with Invalid_argument _ -> ());
  (try ignore (hex_to_bytes "abc"); assert false  (* odd length *)
   with Invalid_argument _ -> ());
  Printf.printf "  hex_to_bytes validation: OK\n";

  assert (constant_time_equal "secret" "secret");
  assert (not (constant_time_equal "secret" "Secret"));
  assert (not (constant_time_equal "short" "longer"));
  assert (constant_time_equal "" "");
  Printf.printf "  constant_time_equal: OK\n";

  sep ();
  Printf.printf "✅ All cipher demos complete!\n"
