(* test_crypto.ml — Tests for classical ciphers *)

let tests_passed = ref 0
let tests_failed = ref 0

let assert_eq name expected actual =
  if expected = actual then begin
    incr tests_passed;
    Printf.printf "  ✓ %s\n" name
  end else begin
    incr tests_failed;
    Printf.printf "  ✗ %s: expected '%s', got '%s'\n" name expected actual
  end

let assert_true name cond =
  if cond then begin
    incr tests_passed;
    Printf.printf "  ✓ %s\n" name
  end else begin
    incr tests_failed;
    Printf.printf "  ✗ %s: expected true\n" name
  end

(* Inline the functions for standalone compilation *)

let is_upper c = c >= 'A' && c <= 'Z'
let is_lower c = c >= 'a' && c <= 'z'
let is_alpha c = is_upper c || is_lower c

let char_shift base c n =
  let offset = Char.code c - Char.code base in
  let shifted = ((offset + n) mod 26 + 26) mod 26 in
  Char.chr (Char.code base + shifted)

let string_map_i f s =
  String.init (String.length s) (fun i -> f i s.[i])

let rot13_char c =
  if is_upper c then char_shift 'A' c 13
  else if is_lower c then char_shift 'a' c 13
  else c

let rot13 s = String.map rot13_char s

let caesar_encrypt shift s =
  String.map (fun c ->
    if is_upper c then char_shift 'A' c shift
    else if is_lower c then char_shift 'a' c shift
    else c) s

let caesar_decrypt shift s = caesar_encrypt (26 - (shift mod 26)) s

let vigenere_encrypt key plaintext =
  let key_upper = String.uppercase_ascii key in
  let key_len = String.length key_upper in
  let ki = ref 0 in
  String.map (fun c ->
    if is_alpha c then begin
      let shift = Char.code key_upper.[!ki mod key_len] - Char.code 'A' in
      ki := !ki + 1;
      if is_upper c then char_shift 'A' c shift
      else char_shift 'a' c shift
    end else c) plaintext

let vigenere_decrypt key ciphertext =
  let key_upper = String.uppercase_ascii key in
  let inv_key = String.map (fun c ->
    Char.chr (Char.code 'A' + (26 - (Char.code c - Char.code 'A')) mod 26)
  ) key_upper in
  vigenere_encrypt inv_key ciphertext

let xor_cipher key data =
  let key_len = String.length key in
  string_map_i (fun i c ->
    Char.chr (Char.code c lxor Char.code key.[i mod key_len])) data

let rail_fence_encrypt rails plaintext =
  if rails <= 1 then plaintext
  else begin
    let n = String.length plaintext in
    let rows = Array.init rails (fun _ -> Buffer.create (n / rails + 1)) in
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

let atbash c =
  if is_upper c then Char.chr (Char.code 'Z' - (Char.code c - Char.code 'A'))
  else if is_lower c then Char.chr (Char.code 'z' - (Char.code c - Char.code 'a'))
  else c

let atbash_cipher s = String.map atbash s

let () =
  Printf.printf "🧪 Crypto Tests\n\n";

  Printf.printf "ROT13:\n";
  assert_eq "basic" "Uryyb" (rot13 "Hello");
  assert_eq "self-inverse" "Hello" (rot13 (rot13 "Hello"));
  assert_eq "preserves non-alpha" "Uryyb, Jbeyq!" (rot13 "Hello, World!");
  assert_eq "empty" "" (rot13 "");

  Printf.printf "\nCaesar:\n";
  assert_eq "encrypt shift=3" "Khoor" (caesar_encrypt 3 "Hello");
  assert_eq "decrypt shift=3" "Hello" (caesar_decrypt 3 "Khoor");
  assert_eq "roundtrip" "Test 123!" (caesar_decrypt 17 (caesar_encrypt 17 "Test 123!"));
  assert_eq "shift=0 identity" "Hello" (caesar_encrypt 0 "Hello");
  assert_eq "shift=26 identity" "Hello" (caesar_encrypt 26 "Hello");

  Printf.printf "\nVigenère:\n";
  assert_eq "encrypt" "Lxfopv ef oapn" (vigenere_encrypt "LEMON" "Attack at dawn");
  assert_eq "decrypt" "Attack at dawn" (vigenere_decrypt "LEMON" "Lxfopv ef oapn");
  assert_eq "roundtrip" "Secret Message" (vigenere_decrypt "KEY" (vigenere_encrypt "KEY" "Secret Message"));

  Printf.printf "\nXOR:\n";
  assert_true "symmetric" (xor_cipher "k" (xor_cipher "k" "test") = "test");
  assert_true "roundtrip long key" (xor_cipher "longkey" (xor_cipher "longkey" "Hello World") = "Hello World");
  assert_eq "empty" "" (xor_cipher "key" "");

  Printf.printf "\nRail Fence:\n";
  assert_eq "encrypt 3 rails" "WECRLTEERDSOEEFEAOCAIVDEN" (rail_fence_encrypt 3 "WEAREDISCOVEREDFLEEATONCE");
  assert_eq "decrypt 3 rails" "WEAREDISCOVEREDFLEEATONCE" (rail_fence_decrypt 3 "WECRLTEERDSOEEFEAOCAIVDEN");
  assert_eq "1 rail identity" "Hello" (rail_fence_encrypt 1 "Hello");
  assert_eq "roundtrip 4 rails" "ABCDEFGH" (rail_fence_decrypt 4 (rail_fence_encrypt 4 "ABCDEFGH"));

  Printf.printf "\nAtbash:\n";
  assert_eq "basic" "Svool Dliow" (atbash_cipher "Hello World");
  assert_eq "self-inverse" "Hello World" (atbash_cipher (atbash_cipher "Hello World"));
  assert_eq "preserves non-alpha" "123!@#" (atbash_cipher "123!@#");

  Printf.printf "\n━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━\n";
  Printf.printf "Results: %d passed, %d failed\n" !tests_passed !tests_failed;
  if !tests_failed > 0 then exit 1
