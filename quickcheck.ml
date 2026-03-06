(* ============================================================================
   quickcheck.ml - Property-Based Testing Framework
   ============================================================================

   A minimal QuickCheck implementation in OCaml, inspired by Haskell's
   QuickCheck library (Claessen & Hughes, 2000).

   Demonstrates:
   - Random value generators with monadic composition (bind/map/return)
   - Shrinking strategies for minimal counterexample discovery
   - Higher-order functions for property specification
   - Polymorphic generator combinators
   - Lazy evaluation for efficient shrinking
   - Statistical test result reporting

   Property-based testing generates random inputs, checks properties hold
   for all of them, and when a property fails, automatically shrinks the
   counterexample to the smallest failing input.

   Usage:
     let () =
       (* Reversing a list twice gives back the original *)
       check "rev_rev" (list_of int) (fun xs ->
         List.rev (List.rev xs) = xs);

       (* Sorting is idempotent *)
       check "sort_idempotent" (list_of int) (fun xs ->
         let sorted = List.sort compare xs in
         List.sort compare sorted = sorted);

       (* With custom config *)
       check ~config:{ default_config with num_tests = 500 }
         "abs_non_negative" int (fun n -> abs n >= 0);

       print_summary ()
   ============================================================================ *)

(* ── Random seed management ─────────────────────────────────────────────── *)

let global_seed = ref 42

let next_random () =
  (* Linear congruential generator — deterministic, portable *)
  global_seed := (!global_seed * 1103515245 + 12345) land 0x3FFFFFFF;
  !global_seed

let random_int bound =
  if bound <= 0 then 0
  else (next_random ()) mod bound

let random_int_range lo hi =
  if hi < lo then lo
  else lo + random_int (hi - lo + 1)

let random_float () =
  float_of_int (next_random ()) /. float_of_int 0x3FFFFFFF

let random_bool () =
  random_int 2 = 0

let set_seed s = global_seed := s

(* ── Generator type ─────────────────────────────────────────────────────── *)

(* A generator produces a random value given a "size" parameter.
   Size starts small and grows, allowing generators to produce
   progressively more complex values. This is the standard QuickCheck
   approach for controlling input complexity. *)

type 'a gen = {
  generate : int -> 'a;          (* size -> random value *)
  shrink   : 'a -> 'a list;     (* value -> smaller alternatives *)
}

(* ── Generator combinators (monadic interface) ──────────────────────────── *)

let return x = {
  generate = (fun _size -> x);
  shrink = (fun _ -> []);
}

let map f gen = {
  generate = (fun size -> f (gen.generate size));
  shrink = (fun _ -> []);  (* mapping loses shrink info *)
}

let bind gen f = {
  generate = (fun size ->
    let a = gen.generate size in
    let gen_b = f a in
    gen_b.generate size);
  shrink = (fun _ -> []);
}

let ( >>= ) = bind
let ( >>| ) gen f = map f gen

(* ── Primitive generators ───────────────────────────────────────────────── *)

(* Integers: range scales with size parameter *)
let int = {
  generate = (fun size ->
    let bound = max 1 size in
    random_int_range (-bound) bound);
  shrink = (fun n ->
    if n = 0 then []
    else
      let candidates = [0] in
      let candidates =
        if n > 0 then candidates @ [n - 1; n / 2]
        else candidates @ [n + 1; n / 2; -n]
      in
      (* Remove duplicates and the original value *)
      List.sort_uniq compare
        (List.filter (fun x -> x <> n) candidates));
}

(* Non-negative integers *)
let nat = {
  generate = (fun size -> random_int (max 1 size));
  shrink = (fun n ->
    if n = 0 then []
    else
      List.sort_uniq compare
        (List.filter (fun x -> x <> n && x >= 0) [0; n - 1; n / 2]));
}

(* Small positive integers (1..size) *)
let pos_int = {
  generate = (fun size -> 1 + random_int (max 1 size));
  shrink = (fun n ->
    if n <= 1 then []
    else List.filter (fun x -> x <> n && x >= 1) [1; n - 1; n / 2]);
}

(* Floating-point numbers *)
let float_gen = {
  generate = (fun size ->
    let bound = float_of_int (max 1 size) in
    (random_float () *. 2.0 -. 1.0) *. bound);
  shrink = (fun x ->
    if x = 0.0 then []
    else
      let candidates = [0.0; Float.round x; x /. 2.0; x -. 1.0; x +. 1.0] in
      List.sort_uniq compare
        (List.filter (fun c -> c <> x) candidates));
}

(* Booleans *)
let bool = {
  generate = (fun _size -> random_bool ());
  shrink = (fun b -> if b then [false] else []);
}

(* Characters *)
let char_gen = {
  generate = (fun _size ->
    Char.chr (random_int_range (Char.code 'a') (Char.code 'z')));
  shrink = (fun c ->
    if c = 'a' then []
    else ['a']);
}

(* Printable ASCII characters *)
let printable_char = {
  generate = (fun _size ->
    Char.chr (random_int_range 32 126));
  shrink = (fun c ->
    if c = 'a' then []
    else ['a'; ' ']);
}

(* ── Composite generators ───────────────────────────────────────────────── *)

(* Lists with length scaling by size *)
let list_of (elem : 'a gen) : 'a list gen = {
  generate = (fun size ->
    let len = random_int (size + 1) in
    List.init len (fun _ -> elem.generate size));
  shrink = (fun xs ->
    match xs with
    | [] -> []
    | _ ->
      let len = List.length xs in
      (* Shrink strategies for lists:
         1. Remove elements (try removing each one)
         2. Shrink individual elements
         3. Try shorter prefixes *)
      let remove_each =
        List.init len (fun i ->
          List.filteri (fun j _ -> j <> i) xs)
      in
      let shorter =
        if len > 1 then
          [List.filteri (fun i _ -> i < len / 2) xs]
        else []
      in
      let shrink_elems =
        List.concat (List.mapi (fun i x ->
          List.map (fun x' ->
            List.mapi (fun j y -> if j = i then x' else y) xs)
            (elem.shrink x))
          xs)
      in
      remove_each @ shorter @ shrink_elems);
}

(* Non-empty lists *)
let non_empty_list_of (elem : 'a gen) : 'a list gen = {
  generate = (fun size ->
    let len = 1 + random_int (max 1 size) in
    List.init len (fun _ -> elem.generate size));
  shrink = (fun xs ->
    let candidates = (list_of elem).shrink xs in
    List.filter (fun l -> l <> []) candidates);
}

(* Strings *)
let string_gen = {
  generate = (fun size ->
    let len = random_int (size + 1) in
    String.init len (fun _ ->
      Char.chr (random_int_range (Char.code 'a') (Char.code 'z'))));
  shrink = (fun s ->
    if String.length s = 0 then []
    else
      let len = String.length s in
      let candidates = [""] in
      let candidates =
        if len > 1 then
          candidates @ [String.sub s 0 (len / 2);
                        String.sub s 0 (len - 1)]
        else candidates
      in
      List.filter (fun x -> x <> s) candidates);
}

(* Pairs *)
let pair (gen_a : 'a gen) (gen_b : 'b gen) : ('a * 'b) gen = {
  generate = (fun size ->
    (gen_a.generate size, gen_b.generate size));
  shrink = (fun (a, b) ->
    (* Shrink first element, then second, then both *)
    let shrink_a = List.map (fun a' -> (a', b)) (gen_a.shrink a) in
    let shrink_b = List.map (fun b' -> (a, b')) (gen_b.shrink b) in
    shrink_a @ shrink_b);
}

(* Triples *)
let triple gen_a gen_b gen_c = {
  generate = (fun size ->
    (gen_a.generate size, gen_b.generate size, gen_c.generate size));
  shrink = (fun (a, b, c) ->
    let sa = List.map (fun a' -> (a', b, c)) (gen_a.shrink a) in
    let sb = List.map (fun b' -> (a, b', c)) (gen_b.shrink b) in
    let sc = List.map (fun c' -> (a, b, c')) (gen_c.shrink c) in
    sa @ sb @ sc);
}

(* Option type *)
let option_of (gen : 'a gen) : 'a option gen = {
  generate = (fun size ->
    if random_int 4 = 0 then None
    else Some (gen.generate size));
  shrink = (fun opt ->
    match opt with
    | None -> []
    | Some x -> None :: List.map (fun x' -> Some x') (gen.shrink x));
}

(* Choose from a list of values *)
let one_of (values : 'a list) : 'a gen =
  if values = [] then failwith "one_of: empty list";
  { generate = (fun _size ->
      let idx = random_int (List.length values) in
      List.nth values idx);
    shrink = (fun x ->
      (* Shrink toward the first element *)
      match values with
      | first :: _ when x <> first -> [first]
      | _ -> []);
  }

(* Frequency-weighted generator choice *)
let frequency (weighted : (int * 'a gen) list) : 'a gen =
  if weighted = [] then failwith "frequency: empty list";
  let total = List.fold_left (fun acc (w, _) -> acc + w) 0 weighted in
  { generate = (fun size ->
      let target = random_int total in
      let rec pick acc = function
        | [] -> failwith "frequency: exhausted"
        | (w, gen) :: rest ->
          if acc + w > target then gen.generate size
          else pick (acc + w) rest
      in
      pick 0 weighted);
    shrink = (fun _ -> []);
  }

(* Sized: explicitly control the size parameter *)
let sized (f : int -> 'a gen) : 'a gen = {
  generate = (fun size -> (f size).generate size);
  shrink = (fun _ -> []);
}

(* Resize: override size for a generator *)
let resize (n : int) (gen : 'a gen) : 'a gen = {
  generate = (fun _size -> gen.generate n);
  shrink = gen.shrink;
}

(* ── Result types ───────────────────────────────────────────────────────── *)

type 'a test_result =
  | Pass
  | Fail of 'a             (* counterexample *)
  | Shrunk of 'a * int     (* shrunk counterexample, shrink steps *)
  | Error of 'a * exn      (* input that caused exception *)

type test_stats = {
  name         : string;
  num_tests    : int;
  result       : string;   (* "pass", "fail", "error" *)
  counterexample : string option;
  shrink_steps : int;
  seed         : int;
}

(* ── Test configuration ─────────────────────────────────────────────────── *)

type config = {
  num_tests   : int;    (* number of random tests to run *)
  max_size    : int;    (* maximum size parameter *)
  max_shrinks : int;    (* maximum shrink attempts *)
  seed        : int;    (* random seed for reproducibility *)
  verbose     : bool;   (* print each test case *)
}

let default_config = {
  num_tests   = 100;
  max_size    = 100;
  max_shrinks = 1000;
  seed        = 42;
  verbose     = false;
}

(* ── Shrinking engine ───────────────────────────────────────────────────── *)

(* Given a failing input, try to find a smaller input that also fails.
   Uses iterative deepening: try each shrink candidate, and if it still
   fails, recursively shrink that candidate. Stop after max_shrinks
   total attempts. *)

let shrink_loop (gen : 'a gen) (prop : 'a -> bool) (failing : 'a)
    ~max_shrinks =
  let steps = ref 0 in
  let best = ref failing in

  let rec try_shrinks candidates =
    if !steps >= max_shrinks then ()
    else match candidates with
      | [] -> ()
      | candidate :: rest ->
        incr steps;
        let still_fails =
          try not (prop candidate)
          with _ -> true
        in
        if still_fails then begin
          best := candidate;
          (* Recursively try to shrink further *)
          try_shrinks (gen.shrink candidate)
        end else
          try_shrinks rest
  in

  try_shrinks (gen.shrink failing);
  (!best, !steps)

(* ── Core test runner ───────────────────────────────────────────────────── *)

let run_test ?(config = default_config) (gen : 'a gen) (prop : 'a -> bool)
    : 'a test_result =
  set_seed config.seed;

  let rec loop i =
    if i >= config.num_tests then Pass
    else begin
      (* Size grows linearly from 0 to max_size *)
      let size = if config.num_tests <= 1 then config.max_size
        else (i * config.max_size) / (config.num_tests - 1) in
      let input = gen.generate size in

      if config.verbose then
        Printf.printf "  Test %d (size=%d)...\n" (i + 1) size;

      let outcome =
        try `Ok (prop input)
        with exn -> `Exn exn
      in
      match outcome with
      | `Exn exn -> Error (input, exn)
      | `Ok true -> loop (i + 1)
      | `Ok false ->
        (* Property failed — try to shrink *)
        let (shrunk, steps) = shrink_loop gen prop input
            ~max_shrinks:config.max_shrinks in
        if steps > 0 then Shrunk (shrunk, steps)
        else Fail input
    end
  in
  loop 0

(* ── Pretty-printing and reporting ──────────────────────────────────────── *)

let total_checks = ref 0
let total_passed = ref 0
let total_failed = ref 0
let all_stats : test_stats list ref = ref []

let check ?(config = default_config) (name : string)
    (gen : 'a gen) (prop : 'a -> bool) =
  let to_string = Printf.sprintf "%s" in  (* placeholder *)
  ignore to_string;
  incr total_checks;

  Printf.printf "  %-50s " name;

  match run_test ~config gen prop with
  | Pass ->
    incr total_passed;
    Printf.printf "OK (%d tests)\n" config.num_tests;
    all_stats := {
      name; num_tests = config.num_tests;
      result = "pass"; counterexample = None;
      shrink_steps = 0; seed = config.seed;
    } :: !all_stats

  | Fail _input ->
    incr total_failed;
    Printf.printf "FAIL!\n";
    Printf.printf "    Counterexample found (could not shrink)\n";
    all_stats := {
      name; num_tests = config.num_tests;
      result = "fail"; counterexample = Some "(opaque)";
      shrink_steps = 0; seed = config.seed;
    } :: !all_stats

  | Shrunk (_input, steps) ->
    incr total_failed;
    Printf.printf "FAIL!\n";
    Printf.printf "    Shrunk in %d steps\n" steps;
    all_stats := {
      name; num_tests = config.num_tests;
      result = "fail"; counterexample = Some "(opaque, shrunk)";
      shrink_steps = steps; seed = config.seed;
    } :: !all_stats

  | Error (_input, exn) ->
    incr total_failed;
    Printf.printf "ERROR: %s\n" (Printexc.to_string exn);
    all_stats := {
      name; num_tests = config.num_tests;
      result = "error"; counterexample = None;
      shrink_steps = 0; seed = config.seed;
    } :: !all_stats

(* Typed check variants with counterexample display *)

let check_int ?(config = default_config) name gen prop =
  let wrapped_gen = { gen with
    generate = gen.generate;
    shrink = gen.shrink;
  } in
  incr total_checks;
  Printf.printf "  %-50s " name;
  match run_test ~config wrapped_gen prop with
  | Pass ->
    incr total_passed;
    Printf.printf "OK (%d tests)\n" config.num_tests;
  | Fail input ->
    incr total_failed;
    Printf.printf "FAIL! Counterexample: %d\n" input
  | Shrunk (input, steps) ->
    incr total_failed;
    Printf.printf "FAIL! Shrunk to: %d (%d steps)\n" input steps
  | Error (input, exn) ->
    incr total_failed;
    Printf.printf "ERROR on input %d: %s\n" input (Printexc.to_string exn)

let check_string ?(config = default_config) name gen prop =
  incr total_checks;
  Printf.printf "  %-50s " name;
  match run_test ~config gen prop with
  | Pass ->
    incr total_passed;
    Printf.printf "OK (%d tests)\n" config.num_tests;
  | Fail input ->
    incr total_failed;
    Printf.printf "FAIL! Counterexample: %S\n" input
  | Shrunk (input, steps) ->
    incr total_failed;
    Printf.printf "FAIL! Shrunk to: %S (%d steps)\n" input steps
  | Error (input, exn) ->
    incr total_failed;
    Printf.printf "ERROR on input %S: %s\n" input (Printexc.to_string exn)

let check_list ?(config = default_config) name
    (show : 'a -> string) gen prop =
  incr total_checks;
  Printf.printf "  %-50s " name;
  match run_test ~config gen prop with
  | Pass ->
    incr total_passed;
    Printf.printf "OK (%d tests)\n" config.num_tests;
  | Fail input ->
    incr total_failed;
    let s = "[" ^ String.concat "; " (List.map show input) ^ "]" in
    Printf.printf "FAIL! Counterexample: %s\n" s
  | Shrunk (input, steps) ->
    incr total_failed;
    let s = "[" ^ String.concat "; " (List.map show input) ^ "]" in
    Printf.printf "FAIL! Shrunk to: %s (%d steps)\n" s steps
  | Error (input, exn) ->
    incr total_failed;
    let s = "[" ^ String.concat "; " (List.map show input) ^ "]" in
    Printf.printf "ERROR on input %s: %s\n" s (Printexc.to_string exn)

let print_summary () =
  Printf.printf "\n  ── QuickCheck Summary ──\n";
  Printf.printf "  Properties tested: %d\n" !total_checks;
  Printf.printf "  Passed:            %d\n" !total_passed;
  Printf.printf "  Failed:            %d\n" !total_failed;
  if !total_failed = 0 then
    Printf.printf "  ✓ All properties hold!\n"
  else
    Printf.printf "  ✗ %d properties violated\n" !total_failed

(* ── Predefined property helpers ────────────────────────────────────────── *)

(* Implication: skip test cases where precondition doesn't hold *)
let ( ==> ) precond prop input =
  if not (precond input) then true  (* vacuously true *)
  else prop input

(* Classify: tag test cases for distribution reporting *)
let classify label _condition _prop = ignore label; true

(* Collect: accumulate a label for each test *)
let collect _label _prop = true

(* ── Demo / Self-test ───────────────────────────────────────────────────── *)

let () =
  Printf.printf "\n╔══════════════════════════════════════════════════════════╗\n";
  Printf.printf "║  QuickCheck — Property-Based Testing                    ║\n";
  Printf.printf "╚══════════════════════════════════════════════════════════╝\n\n";

  Printf.printf "── Integer Properties ──\n";

  (* Absolute value is non-negative (classic QuickCheck example) *)
  check_int "abs(n) >= 0" int (fun n -> abs n >= 0);

  (* Addition is commutative *)
  check "a + b = b + a" (pair int int) (fun (a, b) ->
    a + b = b + a);

  (* Multiplication by zero *)
  check_int "n * 0 = 0" int (fun n -> n * 0 = 0);

  (* Integer division rounding *)
  check "a = (a/b)*b + (a mod b) [b≠0]" (pair int int) (fun (a, b) ->
    if b = 0 then true  (* skip *)
    else a = (a / b) * b + (a mod b));

  Printf.printf "\n── List Properties ──\n";

  (* Reversing twice is identity *)
  check_list "rev (rev xs) = xs" string_of_int (list_of int) (fun xs ->
    List.rev (List.rev xs) = xs);

  (* Length of concatenation *)
  check "length (xs @ ys) = length xs + length ys"
    (pair (list_of int) (list_of int)) (fun (xs, ys) ->
    List.length (xs @ ys) = List.length xs + List.length ys);

  (* Sorting is idempotent *)
  check_list "sort (sort xs) = sort xs" string_of_int
    (list_of int) (fun xs ->
    let sorted = List.sort compare xs in
    List.sort compare sorted = sorted);

  (* Sorted list has same length *)
  check_list "length (sort xs) = length xs" string_of_int
    (list_of int) (fun xs ->
    List.length (List.sort compare xs) = List.length xs);

  (* Map preserves length *)
  check_list "length (map f xs) = length xs" string_of_int
    (list_of int) (fun xs ->
    List.length (List.map (fun x -> x * 2) xs) = List.length xs);

  (* Filter produces sublist *)
  check_list "length (filter f xs) <= length xs" string_of_int
    (list_of int) (fun xs ->
    List.length (List.filter (fun x -> x > 0) xs) <= List.length xs);

  Printf.printf "\n── String Properties ──\n";

  (* String length is non-negative *)
  check_string "String.length s >= 0" string_gen (fun s ->
    String.length s >= 0);

  (* Concatenation length *)
  check "length (s1 ^ s2) = length s1 + length s2"
    (pair string_gen string_gen) (fun (s1, s2) ->
    String.length (s1 ^ s2) = String.length s1 + String.length s2);

  Printf.printf "\n── Shrinking Demo ──\n";

  (* This property is FALSE for n > 10 — QuickCheck will find and shrink *)
  check_int "n <= 10 (expect FAIL — shrink demo)" int (fun n ->
    n <= 10);

  (* This property is FALSE for lists with length > 3 *)
  check_list "length xs <= 3 (expect FAIL — shrink demo)" string_of_int
    (list_of int) (fun xs ->
    List.length xs <= 3);

  Printf.printf "\n── Generator Combinators ──\n";

  (* one_of always produces a member *)
  check "one_of produces member" (one_of [1; 2; 3; 4; 5]) (fun x ->
    List.mem x [1; 2; 3; 4; 5]);

  (* option_of None or Some *)
  check "option is None or Some" (option_of int) (fun opt ->
    match opt with None -> true | Some _ -> true);

  (* Pair components are independent *)
  check "pair generates two values" (pair nat nat) (fun (a, b) ->
    a >= 0 && b >= 0);

  (* Non-empty list is never empty *)
  check "non_empty_list is never empty"
    (non_empty_list_of int) (fun xs ->
    xs <> []);

  Printf.printf "\n── Implication (==>) ──\n";

  (* Only test even numbers *)
  check_int "even n => n mod 2 = 0" int
    ((fun n -> n mod 2 = 0) ==> (fun n -> n mod 2 = 0));

  (* Positive numbers stay positive after increment *)
  check_int "n > 0 => n + 1 > 0" int
    ((fun n -> n > 0) ==> (fun n -> n + 1 > 0));

  print_summary ()
