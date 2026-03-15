(* test_framework.ml — Shared test assertions for all test_*.ml files.
 *
 * Provides a lightweight assertion library with consistent output,
 * counters, and a summary printer. Designed to be loaded via:
 *
 *   #use "test_framework.ml";;
 *
 * or compiled alongside test files:
 *
 *   ocamlopt test_framework.ml test_foo.ml -o test_foo
 *
 * API:
 *   assert_true  ~msg condition        — pass if condition is true
 *   assert_false ~msg condition        — pass if condition is false
 *   assert_equal ~msg expected actual  — pass if expected = actual (strings)
 *   assert_raises ~msg f              — pass if f () raises any exception
 *   assert_float_eq ~msg ~eps a b     — pass if |a - b| < eps
 *   suite name f                      — run f () under suite name
 *   test_summary ()                   — print results, exit 1 if any failed
 *)

let tests_run    = ref 0
let tests_passed = ref 0
let tests_failed = ref 0
let current_suite = ref ""

let assert_true ~msg condition =
  incr tests_run;
  if condition then
    incr tests_passed
  else begin
    incr tests_failed;
    Printf.printf "  FAIL [%s] %s\n" !current_suite msg
  end

let assert_false ~msg condition =
  assert_true ~msg (not condition)

let assert_equal ~msg expected actual =
  incr tests_run;
  if expected = actual then
    incr tests_passed
  else begin
    incr tests_failed;
    Printf.printf "  FAIL [%s] %s: expected %s, got %s\n"
      !current_suite msg expected actual
  end

let assert_raises ~msg f =
  incr tests_run;
  (try
    ignore (f ());
    incr tests_failed;
    Printf.printf "  FAIL [%s] %s: expected exception, none raised\n"
      !current_suite msg
  with _ ->
    incr tests_passed)

let assert_float_eq ~msg ?(eps=1e-9) expected actual =
  incr tests_run;
  if Float.abs (expected -. actual) < eps then
    incr tests_passed
  else begin
    incr tests_failed;
    Printf.printf "  FAIL [%s] %s: expected %f, got %f (eps=%g)\n"
      !current_suite msg expected actual eps
  end

let suite name f =
  current_suite := name;
  Printf.printf "Running: %s\n" name;
  f ()

let test_summary () =
  Printf.printf "\n=== Results ===\n";
  Printf.printf "Total: %d | Passed: %d | Failed: %d\n"
    !tests_run !tests_passed !tests_failed;
  if !tests_failed > 0 then begin
    Printf.printf "STATUS: SOME TESTS FAILED\n";
    exit 1
  end else begin
    Printf.printf "STATUS: ALL TESTS PASSED\n";
    exit 0
  end
