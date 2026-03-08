(* test_free_monad.ml — tests for free_monad.ml *)
(* Run: ocaml free_monad.ml  (tests are inline) *)
(* This file provides additional integration tests via #use *)

#use "free_monad.ml";;

(* If we reach here, all inline tests passed.
   Add a few more integration-level checks. *)

let () = Printf.printf "Integration tests:\n"

(* Test: update combinator *)
let () =
  let open KVStoreDSL in
  let open KV in
  let prog =
    put "counter" "0" >>= fun () ->
    update "counter" (fun _ -> "1") >>= fun v1 ->
    update "counter" (fun old ->
      match old with Some n -> string_of_int (int_of_string n + 1) | None -> "0"
    ) >>= fun v2 ->
    pure (v1, v2)
  in
  let (v1, v2) = run_in_memory prog in
  assert (v1 = "1");
  assert (v2 = "2");
  Printf.printf "  ✓ KV update combinator chains correctly\n"

(* Test: Console error channel *)
let () =
  let open ConsoleDSL in
  let prog =
    let open Console in
    print_line "Starting..." >>= fun () ->
    print_error "Something went wrong" >>= fun () ->
    print_line "Continuing anyway" >>= fun () ->
    pure ()
  in
  let ((), result) = run_test [] prog in
  assert (result.outputs = ["Starting..."; "Continuing anyway"]);
  assert (result.errors = ["Something went wrong"]);
  Printf.printf "  ✓ Console separates stdout and stderr\n"

(* Test: Logger GetLogCount reflects actual count *)
let () =
  let open LogDSL in
  let open Logger in
  let prog =
    info "one" >>= fun () ->
    info "two" >>= fun () ->
    log_count () >>= fun c1 ->
    info "three" >>= fun () ->
    log_count () >>= fun c2 ->
    pure (c1, c2)
  in
  let ((c1, c2), _) = collect_logs prog in
  assert (c1 = 2);
  assert (c2 = 3);
  Printf.printf "  ✓ Logger count tracks correctly\n"

(* Test: Empty KV dry run *)
let () =
  let open KVStoreDSL in
  let prog = KV.pure 42 in
  let ops = dry_run prog in
  assert (ops = []);
  Printf.printf "  ✓ Dry run of pure is empty\n"

(* Test: Combined DSL retrieves stored value *)
let () =
  let open ConsoleKV in
  let open Combined in
  let prog =
    put "secret" "42" >>= fun () ->
    get "secret" >>= fun v ->
    print_line (match v with Some s -> "Got: " ^ s | None -> "Not found") >>= fun () ->
    pure v
  in
  let tbl = Hashtbl.create 4 in
  let (result, outputs, _) = run_test [] tbl prog in
  assert (result = Some "42");
  assert (outputs = ["Got: 42"]);
  Printf.printf "  ✓ Combined DSL round-trips values\n"

let () = Printf.printf "\nAll integration tests passed!\n"
