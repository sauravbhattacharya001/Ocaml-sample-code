(* free_monad.ml - Free Monads: Separating Description from Execution
 *
 * A free monad lets you describe a program as pure data (an AST of
 * operations), then interpret it in different ways — a real interpreter
 * that performs effects, a test interpreter that records them, a
 * pretty-printer that shows what *would* happen, etc.
 *
 * This is the "dependency injection" of functional programming:
 * your business logic never touches IO directly; it just emits
 * instructions.  The interpreter decides what those instructions mean.
 *
 * Concepts demonstrated:
 *   - GADTs (generalized algebraic data types) via encoding
 *   - Higher-kinded types via defunctionalisation
 *   - Continuation-passing style (CPS)
 *   - Monad laws and composition
 *   - Interpreter pattern (multiple backends for one DSL)
 *   - Separation of concerns (pure description vs effectful execution)
 *   - Functor/applicative/monad hierarchy
 *
 * Three example DSLs:
 *   1. Console DSL — read/write to terminal
 *   2. Key-Value Store DSL — get/put/delete
 *   3. Logging DSL — structured log messages
 *
 * Each DSL gets multiple interpreters showing the power of the pattern.
 *)


(* ══════════════════════════════════════════════════════════════════════
   Core Free Monad
   ══════════════════════════════════════════════════════════════════════ *)

(* A free monad is either:
   - Pure: a finished computation holding a value
   - Free: a suspended computation holding an instruction (functor)
           and a continuation for what to do next

   In Haskell: data Free f a = Pure a | Free (f (Free f a))
   
   In OCaml we don't have higher-kinded types directly, so we use
   a concrete approach: each DSL defines its own free monad type. *)

(* Generic free monad — we encode the "functor" as a variant type
   parameterised by the continuation's return type. *)

module type FUNCTOR = sig
  type 'a t
  val map : ('a -> 'b) -> 'a t -> 'b t
end

(* Build a free monad from any functor *)
module Free (F : FUNCTOR) = struct
  type 'a t =
    | Pure of 'a
    | Free of 'a t F.t

  let pure x = Pure x

  let rec map f = function
    | Pure x -> Pure (f x)
    | Free fx -> Free (F.map (map f) fx)

  (* Monadic bind — the heart of the free monad *)
  let rec bind m f = match m with
    | Pure x -> f x
    | Free fx -> Free (F.map (fun m' -> bind m' f) fx)

  (* Infix operators for readability *)
  let ( >>= ) = bind
  let ( >>| ) m f = map f m
  let ( >> ) m1 m2 = bind m1 (fun _ -> m2)

  (* Lift a single instruction into the free monad *)
  let lift_f (instruction : 'a F.t) : 'a t =
    Free (F.map pure instruction)

  (* Fold/interpret the free monad using a natural transformation *)
  let rec fold_free
    (interpret : 'a. 'a F.t -> 'a)
    (program : 'a t) : 'a =
    match program with
    | Pure x -> x
    | Free fx -> fold_free interpret (interpret fx)
end


(* ══════════════════════════════════════════════════════════════════════
   DSL 1: Console (Read/Write/Prompt)
   ══════════════════════════════════════════════════════════════════════ *)

module ConsoleDSL = struct

  (* The "functor" — each constructor is an instruction.
     The type parameter 'a represents "what comes next" (the continuation). *)
  type 'a instruction =
    | PrintLine of string * 'a         (* print a line, then continue with 'a *)
    | ReadLine of (string -> 'a)       (* read a line, pass it to continuation *)
    | PrintError of string * 'a        (* print to stderr, then continue *)

  (* Functor instance — map over the continuation *)
  module InstrF : FUNCTOR with type 'a t = 'a instruction = struct
    type 'a t = 'a instruction
    let map f = function
      | PrintLine (s, next) -> PrintLine (s, f next)
      | ReadLine cont -> ReadLine (fun s -> f (cont s))
      | PrintError (s, next) -> PrintError (s, f next)
  end

  (* Free monad over console instructions *)
  module Console = Free(InstrF)

  (* Smart constructors — these are what DSL users call *)
  let print_line s = Console.lift_f (PrintLine (s, ()))
  let read_line () = Console.lift_f (ReadLine (fun s -> s))
  let print_error s = Console.lift_f (PrintError (s, ()))

  (* ── Example program ─────────────────────────────────────────── *)

  (* A simple interactive program — pure data, no side effects! *)
  let greet_program =
    let open Console in
    print_line "What is your name?" >>= fun () ->
    read_line () >>= fun name ->
    print_line ("Hello, " ^ name ^ "!") >>= fun () ->
    print_line "How old are you?" >>= fun () ->
    read_line () >>= fun age ->
    print_line ("Wow, " ^ age ^ " is a great age!") >>= fun () ->
    pure name

  (* A program that asks for numbers and sums them *)
  let sum_program =
    let open Console in
    print_line "Enter first number:" >>= fun () ->
    read_line () >>= fun a ->
    print_line "Enter second number:" >>= fun () ->
    read_line () >>= fun b ->
    let sum = (int_of_string a) + (int_of_string b) in
    print_line ("Sum: " ^ string_of_int sum) >>= fun () ->
    pure sum

  (* ── Interpreter 1: Real IO ──────────────────────────────────── *)

  (* Actually performs the IO operations *)
  let rec run_io : type a. a Console.t -> a = function
    | Console.Pure x -> x
    | Console.Free (PrintLine (s, next)) ->
        print_endline s;
        run_io next
    | Console.Free (ReadLine cont) ->
        let line = input_line stdin in
        run_io (cont line)
    | Console.Free (PrintError (s, next)) ->
        Printf.eprintf "%s\n" s;
        run_io next

  (* ── Interpreter 2: Test/Mock ────────────────────────────────── *)

  (* Runs with pre-supplied inputs, collects all outputs *)
  type test_result = {
    outputs: string list;   (* lines printed *)
    errors: string list;    (* errors printed *)
    remaining_inputs: string list;
  }

  let rec run_test : type a. string list -> a Console.t -> a * test_result =
    fun inputs program ->
    match program with
    | Console.Pure x ->
        (x, { outputs = []; errors = []; remaining_inputs = inputs })
    | Console.Free (PrintLine (s, next)) ->
        let (result, state) = run_test inputs next in
        (result, { state with outputs = s :: state.outputs })
    | Console.Free (ReadLine cont) ->
        begin match inputs with
        | [] -> failwith "Test error: no more inputs available"
        | input :: rest ->
            run_test rest (cont input)
        end
    | Console.Free (PrintError (s, next)) ->
        let (result, state) = run_test inputs next in
        (result, { state with errors = s :: state.errors })

  (* ── Interpreter 3: Pretty-printer ──────────────────────────── *)

  (* Shows what the program *would* do, without executing anything *)
  let rec pretty_print : type a. int -> a Console.t -> string list =
    fun step program ->
    match program with
    | Console.Pure _ -> [Printf.sprintf "[Step %d] Done." step]
    | Console.Free (PrintLine (s, next)) ->
        Printf.sprintf "[Step %d] PRINT: %s" step s
        :: pretty_print (step + 1) next
    | Console.Free (ReadLine cont) ->
        Printf.sprintf "[Step %d] READ: <waiting for input>" step
        :: pretty_print (step + 1) (cont "<user-input>")
    | Console.Free (PrintError (s, next)) ->
        Printf.sprintf "[Step %d] ERROR: %s" step s
        :: pretty_print (step + 1) next

  let trace program = pretty_print 1 program

  (* ── Interpreter 4: Instruction counter ─────────────────────── *)

  (* Counts how many instructions a program uses *)
  let rec count_instructions : type a. a Console.t -> int = function
    | Console.Pure _ -> 0
    | Console.Free (PrintLine (_, next)) -> 1 + count_instructions next
    | Console.Free (ReadLine cont) -> 1 + count_instructions (cont "")
    | Console.Free (PrintError (_, next)) -> 1 + count_instructions next
end


(* ══════════════════════════════════════════════════════════════════════
   DSL 2: Key-Value Store
   ══════════════════════════════════════════════════════════════════════ *)

module KVStoreDSL = struct

  (* Instructions for a key-value store *)
  type 'a instruction =
    | Get of string * (string option -> 'a)     (* get key, pass result *)
    | Put of string * string * 'a               (* put key value, continue *)
    | Delete of string * 'a                     (* delete key, continue *)
    | Keys of (string list -> 'a)               (* list all keys *)

  module InstrF : FUNCTOR with type 'a t = 'a instruction = struct
    type 'a t = 'a instruction
    let map f = function
      | Get (k, cont) -> Get (k, fun v -> f (cont v))
      | Put (k, v, next) -> Put (k, v, f next)
      | Delete (k, next) -> Delete (k, f next)
      | Keys cont -> Keys (fun ks -> f (cont ks))
  end

  module KV = Free(InstrF)

  (* Smart constructors *)
  let get key = KV.lift_f (Get (key, fun v -> v))
  let put key value = KV.lift_f (Put (key, value, ()))
  let delete key = KV.lift_f (Delete (key, ()))
  let keys () = KV.lift_f (Keys (fun ks -> ks))

  (* Derived operations built from primitives *)
  let get_or_default key default_val =
    let open KV in
    get key >>= fun result ->
    pure (match result with Some v -> v | None -> default_val)

  let update key f =
    let open KV in
    get key >>= fun old_val ->
    let new_val = f old_val in
    put key new_val >>= fun () ->
    pure new_val

  let put_if_absent key value =
    let open KV in
    get key >>= fun existing ->
    match existing with
    | Some v -> pure v
    | None -> put key value >> pure value

  let swap key1 key2 =
    let open KV in
    get key1 >>= fun v1 ->
    get key2 >>= fun v2 ->
    (match v1 with Some v -> put key2 v | None -> delete key2) >>= fun () ->
    (match v2 with Some v -> put key1 v | None -> delete key1) >>= fun () ->
    pure ()

  (* ── Example programs ───────────────────────────────────────── *)

  (* Build a shopping cart *)
  let shopping_cart_program =
    let open KV in
    put "apples" "3" >>= fun () ->
    put "bananas" "5" >>= fun () ->
    put "oranges" "2" >>= fun () ->
    get "bananas" >>= fun banana_count ->
    let new_count = match banana_count with
      | Some n -> string_of_int (int_of_string n + 1)
      | None -> "1"
    in
    put "bananas" new_count >>= fun () ->
    delete "oranges" >>= fun () ->
    keys () >>= fun all_keys ->
    pure all_keys

  (* ── Interpreter 1: In-memory hashtable ─────────────────────── *)

  let rec run_hashtable : type a. (string, string) Hashtbl.t -> a KV.t -> a =
    fun tbl program ->
    match program with
    | KV.Pure x -> x
    | KV.Free (Get (k, cont)) ->
        let v = Hashtbl.find_opt tbl k in
        run_hashtable tbl (cont v)
    | KV.Free (Put (k, v, next)) ->
        Hashtbl.replace tbl k v;
        run_hashtable tbl next
    | KV.Free (Delete (k, next)) ->
        Hashtbl.remove tbl k;
        run_hashtable tbl next
    | KV.Free (Keys cont) ->
        let ks = Hashtbl.fold (fun k _ acc -> k :: acc) tbl [] in
        run_hashtable tbl (cont (List.sort compare ks))

  let run_in_memory program =
    let tbl = Hashtbl.create 16 in
    run_hashtable tbl program

  (* ── Interpreter 2: Logging/audit trail ─────────────────────── *)

  type audit_entry =
    | AGet of string * string option
    | APut of string * string
    | ADelete of string
    | AKeys of string list

  let rec run_with_audit : type a.
    (string, string) Hashtbl.t -> a KV.t -> a * audit_entry list =
    fun tbl program ->
    match program with
    | KV.Pure x -> (x, [])
    | KV.Free (Get (k, cont)) ->
        let v = Hashtbl.find_opt tbl k in
        let (result, log) = run_with_audit tbl (cont v) in
        (result, AGet (k, v) :: log)
    | KV.Free (Put (k, v, next)) ->
        Hashtbl.replace tbl k v;
        let (result, log) = run_with_audit tbl next in
        (result, APut (k, v) :: log)
    | KV.Free (Delete (k, next)) ->
        Hashtbl.remove tbl k;
        let (result, log) = run_with_audit tbl next in
        (result, ADelete k :: log)
    | KV.Free (Keys cont) ->
        let ks = Hashtbl.fold (fun k _ acc -> k :: acc) tbl [] in
        let sorted = List.sort compare ks in
        let (result, log) = run_with_audit tbl (cont sorted) in
        (result, AKeys sorted :: log)

  let run_audited program =
    let tbl = Hashtbl.create 16 in
    run_with_audit tbl program

  (* ── Interpreter 3: Dry-run (records operations without executing) *)

  type dry_run_op =
    | DryGet of string
    | DryPut of string * string
    | DryDelete of string
    | DryKeys

  let rec dry_run : type a. a KV.t -> dry_run_op list = function
    | KV.Pure _ -> []
    | KV.Free (Get (k, cont)) -> DryGet k :: dry_run (cont None)
    | KV.Free (Put (k, v, next)) -> DryPut (k, v) :: dry_run next
    | KV.Free (Delete (k, next)) -> DryDelete k :: dry_run next
    | KV.Free (Keys cont) -> DryKeys :: dry_run (cont [])

  (* Format dry-run ops as readable strings *)
  let format_dry_run ops =
    List.map (function
      | DryGet k -> Printf.sprintf "GET %s" k
      | DryPut (k, v) -> Printf.sprintf "PUT %s = %s" k v
      | DryDelete k -> Printf.sprintf "DELETE %s" k
      | DryKeys -> "KEYS"
    ) ops
end


(* ══════════════════════════════════════════════════════════════════════
   DSL 3: Structured Logging
   ══════════════════════════════════════════════════════════════════════ *)

module LogDSL = struct

  type level = Debug | Info | Warn | Error

  let level_to_string = function
    | Debug -> "DEBUG" | Info -> "INFO"
    | Warn -> "WARN"  | Error -> "ERROR"

  type 'a instruction =
    | Log of level * string * 'a
    | LogWithContext of level * string * (string * string) list * 'a
    | GetLogCount of (int -> 'a)

  module InstrF : FUNCTOR with type 'a t = 'a instruction = struct
    type 'a t = 'a instruction
    let map f = function
      | Log (lvl, msg, next) -> Log (lvl, msg, f next)
      | LogWithContext (lvl, msg, ctx, next) ->
          LogWithContext (lvl, msg, ctx, f next)
      | GetLogCount cont -> GetLogCount (fun n -> f (cont n))
  end

  module Logger = Free(InstrF)

  (* Smart constructors *)
  let debug msg = Logger.lift_f (Log (Debug, msg, ()))
  let info msg = Logger.lift_f (Log (Info, msg, ()))
  let warn msg = Logger.lift_f (Log (Warn, msg, ()))
  let error msg = Logger.lift_f (Log (Error, msg, ()))
  let log_with lvl msg ctx = Logger.lift_f (LogWithContext (lvl, msg, ctx, ()))
  let log_count () = Logger.lift_f (GetLogCount (fun n -> n))

  (* ── Example program ─────────────────────────────────────────── *)

  let processing_pipeline =
    let open Logger in
    info "Starting data pipeline" >>= fun () ->
    log_with Info "Loading dataset" [("source", "db"); ("table", "users")] >>= fun () ->
    debug "Parsed 1000 records" >>= fun () ->
    warn "Found 3 records with missing fields" >>= fun () ->
    log_with Info "Transformation complete" [("records", "997"); ("skipped", "3")] >>= fun () ->
    log_count () >>= fun count ->
    info (Printf.sprintf "Pipeline finished (%d log entries)" count) >>= fun () ->
    pure count

  (* ── Interpreter 1: Collect all logs ─────────────────────────── *)

  type log_entry = {
    level: level;
    message: string;
    context: (string * string) list;
  }

  let rec run_collect : type a. int -> a Logger.t -> a * log_entry list =
    fun count program ->
    match program with
    | Logger.Pure x -> (x, [])
    | Logger.Free (Log (lvl, msg, next)) ->
        let entry = { level = lvl; message = msg; context = [] } in
        let (result, rest) = run_collect (count + 1) next in
        (result, entry :: rest)
    | Logger.Free (LogWithContext (lvl, msg, ctx, next)) ->
        let entry = { level = lvl; message = msg; context = ctx } in
        let (result, rest) = run_collect (count + 1) next in
        (result, entry :: rest)
    | Logger.Free (GetLogCount cont) ->
        run_collect count (cont count)

  let collect_logs program = run_collect 0 program

  (* ── Interpreter 2: Filter by level ─────────────────────────── *)

  let level_value = function
    | Debug -> 0 | Info -> 1 | Warn -> 2 | Error -> 3

  let rec run_filtered : type a. level -> int -> a Logger.t -> a * log_entry list =
    fun min_level count program ->
    match program with
    | Logger.Pure x -> (x, [])
    | Logger.Free (Log (lvl, msg, next)) ->
        let (result, rest) = run_filtered min_level (count + 1) next in
        if level_value lvl >= level_value min_level then
          let entry = { level = lvl; message = msg; context = [] } in
          (result, entry :: rest)
        else
          (result, rest)
    | Logger.Free (LogWithContext (lvl, msg, ctx, next)) ->
        let (result, rest) = run_filtered min_level (count + 1) next in
        if level_value lvl >= level_value min_level then
          let entry = { level = lvl; message = msg; context = ctx } in
          (result, entry :: rest)
        else
          (result, rest)
    | Logger.Free (GetLogCount cont) ->
        run_filtered min_level count (cont count)

  let collect_filtered min_level program =
    run_filtered min_level 0 program

  (* ── Interpreter 3: Format as strings ────────────────────────── *)

  let format_entry entry =
    let base = Printf.sprintf "[%s] %s"
      (level_to_string entry.level) entry.message in
    match entry.context with
    | [] -> base
    | ctx ->
        let pairs = List.map (fun (k, v) -> k ^ "=" ^ v) ctx in
        base ^ " {" ^ String.concat ", " pairs ^ "}"

  let format_logs entries =
    List.map format_entry entries
end


(* ══════════════════════════════════════════════════════════════════════
   Composing Free Monads: Coproduct (Sum) of Functors
   ══════════════════════════════════════════════════════════════════════ *)

(* In real systems you want to combine DSLs — e.g., a program that does
   both console IO and key-value storage.  This is done by taking the
   coproduct (sum) of their instruction functors. *)

module Coproduct (F : FUNCTOR) (G : FUNCTOR) = struct
  type 'a t =
    | InL of 'a F.t
    | InR of 'a G.t

  let map f = function
    | InL x -> InL (F.map f x)
    | InR x -> InR (G.map f x)

  (* Interpret a coproduct by dispatching to the appropriate handler *)
  let fold (handle_f : 'a F.t -> 'a) (handle_g : 'a G.t -> 'a) = function
    | InL x -> handle_f x
    | InR x -> handle_g x
end

(* Example: Console + KVStore combined DSL *)
module ConsoleKV = struct
  module CopF = Coproduct(ConsoleDSL.InstrF)(KVStoreDSL.InstrF)
  module Combined = Free(CopF)

  (* Lift console instructions into the combined monad *)
  let print_line s = Combined.lift_f (CopF.InL (ConsoleDSL.PrintLine (s, ())))
  let read_line () = Combined.lift_f (CopF.InL (ConsoleDSL.ReadLine (fun s -> s)))

  (* Lift KV instructions into the combined monad *)
  let get key = Combined.lift_f (CopF.InR (KVStoreDSL.Get (key, fun v -> v)))
  let put key value = Combined.lift_f (CopF.InR (KVStoreDSL.Put (key, value, ())))

  (* A program that uses BOTH console and KV store *)
  let interactive_store =
    let open Combined in
    print_line "Enter a key:" >>= fun () ->
    read_line () >>= fun key ->
    print_line "Enter a value:" >>= fun () ->
    read_line () >>= fun value ->
    put key value >>= fun () ->
    print_line ("Stored: " ^ key ^ " = " ^ value) >>= fun () ->
    get key >>= fun retrieved ->
    let msg = match retrieved with
      | Some v -> "Retrieved: " ^ v
      | None -> "Error: key not found!"
    in
    print_line msg >>= fun () ->
    pure ()

  (* Combined interpreter using test inputs *)
  let rec run_test : type a.
    string list -> (string, string) Hashtbl.t -> a Combined.t ->
    a * string list * string list =
    fun inputs tbl program ->
    match program with
    | Combined.Pure x -> (x, [], inputs)
    | Combined.Free (CopF.InL (ConsoleDSL.PrintLine (s, next))) ->
        let (result, outputs, remaining) = run_test inputs tbl next in
        (result, s :: outputs, remaining)
    | Combined.Free (CopF.InL (ConsoleDSL.ReadLine cont)) ->
        begin match inputs with
        | [] -> failwith "No more test inputs"
        | input :: rest -> run_test rest tbl (cont input)
        end
    | Combined.Free (CopF.InL (ConsoleDSL.PrintError (s, next))) ->
        let (result, outputs, remaining) = run_test inputs tbl next in
        (result, ("[ERROR] " ^ s) :: outputs, remaining)
    | Combined.Free (CopF.InR (KVStoreDSL.Get (k, cont))) ->
        let v = Hashtbl.find_opt tbl k in
        run_test inputs tbl (cont v)
    | Combined.Free (CopF.InR (KVStoreDSL.Put (k, v, next))) ->
        Hashtbl.replace tbl k v;
        run_test inputs tbl next
    | Combined.Free (CopF.InR (KVStoreDSL.Delete (_, next))) ->
        run_test inputs tbl next
    | Combined.Free (CopF.InR (KVStoreDSL.Keys cont)) ->
        let ks = Hashtbl.fold (fun k _ acc -> k :: acc) tbl [] in
        run_test inputs tbl (cont (List.sort compare ks))
end


(* ══════════════════════════════════════════════════════════════════════
   Church-Encoded Free Monad (Codensity)
   ══════════════════════════════════════════════════════════════════════ *)

(* The naive free monad has O(n²) left-associated binds.
   Church encoding (Codensity transformation) fixes this by using CPS
   to achieve O(n) bind.  This is the same trick as difference lists. *)

module ChurchFree (F : FUNCTOR) = struct
  (* Church-encoded: a program is a function that, given an interpreter
     for Pure and Free cases, produces a result. *)
  type 'a t = { run : 'r. ('a -> 'r) -> ('a t F.t -> 'r) -> 'r }

  let pure x = { run = fun k _ -> k x }

  let bind m f = {
    run = fun k_pure k_free ->
      m.run
        (fun a -> (f a).run k_pure k_free)
        k_free
  }

  let ( >>= ) = bind
  let ( >> ) m1 m2 = bind m1 (fun _ -> m2)

  let lift_f (instr : 'a F.t) : 'a t =
    { run = fun k_pure k_free ->
        k_free (F.map (fun a -> pure a) instr) }

  (* Convert to standard free monad for interpretation *)
  module Standard = Free(F)

  let to_standard (m : 'a t) : 'a Standard.t =
    m.run
      (fun x -> Standard.Pure x)
      (fun fx -> Standard.Free fx)
end


(* ══════════════════════════════════════════════════════════════════════
   Tests
   ══════════════════════════════════════════════════════════════════════ *)

let () =
  let tests_passed = ref 0 in
  let tests_failed = ref 0 in

  let check name cond =
    if cond then begin
      Printf.printf "  ✓ %s\n" name;
      incr tests_passed
    end else begin
      Printf.printf "  ✗ %s\n" name;
      incr tests_failed
    end
  in

  Printf.printf "\n═══ Free Monad Tests ═══\n\n";

  (* ── Console DSL tests ──────────────────────────────────────── *)
  Printf.printf "Console DSL:\n";

  let (name, result) =
    ConsoleDSL.run_test ["Alice"; "25"] ConsoleDSL.greet_program
  in
  check "greet returns name" (name = "Alice");
  check "greet has correct outputs"
    (result.outputs = [
      "What is your name?";
      "Hello, Alice!";
      "How old are you?";
      "Wow, 25 is a great age!"
    ]);
  check "greet has no errors" (result.errors = []);
  check "greet consumes all inputs" (result.remaining_inputs = []);

  let (sum, result2) =
    ConsoleDSL.run_test ["10"; "20"] ConsoleDSL.sum_program
  in
  check "sum returns correct result" (sum = 30);
  check "sum prints result"
    (List.exists (fun s -> s = "Sum: 30") result2.outputs);

  let trace = ConsoleDSL.trace ConsoleDSL.greet_program in
  check "trace has steps" (List.length trace > 0);
  check "trace contains PRINT"
    (List.exists (fun s -> String.length s > 0 &&
       try ignore (Str.search_forward (Str.regexp "PRINT") s 0); true
       with Not_found -> false) trace
     || List.exists (fun s ->
       let len = String.length s in
       let rec find_substr i =
         if i + 5 > len then false
         else if String.sub s i 5 = "PRINT" then true
         else find_substr (i + 1)
       in find_substr 0) trace);

  let count = ConsoleDSL.count_instructions ConsoleDSL.greet_program in
  check "instruction count is correct" (count = 6);  (* 4 prints + 2 reads *)

  (* Test with empty input should fail *)
  let failed_test =
    try
      ignore (ConsoleDSL.run_test [] ConsoleDSL.greet_program);
      false
    with Failure _ -> true
  in
  check "test with no inputs fails" failed_test;

  (* ── KV Store DSL tests ─────────────────────────────────────── *)
  Printf.printf "\nKV Store DSL:\n";

  let keys = KVStoreDSL.run_in_memory KVStoreDSL.shopping_cart_program in
  check "shopping cart has apples" (List.mem "apples" keys);
  check "shopping cart has bananas" (List.mem "bananas" keys);
  check "shopping cart no oranges" (not (List.mem "oranges" keys));
  check "shopping cart has 2 items" (List.length keys = 2);

  (* Test get_or_default *)
  let default_program =
    let open KVStoreDSL in
    let open KV in
    put "existing" "hello" >>= fun () ->
    get_or_default "existing" "nope" >>= fun v1 ->
    get_or_default "missing" "default" >>= fun v2 ->
    pure (v1, v2)
  in
  let (v1, v2) = KVStoreDSL.run_in_memory default_program in
  check "get_or_default existing" (v1 = "hello");
  check "get_or_default missing" (v2 = "default");

  (* Test put_if_absent *)
  let absent_program =
    let open KVStoreDSL in
    let open KV in
    put "key" "original" >>= fun () ->
    put_if_absent "key" "new" >>= fun v1 ->
    put_if_absent "new_key" "fresh" >>= fun v2 ->
    pure (v1, v2)
  in
  let (v1, v2) = KVStoreDSL.run_in_memory absent_program in
  check "put_if_absent keeps original" (v1 = "original");
  check "put_if_absent sets new" (v2 = "fresh");

  (* Test swap *)
  let swap_program =
    let open KVStoreDSL in
    let open KV in
    put "a" "1" >>= fun () ->
    put "b" "2" >>= fun () ->
    swap "a" "b" >>= fun () ->
    get "a" >>= fun va ->
    get "b" >>= fun vb ->
    pure (va, vb)
  in
  let (va, vb) = KVStoreDSL.run_in_memory swap_program in
  check "swap moves a->b" (vb = Some "1");
  check "swap moves b->a" (va = Some "2");

  (* Test audit trail *)
  let (_, audit) = KVStoreDSL.run_audited KVStoreDSL.shopping_cart_program in
  check "audit trail not empty" (List.length audit > 0);
  check "audit starts with put"
    (match List.hd audit with KVStoreDSL.APut _ -> true | _ -> false);

  (* Test dry run *)
  let ops = KVStoreDSL.dry_run KVStoreDSL.shopping_cart_program in
  check "dry run captures operations" (List.length ops > 0);
  let formatted = KVStoreDSL.format_dry_run ops in
  check "dry run format works" (List.length formatted = List.length ops);
  check "dry run has PUT"
    (List.exists (fun s ->
      let len = String.length s in
      len >= 3 && String.sub s 0 3 = "PUT") formatted);

  (* ── Logging DSL tests ──────────────────────────────────────── *)
  Printf.printf "\nLogging DSL:\n";

  let (count, logs) = LogDSL.collect_logs LogDSL.processing_pipeline in
  check "pipeline returns log count" (count = 6);  (* 6 log entries total *)
  check "collected all logs" (List.length logs = 6);
  check "first log is info"
    (match logs with
     | { LogDSL.level = LogDSL.Info; _ } :: _ -> true
     | _ -> false);

  (* Test level filtering *)
  let (_, warn_logs) =
    LogDSL.collect_filtered LogDSL.Warn LogDSL.processing_pipeline
  in
  check "filtered logs have fewer entries" (List.length warn_logs < List.length logs);
  check "filtered only has warn+"
    (List.for_all (fun e ->
      LogDSL.level_value e.LogDSL.level >= LogDSL.level_value LogDSL.Warn
    ) warn_logs);

  (* Test log formatting *)
  let formatted = LogDSL.format_logs logs in
  check "format produces strings" (List.length formatted = List.length logs);
  check "format includes level"
    (List.exists (fun s ->
      let len = String.length s in
      len >= 6 && String.sub s 0 6 = "[INFO]") formatted);
  check "format includes context"
    (List.exists (fun s ->
      let rec has_substr str sub i =
        let slen = String.length sub in
        if i + slen > String.length str then false
        else if String.sub str i slen = sub then true
        else has_substr str sub (i + 1)
      in has_substr s "source=db" 0) formatted);

  (* ── Combined DSL tests ─────────────────────────────────────── *)
  Printf.printf "\nCombined Console+KV DSL:\n";

  let ((), outputs, _remaining) =
    ConsoleKV.run_test
      ["mykey"; "myvalue"]
      (Hashtbl.create 4)
      ConsoleKV.interactive_store
  in
  check "combined outputs prompts"
    (List.exists (fun s ->
      let len = String.length s in
      let rec has i =
        if i + 3 > len then false
        else if String.sub s i 3 = "key" then true
        else has (i + 1)
      in has 0) outputs);
  check "combined outputs stored confirmation"
    (List.exists (fun s ->
      let len = String.length s in
      let rec has i =
        if i + 7 > len then false
        else if String.sub s i 7 = "myvalue" then true
        else has (i + 1)
      in has 0) outputs);

  (* ── Church-encoded free monad tests ────────────────────────── *)
  Printf.printf "\nChurch-Encoded Free Monad:\n";

  let module ChurchConsole = ChurchFree(ConsoleDSL.InstrF) in

  (* Build a program using Church encoding *)
  let church_program =
    let open ChurchConsole in
    lift_f (ConsoleDSL.PrintLine ("Hello from Church!", ())) >>= fun () ->
    lift_f (ConsoleDSL.ReadLine (fun s -> s)) >>= fun name ->
    lift_f (ConsoleDSL.PrintLine ("Hi " ^ name ^ "!", ())) >>= fun () ->
    pure name
  in
  (* Convert to standard and interpret *)
  let standard = ChurchConsole.to_standard church_program in
  let (name, result) = ConsoleDSL.run_test ["World"] standard in
  check "church encoding returns value" (name = "World");
  check "church encoding outputs correct"
    (result.outputs = ["Hello from Church!"; "Hi World!"]);

  (* Test Church bind associativity (the whole point — O(n) not O(n²)) *)
  let chain_church n =
    let open ChurchConsole in
    let rec build acc i =
      if i >= n then acc
      else build (acc >>= fun count ->
        lift_f (ConsoleDSL.PrintLine (string_of_int count, ())) >> pure (count + 1)
      ) (i + 1)
    in
    build (pure 0) 0
  in
  let standard_chain = ChurchConsole.to_standard (chain_church 100) in
  let (final_count, chain_result) = ConsoleDSL.run_test [] standard_chain in
  check "church chain completes" (final_count = 100);
  check "church chain correct output count" (List.length chain_result.outputs = 100);

  (* ── Monad law tests ────────────────────────────────────────── *)
  Printf.printf "\nMonad Laws:\n";

  (* Left identity: pure x >>= f  ≡  f x *)
  let f x =
    let open KVStoreDSL in
    let open KV in
    put "test" x >> pure (String.length x)
  in
  let left = KVStoreDSL.run_in_memory KVStoreDSL.KV.(pure "hello" >>= f) in
  let right = KVStoreDSL.run_in_memory (f "hello") in
  check "left identity law" (left = right);

  (* Right identity: m >>= pure  ≡  m *)
  let m =
    let open KVStoreDSL in
    let open KV in
    put "x" "1" >> get "x"
  in
  let left = KVStoreDSL.run_in_memory KVStoreDSL.KV.(m >>= pure) in
  let right = KVStoreDSL.run_in_memory m in
  check "right identity law" (left = right);

  (* Associativity: (m >>= f) >>= g  ≡  m >>= (fun x -> f x >>= g) *)
  let g v = KVStoreDSL.KV.pure (match v with Some s -> String.length s | None -> 0) in
  let m =
    let open KVStoreDSL in
    let open KV in
    put "k" "val" >> pure "k"
  in
  let f2 k = KVStoreDSL.get k in
  let left = KVStoreDSL.run_in_memory KVStoreDSL.KV.((m >>= f2) >>= g) in
  let right = KVStoreDSL.run_in_memory KVStoreDSL.KV.(m >>= fun x -> f2 x >>= g) in
  check "associativity law" (left = right);

  (* ── Summary ────────────────────────────────────────────────── *)
  Printf.printf "\n═══ Results: %d passed, %d failed ═══\n\n"
    !tests_passed !tests_failed;

  if !tests_failed > 0 then exit 1
