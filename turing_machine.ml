(* Turing Machine Simulator
 *
 * Demonstrates:
 *   - Classic single-tape Turing machine model
 *   - Transition table-based computation
 *   - Step-by-step execution with tape visualization
 *   - Multiple example machines (palindrome, binary increment, busy beaver)
 *   - Halting detection and step counting
 *   - Functional state management
 *
 * Usage:
 *   ocaml turing_machine.ml
 *)

(* ── Types ──────────────────────────────────────────────────────────── *)

type direction = Left | Right | Stay

type symbol = char

type state = string

type transition = {
  read_sym   : symbol;
  write_sym  : symbol;
  direction  : direction;
  next_state : state;
}

type machine = {
  name          : string;
  states        : state list;
  alphabet      : symbol list;
  blank         : symbol;
  initial_state : state;
  accept_states : state list;
  reject_states : state list;
  transitions   : (state * symbol, transition) Hashtbl.t;
}

type tape = {
  left   : symbol list;   (* reversed left portion *)
  head   : symbol;        (* current symbol under head *)
  right  : symbol list;   (* right portion *)
  blank  : symbol;
}

type config = {
  tape    : tape;
  state   : state;
  steps   : int;
  history : (state * tape) list;
}

(* ── Tape operations ────────────────────────────────────────────────── *)

let make_tape ?(blank='_') input =
  match input with
  | [] -> { left = []; head = blank; right = []; blank }
  | h :: t -> { left = []; head = h; right = t; blank }

let tape_of_string ?(blank='_') s =
  let chars = List.init (String.length s) (String.get s) in
  make_tape ~blank chars

let move_left tape =
  match tape.left with
  | [] -> { tape with left = []; head = tape.blank; right = tape.head :: tape.right }
  | l :: ls -> { tape with left = ls; head = l; right = tape.head :: tape.right }

let move_right tape =
  match tape.right with
  | [] -> { tape with left = tape.head :: tape.left; head = tape.blank; right = [] }
  | r :: rs -> { tape with left = tape.head :: tape.left; head = r; right = rs }

let move_stay tape = tape

let write_tape tape sym =
  { tape with head = sym }

let move tape dir =
  match dir with
  | Left  -> move_left tape
  | Right -> move_right tape
  | Stay  -> move_stay tape

let tape_contents tape =
  let left_str = List.rev tape.left |> List.to_seq |> String.of_seq in
  let right_str = tape.right |> List.to_seq |> String.of_seq in
  let full = left_str ^ String.make 1 tape.head ^ right_str in
  (* Trim trailing blanks *)
  let len = ref (String.length full) in
  while !len > 0 && full.[!len - 1] = tape.blank do decr len done;
  (* Trim leading blanks *)
  let start = ref 0 in
  while !start < !len && full.[!start] = tape.blank do incr start done;
  if !start >= !len then String.make 1 tape.blank
  else String.sub full !start (!len - !start)

(* ── Tape visualization ─────────────────────────────────────────────── *)

let render_tape tape ?(context=15) () =
  let left_syms = 
    let pad_count = max 0 (context - List.length tape.left) in
    List.init pad_count (fun _ -> tape.blank) @ List.rev (
      if List.length tape.left > context 
      then List.filteri (fun i _ -> i < context) tape.left
      else tape.left
    )
  in
  let right_syms =
    let r = if List.length tape.right > context
      then List.filteri (fun i _ -> i < context) tape.right
      else tape.right
    in
    let pad_count = max 0 (context - List.length r) in
    r @ List.init pad_count (fun _ -> tape.blank)
  in
  let top    = String.concat "" (List.map (fun _ -> "+---") left_syms) ^ "+---+" ^ String.concat "" (List.map (fun _ -> "+---") right_syms) ^ "+" in
  let cells  = String.concat "" (List.map (fun c -> Printf.sprintf "| %c " c) left_syms) ^ Printf.sprintf "|[%c]" tape.head ^ String.concat "" (List.map (fun c -> Printf.sprintf "| %c " c) right_syms) ^ "|" in
  let bottom = top in
  Printf.sprintf "%s\n%s\n%s" top cells bottom

(* ── Machine construction ───────────────────────────────────────────── *)

let create_machine ~name ~states ~alphabet ~blank ~initial_state ~accept_states ~reject_states ~transitions =
  let tbl = Hashtbl.create (List.length transitions) in
  List.iter (fun (st, sym, wr, dir, next) ->
    Hashtbl.replace tbl (st, sym) { read_sym = sym; write_sym = wr; direction = dir; next_state = next }
  ) transitions;
  { name; states; alphabet; blank; initial_state; accept_states; reject_states; transitions = tbl }

(* ── Execution ──────────────────────────────────────────────────────── *)

let init_config machine input =
  let tape = tape_of_string ~blank:machine.blank input in
  { tape; state = machine.initial_state; steps = 0; history = [] }

let is_halted machine config =
  List.mem config.state machine.accept_states ||
  List.mem config.state machine.reject_states

let is_accepted machine config =
  List.mem config.state machine.accept_states

let step machine config =
  if is_halted machine config then None
  else
    match Hashtbl.find_opt machine.transitions (config.state, config.tape.head) with
    | None -> None  (* No transition = halt/reject *)
    | Some tr ->
      let new_tape = write_tape config.tape tr.write_sym |> fun t -> move t tr.direction in
      Some {
        tape = new_tape;
        state = tr.next_state;
        steps = config.steps + 1;
        history = (config.state, config.tape) :: config.history;
      }

let run ?(max_steps=10000) ?(verbose=false) machine input =
  let config = ref (init_config machine input) in
  if verbose then (
    Printf.printf "=== %s ===\n" machine.name;
    Printf.printf "Input: \"%s\"\n\n" input;
    Printf.printf "Step %d | State: %s\n%s\n\n" !config.steps !config.state (render_tape !config.tape ~context:10 ())
  );
  let halted = ref false in
  while not !halted && !config.steps < max_steps do
    match step machine !config with
    | None -> halted := true
    | Some c ->
      config := c;
      if verbose then
        Printf.printf "Step %d | State: %s\n%s\n\n" c.steps c.state (render_tape c.tape ~context:10 ())
  done;
  if verbose then (
    if is_accepted machine !config then
      Printf.printf "✓ ACCEPTED after %d steps\n" !config.steps
    else if is_halted machine !config then
      Printf.printf "✗ REJECTED after %d steps\n" !config.steps
    else
      Printf.printf "⚠ Did not halt within %d steps\n" max_steps
  );
  !config

(* ── Example Machines ───────────────────────────────────────────────── *)

(* Binary increment: adds 1 to a binary number *)
let binary_increment () =
  create_machine
    ~name:"Binary Increment"
    ~states:["scan_right"; "carry"; "done"]
    ~alphabet:['0'; '1'; '_']
    ~blank:'_'
    ~initial_state:"scan_right"
    ~accept_states:["done"]
    ~reject_states:[]
    ~transitions:[
      (* Scan right to find the end *)
      ("scan_right", '0', '0', Right, "scan_right");
      ("scan_right", '1', '1', Right, "scan_right");
      ("scan_right", '_', '_', Left,  "carry");
      (* Carry back *)
      ("carry", '0', '1', Stay, "done");
      ("carry", '1', '0', Left, "carry");
      ("carry", '_', '1', Stay, "done");
    ]

(* Unary addition: computes n + m using 1s separated by + *)
let unary_addition () =
  create_machine
    ~name:"Unary Addition (1^n + 1^m = 1^(n+m))"
    ~states:["find_plus"; "erase_plus"; "go_end"; "erase_last"; "done"]
    ~alphabet:['1'; '+'; '_']
    ~blank:'_'
    ~initial_state:"find_plus"
    ~accept_states:["done"]
    ~reject_states:[]
    ~transitions:[
      (* Find the + sign *)
      ("find_plus", '1', '1', Right, "find_plus");
      ("find_plus", '+', '1', Right, "go_end");
      (* Go to end *)
      ("go_end", '1', '1', Right, "go_end");
      ("go_end", '_', '_', Left,  "erase_last");
      (* Erase last 1 *)
      ("erase_last", '1', '_', Stay, "done");
    ]

(* Palindrome checker for strings of a's and b's *)
let palindrome_checker () =
  create_machine
    ~name:"Palindrome Checker ({a,b}*)"
    ~states:["start"; "found_a"; "found_b"; "go_right_a"; "go_right_b"; "check_a"; "check_b"; "go_back"; "accept"; "reject"]
    ~alphabet:['a'; 'b'; 'X'; '_']
    ~blank:'_'
    ~initial_state:"start"
    ~accept_states:["accept"]
    ~reject_states:["reject"]
    ~transitions:[
      (* Read leftmost symbol *)
      ("start", 'a', 'X', Right, "go_right_a");
      ("start", 'b', 'X', Right, "go_right_b");
      ("start", 'X', 'X', Right, "start");
      ("start", '_', '_', Stay,  "accept");  (* empty or all matched *)
      (* Go right to find the rightmost unchecked symbol *)
      ("go_right_a", 'a', 'a', Right, "go_right_a");
      ("go_right_a", 'b', 'b', Right, "go_right_a");
      ("go_right_a", 'X', 'X', Left,  "check_a");
      ("go_right_a", '_', '_', Left,  "check_a");
      ("go_right_b", 'a', 'a', Right, "go_right_b");
      ("go_right_b", 'b', 'b', Right, "go_right_b");
      ("go_right_b", 'X', 'X', Left,  "check_b");
      ("go_right_b", '_', '_', Left,  "check_b");
      (* Check if rightmost matches *)
      ("check_a", 'a', 'X', Left,  "go_back");
      ("check_a", 'b', 'b', Stay,  "reject");
      ("check_a", 'X', 'X', Stay,  "accept");  (* single char left = palindrome *)
      ("check_b", 'b', 'X', Left,  "go_back");
      ("check_b", 'a', 'a', Stay,  "reject");
      ("check_b", 'X', 'X', Stay,  "accept");
      (* Go back to the leftmost unchecked *)
      ("go_back", 'a', 'a', Left,  "go_back");
      ("go_back", 'b', 'b', Left,  "go_back");
      ("go_back", 'X', 'X', Right, "start");
    ]

(* 3-state Busy Beaver (BB-3): produces 6 ones and halts in 14 steps *)
let busy_beaver_3 () =
  create_machine
    ~name:"3-State Busy Beaver"
    ~states:["A"; "B"; "C"; "HALT"]
    ~alphabet:['0'; '1']
    ~blank:'0'
    ~initial_state:"A"
    ~accept_states:["HALT"]
    ~reject_states:[]
    ~transitions:[
      ("A", '0', '1', Right, "B");
      ("A", '1', '1', Left,  "C");
      ("B", '0', '1', Left,  "A");
      ("B", '1', '1', Right, "B");
      ("C", '0', '1', Left,  "B");
      ("C", '1', '1', Stay,  "HALT");
    ]

(* ── Statistics ─────────────────────────────────────────────────────── *)

let run_stats machine input =
  let config = run ~verbose:false machine input in
  let result = tape_contents config.tape in
  let accepted = is_accepted machine config in
  Printf.printf "Machine: %s\n" machine.name;
  Printf.printf "Input:   \"%s\"\n" input;
  Printf.printf "Output:  \"%s\"\n" result;
  Printf.printf "Steps:   %d\n" config.steps;
  Printf.printf "Result:  %s\n\n" (if accepted then "ACCEPTED" else "REJECTED");
  (config, result, accepted)

(* ── Demo ───────────────────────────────────────────────────────────── *)

let () =
  Printf.printf "╔══════════════════════════════════════════════╗\n";
  Printf.printf "║       Turing Machine Simulator               ║\n";
  Printf.printf "╚══════════════════════════════════════════════╝\n\n";

  (* Binary increment *)
  Printf.printf "━━━ Binary Increment ━━━\n\n";
  let machine = binary_increment () in
  List.iter (fun input ->
    let _ = run ~verbose:true machine input in
    Printf.printf "---\n\n"
  ) ["101"; "111"; "1011"; "0"];

  (* Unary addition *)
  Printf.printf "\n━━━ Unary Addition ━━━\n\n";
  let machine = unary_addition () in
  List.iter (fun input ->
    let (cfg, result, _) = run_stats machine input in
    ignore cfg;
    Printf.printf "  %s → %s (computed: %d + %d = %d)\n\n"
      input result
      (String.length (String.split_on_char '+' input |> List.hd))
      (String.length (String.split_on_char '+' input |> List.rev |> List.hd))
      (String.length result)
  ) ["111+11"; "1+1"; "11111+111"];

  (* Palindrome checker *)
  Printf.printf "\n━━━ Palindrome Checker ━━━\n\n";
  let machine = palindrome_checker () in
  List.iter (fun input ->
    let (_, _, accepted) = run_stats machine input in
    Printf.printf "  \"%s\" is %sa palindrome\n\n" input (if accepted then "" else "NOT ")
  ) ["abba"; "aba"; "abc"; "aabaa"; "ab"; "a"; ""];

  (* Busy Beaver *)
  Printf.printf "\n━━━ 3-State Busy Beaver ━━━\n\n";
  let machine = busy_beaver_3 () in
  let _ = run ~verbose:true machine "" in
  let (cfg, result, _) = run_stats machine "" in
  let ones = String.to_seq result |> Seq.filter (fun c -> c = '1') |> Seq.length in
  Printf.printf "Ones produced: %d (expected: 6)\n" ones;
  Printf.printf "Steps taken:   %d (expected: 14)\n" cfg.steps;

  Printf.printf "\n═══════════════════════════════════════════════\n";
  Printf.printf "All demonstrations complete!\n"
