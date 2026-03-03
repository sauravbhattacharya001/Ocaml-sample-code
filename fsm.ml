(* Finite State Machines — deterministic & nondeterministic automata *)
(* Demonstrates: variant types, pattern matching, sets/maps, fixpoints, *)
(* formal language theory, DFA/NFA construction, string acceptance *)

(* ── Types ─────────────────────────────────────────────────────── *)

module CharSet = Set.Make(Char)
module StateSet = Set.Make(Int)
module TransMap = Map.Make(struct
  type t = int * char
  let compare = compare
end)
module EpsMap = Map.Make(Int)

(* Deterministic Finite Automaton *)
type dfa = {
  dfa_states     : StateSet.t;
  dfa_alphabet   : CharSet.t;
  dfa_transition : int TransMap.t;      (* (state, char) -> state *)
  dfa_start      : int;
  dfa_accept     : StateSet.t;
}

(* Nondeterministic Finite Automaton with epsilon transitions *)
type nfa = {
  nfa_states     : StateSet.t;
  nfa_alphabet   : CharSet.t;
  nfa_transition : StateSet.t TransMap.t;  (* (state, char) -> set of states *)
  nfa_epsilon    : StateSet.t EpsMap.t;    (* state -> epsilon-reachable states *)
  nfa_start      : int;
  nfa_accept     : StateSet.t;
}

(* ── DFA Operations ────────────────────────────────────────────── *)

(* Create a DFA from components *)
let make_dfa ~states ~alphabet ~transitions ~start ~accept =
  let dfa_states = StateSet.of_list states in
  let dfa_alphabet = CharSet.of_list alphabet in
  let dfa_transition =
    List.fold_left (fun m (s, c, t) -> TransMap.add (s, c) t m)
      TransMap.empty transitions
  in
  let dfa_accept = StateSet.of_list accept in
  { dfa_states; dfa_alphabet; dfa_transition; dfa_start = start; dfa_accept }

(* Step one transition in a DFA; returns None if no transition defined *)
let dfa_step dfa state ch =
  TransMap.find_opt (state, ch) dfa.dfa_transition

(* Run a DFA on a string; returns true if accepted *)
let dfa_accepts dfa input =
  let len = String.length input in
  let rec go state i =
    if i >= len then StateSet.mem state dfa.dfa_accept
    else
      match dfa_step dfa state input.[i] with
      | None -> false
      | Some next -> go next (i + 1)
  in
  go dfa.dfa_start 0

(* Trace a DFA run, returning the list of states visited *)
let dfa_trace dfa input =
  let len = String.length input in
  let rec go state i acc =
    if i >= len then List.rev (state :: acc)
    else
      match dfa_step dfa state input.[i] with
      | None -> List.rev (state :: acc)  (* stuck *)
      | Some next -> go next (i + 1) (state :: acc)
  in
  go dfa.dfa_start 0 []

(* ── NFA Operations ────────────────────────────────────────────── *)

(* Create an NFA from components *)
let make_nfa ~states ~alphabet ~transitions ~epsilon ~start ~accept =
  let nfa_states = StateSet.of_list states in
  let nfa_alphabet = CharSet.of_list alphabet in
  let nfa_transition =
    List.fold_left (fun m (s, c, targets) ->
      let existing = match TransMap.find_opt (s, c) m with
        | None -> StateSet.empty
        | Some ss -> ss
      in
      TransMap.add (s, c) (StateSet.union existing (StateSet.of_list targets)) m
    ) TransMap.empty transitions
  in
  let nfa_epsilon =
    List.fold_left (fun m (s, targets) ->
      let existing = match EpsMap.find_opt s m with
        | None -> StateSet.empty
        | Some ss -> ss
      in
      EpsMap.add s (StateSet.union existing (StateSet.of_list targets)) m
    ) EpsMap.empty epsilon
  in
  { nfa_states; nfa_alphabet; nfa_transition; nfa_epsilon;
    nfa_start = start; nfa_accept = StateSet.of_list accept }

(* Compute epsilon closure of a set of states *)
let epsilon_closure nfa states =
  let rec fixpoint current =
    let next = StateSet.fold (fun s acc ->
      match EpsMap.find_opt s nfa.nfa_epsilon with
      | None -> acc
      | Some reachable -> StateSet.union acc reachable
    ) current current
    in
    if StateSet.equal current next then current
    else fixpoint next
  in
  fixpoint states

(* Step NFA: from a set of states on a character, compute next states *)
let nfa_step nfa states ch =
  let moved = StateSet.fold (fun s acc ->
    match TransMap.find_opt (s, ch) nfa.nfa_transition with
    | None -> acc
    | Some targets -> StateSet.union acc targets
  ) states StateSet.empty
  in
  epsilon_closure nfa moved

(* Run an NFA on a string; returns true if accepted *)
let nfa_accepts nfa input =
  let len = String.length input in
  let initial = epsilon_closure nfa (StateSet.singleton nfa.nfa_start) in
  let rec go current i =
    if i >= len then
      not (StateSet.is_empty (StateSet.inter current nfa.nfa_accept))
    else
      let next = nfa_step nfa current input.[i] in
      if StateSet.is_empty next then false
      else go next (i + 1)
  in
  go initial 0

(* ── NFA to DFA (Subset Construction) ─────────────────────────── *)

(* Convert an NFA to an equivalent DFA via the powerset/subset construction. *)
(* Each DFA state corresponds to a set of NFA states. *)
let nfa_to_dfa nfa =
  let initial = epsilon_closure nfa (StateSet.singleton nfa.nfa_start) in
  let state_id = Hashtbl.create 16 in
  let next_id = ref 0 in
  let get_id ss =
    match Hashtbl.find_opt state_id ss with
    | Some id -> id
    | None ->
      let id = !next_id in
      incr next_id;
      Hashtbl.add state_id ss id;
      id
  in
  let start_id = get_id initial in
  let transitions = ref [] in
  let accept_ids = ref [] in
  let all_ids = ref [] in
  let worklist = Queue.create () in
  Queue.push initial worklist;
  while not (Queue.is_empty worklist) do
    let current = Queue.pop worklist in
    let cid = get_id current in
    all_ids := cid :: !all_ids;
    if not (StateSet.is_empty (StateSet.inter current nfa.nfa_accept)) then
      accept_ids := cid :: !accept_ids;
    CharSet.iter (fun ch ->
      let next = nfa_step nfa current ch in
      if not (StateSet.is_empty next) then begin
        let nid = get_id next in
        transitions := (cid, ch, nid) :: !transitions;
        if not (Hashtbl.mem state_id next && nid < !next_id - 1 || nid <= cid) then
          () (* already visited *)
        (* Simple approach: re-check *)
      end
    ) nfa.nfa_alphabet
  done;
  (* Rebuild properly with BFS *)
  let visited = Hashtbl.create 16 in
  let transitions2 = ref [] in
  let accept2 = ref [] in
  let all2 = ref [] in
  Hashtbl.clear state_id;
  next_id := 0;
  let start_id2 = get_id initial in
  let q = Queue.create () in
  Queue.push initial q;
  Hashtbl.add visited (StateSet.elements initial) true;
  while not (Queue.is_empty q) do
    let current = Queue.pop q in
    let cid = get_id current in
    all2 := cid :: !all2;
    if not (StateSet.is_empty (StateSet.inter current nfa.nfa_accept)) then
      accept2 := cid :: !accept2;
    CharSet.iter (fun ch ->
      let next = nfa_step nfa current ch in
      if not (StateSet.is_empty next) then begin
        let nid = get_id next in
        transitions2 := (cid, ch, nid) :: !transitions2;
        let key = StateSet.elements next in
        if not (Hashtbl.mem visited key) then begin
          Hashtbl.add visited key true;
          Queue.push next q
        end
      end
    ) nfa.nfa_alphabet
  done;
  make_dfa
    ~states:!all2
    ~alphabet:(CharSet.elements nfa.nfa_alphabet)
    ~transitions:!transitions2
    ~start:start_id2
    ~accept:!accept2

(* ── DFA Complement ────────────────────────────────────────────── *)

(* Complement a DFA: swap accept and non-accept states.
   Requires the DFA to be complete (transitions defined for all state/char pairs). *)
let dfa_complement dfa =
  { dfa with dfa_accept = StateSet.diff dfa.dfa_states dfa.dfa_accept }

(* ── Pretty Printing ───────────────────────────────────────────── *)

let string_of_state_set ss =
  "{" ^ (StateSet.elements ss |> List.map string_of_int |> String.concat ", ") ^ "}"

let print_dfa dfa =
  Printf.printf "DFA:\n";
  Printf.printf "  States:  %s\n" (string_of_state_set dfa.dfa_states);
  Printf.printf "  Start:   %d\n" dfa.dfa_start;
  Printf.printf "  Accept:  %s\n" (string_of_state_set dfa.dfa_accept);
  Printf.printf "  Transitions:\n";
  TransMap.iter (fun (s, c) t ->
    Printf.printf "    δ(%d, '%c') = %d\n" s c t
  ) dfa.dfa_transition

(* ── Example / Demo ────────────────────────────────────────────── *)

let () =
  print_endline "=== Finite State Machines ===\n";

  (* DFA that accepts strings over {a,b} ending in "ab" *)
  print_endline "-- DFA: accepts strings ending in \"ab\" --";
  let dfa1 = make_dfa
    ~states:[0; 1; 2]
    ~alphabet:['a'; 'b']
    ~transitions:[
      (0, 'a', 1); (0, 'b', 0);   (* state 0: saw nothing useful *)
      (1, 'a', 1); (1, 'b', 2);   (* state 1: saw 'a' *)
      (2, 'a', 1); (2, 'b', 0);   (* state 2: saw 'ab' — accept *)
    ]
    ~start:0
    ~accept:[2]
  in
  print_dfa dfa1;
  let test_strings = ["ab"; "aab"; "abb"; "bab"; "a"; "b"; ""; "abab"] in
  List.iter (fun s ->
    Printf.printf "  \"%s\" → %s  (trace: [%s])\n" s
      (if dfa_accepts dfa1 s then "ACCEPT" else "REJECT")
      (dfa_trace dfa1 s |> List.map string_of_int |> String.concat " → ")
  ) test_strings;

  (* NFA that accepts strings containing "ab" as a substring *)
  print_endline "\n-- NFA: accepts strings containing \"ab\" --";
  let nfa1 = make_nfa
    ~states:[0; 1; 2]
    ~alphabet:['a'; 'b']
    ~transitions:[
      (0, 'a', [0; 1]); (0, 'b', [0]);  (* state 0: haven't started matching *)
      (1, 'b', [2]);                      (* state 1: saw 'a', need 'b' *)
      (2, 'a', [2]); (2, 'b', [2]);      (* state 2: matched, accept everything *)
    ]
    ~epsilon:[]
    ~start:0
    ~accept:[2]
  in
  let nfa_tests = ["ab"; "aab"; "ba"; "bab"; "a"; "b"; ""; "xab"] in
  List.iter (fun s ->
    Printf.printf "  \"%s\" → %s\n" s
      (if nfa_accepts nfa1 s then "ACCEPT" else "REJECT")
  ) nfa_tests;

  (* NFA with epsilon transitions: accepts "a" or "b" or "" *)
  print_endline "\n-- NFA with ε-transitions: accepts \"a\" or \"b\" or ε --";
  let nfa2 = make_nfa
    ~states:[0; 1; 2; 3]
    ~alphabet:['a'; 'b']
    ~transitions:[
      (1, 'a', [1]);   (* loop on 'a' *)
      (2, 'b', [2]);   (* loop on 'b' *)
    ]
    ~epsilon:[(0, [1; 2; 3])]  (* start branches to 1, 2, or accept *)
    ~start:0
    ~accept:[3; 1; 2]
  in
  let eps_tests = [""; "a"; "b"; "aa"; "bb"; "ab"] in
  List.iter (fun s ->
    Printf.printf "  \"%s\" → %s\n" s
      (if nfa_accepts nfa2 s then "ACCEPT" else "REJECT")
  ) eps_tests;

  (* Subset construction: convert NFA to DFA *)
  print_endline "\n-- Subset construction: NFA→DFA for 'contains ab' --";
  let converted = nfa_to_dfa nfa1 in
  print_dfa converted;
  List.iter (fun s ->
    Printf.printf "  \"%s\" → %s\n" s
      (if dfa_accepts converted s then "ACCEPT" else "REJECT")
  ) nfa_tests;

  (* Complement *)
  print_endline "\n-- DFA complement: rejects strings ending in \"ab\" --";
  let comp = dfa_complement dfa1 in
  List.iter (fun s ->
    Printf.printf "  \"%s\" → %s\n" s
      (if dfa_accepts comp s then "ACCEPT" else "REJECT")
  ) test_strings;

  print_endline "\nDone!"
