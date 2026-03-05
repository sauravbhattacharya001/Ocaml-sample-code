(* automata.ml — Finite Automata Toolkit
 *
 * A comprehensive library for working with deterministic and nondeterministic
 * finite automata (DFA/NFA) in OCaml.
 *
 * Concepts demonstrated:
 * - Algebraic data types for automata representations
 * - Subset construction (NFA → DFA, powerset construction)
 * - DFA minimization (Hopcroft's algorithm)
 * - Product construction (intersection, union, difference)
 * - Language equivalence and inclusion testing
 * - Regular language operations (complement, reverse, concatenation)
 * - String acceptance and generation
 * - Reachability analysis and dead state removal
 * - Automaton visualization (DOT format)
 *
 * Key types:
 *   dfa  — deterministic finite automaton
 *   nfa  — nondeterministic finite automaton (with ε-transitions)
 *
 * Usage:
 *   let dfa = Automata.dfa_create ~states:2 ~alphabet:['a';'b']
 *     ~transitions:[(0,'a',0);(0,'b',1);(1,'a',0);(1,'b',1)]
 *     ~start:0 ~accept:[1] in
 *   Automata.dfa_accepts dfa "ab"  (* true — ends in 'b' *)
 *
 *   let nfa = Automata.nfa_create ~states:3 ~alphabet:['a';'b']
 *     ~transitions:[(0,'a',0);(0,'b',0);(0,'a',1);(1,'b',2);(2,'a',2);(2,'b',2)]
 *     ~epsilon:[] ~start:0 ~accept:[2] in
 *   let dfa = Automata.nfa_to_dfa nfa in
 *   let min_dfa = Automata.dfa_minimize dfa in
 *   Automata.dfa_accepts min_dfa "bab"  (* true — contains "ab" *)
 *)

module Automata = struct

  (* ── Types ─────────────────────────────────────────────────── *)

  type state = int

  module StateSet = Set.Make(Int)
  module StateMap = Map.Make(Int)
  module CharMap = Map.Make(Char)
  module StateSetMap = Map.Make(struct
    type t = StateSet.t
    let compare = StateSet.compare
  end)

  type dfa = {
    d_states: int;
    d_alphabet: char list;
    d_trans: int CharMap.t StateMap.t;
    d_start: state;
    d_accept: StateSet.t;
  }

  type nfa = {
    n_states: int;
    n_alphabet: char list;
    n_trans: StateSet.t CharMap.t StateMap.t;
    n_epsilon: StateSet.t StateMap.t;
    n_start: state;
    n_accept: StateSet.t;
  }

  (* ── DFA Creation ──────────────────────────────────────────── *)

  let dfa_create ~states ~alphabet ~transitions ~start ~accept =
    let d_trans = List.fold_left (fun acc (s, c, t) ->
      let cm = try StateMap.find s acc with Not_found -> CharMap.empty in
      StateMap.add s (CharMap.add c t cm) acc
    ) StateMap.empty transitions in
    { d_states = states; d_alphabet = alphabet; d_trans;
      d_start = start; d_accept = StateSet.of_list accept }

  (* ── DFA Acceptance ────────────────────────────────────────── *)

  let dfa_step dfa state c =
    try
      let cm = StateMap.find state dfa.d_trans in
      Some (CharMap.find c cm)
    with Not_found -> None

  let dfa_accepts dfa s =
    let rec go state i =
      if i >= String.length s then StateSet.mem state dfa.d_accept
      else match dfa_step dfa state s.[i] with
        | Some next -> go next (i + 1)
        | None -> false
    in
    go dfa.d_start 0

  let dfa_accepts_all dfa strings =
    List.map (fun s -> (s, dfa_accepts dfa s)) strings

  (* ── NFA Creation ──────────────────────────────────────────── *)

  let nfa_create ~states ~alphabet ~transitions ~epsilon ~start ~accept =
    let n_trans = List.fold_left (fun acc (s, c, t) ->
      let cm = try StateMap.find s acc with Not_found -> CharMap.empty in
      let ss = try CharMap.find c cm with Not_found -> StateSet.empty in
      StateMap.add s (CharMap.add c (StateSet.add t ss) cm) acc
    ) StateMap.empty transitions in
    let n_epsilon = List.fold_left (fun acc (s, t) ->
      let ss = try StateMap.find s acc with Not_found -> StateSet.empty in
      StateMap.add s (StateSet.add t ss) acc
    ) StateMap.empty epsilon in
    { n_states = states; n_alphabet = alphabet; n_trans; n_epsilon;
      n_start = start; n_accept = StateSet.of_list accept }

  (* ── Epsilon Closure ───────────────────────────────────────── *)

  let epsilon_closure nfa states =
    let rec expand worklist visited =
      match worklist with
      | [] -> visited
      | s :: rest ->
        if StateSet.mem s visited then expand rest visited
        else
          let visited = StateSet.add s visited in
          let eps = try StateMap.find s nfa.n_epsilon
                    with Not_found -> StateSet.empty in
          let new_states = StateSet.elements (StateSet.diff eps visited) in
          expand (new_states @ rest) visited
    in
    expand (StateSet.elements states) StateSet.empty

  (* ── NFA Acceptance ────────────────────────────────────────── *)

  let nfa_move nfa states c =
    StateSet.fold (fun s acc ->
      let targets = try
        let cm = StateMap.find s nfa.n_trans in
        CharMap.find c cm
      with Not_found -> StateSet.empty in
      StateSet.union acc targets
    ) states StateSet.empty

  let nfa_accepts nfa s =
    let rec go current i =
      if i >= String.length s then
        not (StateSet.is_empty (StateSet.inter current nfa.n_accept))
      else
        let moved = nfa_move nfa current s.[i] in
        let next = epsilon_closure nfa moved in
        go next (i + 1)
    in
    let start = epsilon_closure nfa (StateSet.singleton nfa.n_start) in
    go start 0

  (* ── Subset Construction (NFA → DFA) ───────────────────────── *)

  let nfa_to_dfa nfa =
    let start_set = epsilon_closure nfa (StateSet.singleton nfa.n_start) in
    let next_id = ref 0 in
    let set_to_id = ref StateSetMap.empty in
    let get_id ss =
      match StateSetMap.find_opt ss !set_to_id with
      | Some id -> (id, false)
      | None ->
        let id = !next_id in
        incr next_id;
        set_to_id := StateSetMap.add ss id !set_to_id;
        (id, true)
    in
    let transitions = ref [] in
    let accept = ref StateSet.empty in
    let queue = Queue.create () in
    let (start_id, _) = get_id start_set in
    Queue.push (start_id, start_set) queue;
    if not (StateSet.is_empty (StateSet.inter start_set nfa.n_accept)) then
      accept := StateSet.add start_id !accept;
    while not (Queue.is_empty queue) do
      let (src_id, src_set) = Queue.pop queue in
      List.iter (fun c ->
        let moved = nfa_move nfa src_set c in
        let dst_set = epsilon_closure nfa moved in
        if not (StateSet.is_empty dst_set) then begin
          let (dst_id, is_new) = get_id dst_set in
          transitions := (src_id, c, dst_id) :: !transitions;
          if is_new then begin
            Queue.push (dst_id, dst_set) queue;
            if not (StateSet.is_empty (StateSet.inter dst_set nfa.n_accept)) then
              accept := StateSet.add dst_id !accept
          end
        end
      ) nfa.n_alphabet
    done;
    dfa_create ~states:(!next_id) ~alphabet:nfa.n_alphabet
      ~transitions:(List.rev !transitions)
      ~start:start_id ~accept:(StateSet.elements !accept)

  (* ── DFA Completion (add dead/sink state if needed) ────────── *)

  let dfa_complete dfa =
    let sink = dfa.d_states in
    let needs_sink = ref false in
    let transitions = ref [] in
    for s = 0 to dfa.d_states - 1 do
      List.iter (fun c ->
        match dfa_step dfa s c with
        | Some t -> transitions := (s, c, t) :: !transitions
        | None ->
          needs_sink := true;
          transitions := (s, c, sink) :: !transitions
      ) dfa.d_alphabet
    done;
    if !needs_sink then begin
      List.iter (fun c ->
        transitions := (sink, c, sink) :: !transitions
      ) dfa.d_alphabet;
      dfa_create ~states:(dfa.d_states + 1) ~alphabet:dfa.d_alphabet
        ~transitions:(List.rev !transitions)
        ~start:dfa.d_start ~accept:(StateSet.elements dfa.d_accept)
    end else
      dfa

  (* ── DFA Minimization (Hopcroft's partition refinement) ───── *)

  let dfa_minimize dfa =
    let dfa = dfa_complete dfa in
    let n = dfa.d_states in
    let non_accept = StateSet.diff
      (StateSet.of_list (List.init n Fun.id)) dfa.d_accept in
    let initial_partitions =
      (if StateSet.is_empty dfa.d_accept then [] else [dfa.d_accept]) @
      (if StateSet.is_empty non_accept then [] else [non_accept]) in
    let partitions = ref (Array.of_list initial_partitions) in
    let changed = ref true in
    while !changed do
      changed := false;
      let new_parts = ref [] in
      Array.iter (fun part ->
        let representative = StateSet.min_elt part in
        let same = ref (StateSet.singleton representative) in
        let diff = ref StateSet.empty in
        StateSet.iter (fun s ->
          if s <> representative then begin
            let is_same = List.for_all (fun c ->
              let t1 = dfa_step dfa representative c in
              let t2 = dfa_step dfa s c in
              let find_part st =
                match st with
                | None -> -1
                | Some t ->
                  let idx = ref (-1) in
                  Array.iteri (fun i p ->
                    if StateSet.mem t p then idx := i
                  ) !partitions;
                  !idx
              in
              find_part t1 = find_part t2
            ) dfa.d_alphabet in
            if is_same then same := StateSet.add s !same
            else diff := StateSet.add s !diff
          end
        ) part;
        new_parts := !same :: !new_parts;
        if not (StateSet.is_empty !diff) then begin
          new_parts := !diff :: !new_parts;
          changed := true
        end
      ) !partitions;
      partitions := Array.of_list (List.rev !new_parts)
    done;
    let find_partition s =
      let idx = ref 0 in
      Array.iteri (fun i p ->
        if StateSet.mem s p then idx := i
      ) !partitions;
      !idx
    in
    let transitions = ref [] in
    let accept = ref [] in
    Array.iteri (fun i part ->
      let rep = StateSet.min_elt part in
      if StateSet.mem rep dfa.d_accept then accept := i :: !accept;
      List.iter (fun c ->
        match dfa_step dfa rep c with
        | Some t -> transitions := (i, c, find_partition t) :: !transitions
        | None -> ()
      ) dfa.d_alphabet
    ) !partitions;
    dfa_create ~states:(Array.length !partitions) ~alphabet:dfa.d_alphabet
      ~transitions:(List.rev !transitions)
      ~start:(find_partition dfa.d_start) ~accept:(List.rev !accept)

  (* ── DFA Complement ────────────────────────────────────────── *)

  let dfa_complement dfa =
    let dfa = dfa_complete dfa in
    let all = StateSet.of_list (List.init dfa.d_states Fun.id) in
    { dfa with d_accept = StateSet.diff all dfa.d_accept }

  (* ── Product Construction ──────────────────────────────────── *)

  type product_mode = Intersection | Union | Difference | SymDifference

  let dfa_product mode dfa1 dfa2 =
    let dfa1 = dfa_complete dfa1 in
    let dfa2 = dfa_complete dfa2 in
    let alphabet = dfa1.d_alphabet in
    let n2 = dfa2.d_states in
    let pair_to_id s1 s2 = s1 * n2 + s2 in
    let total = dfa1.d_states * n2 in
    let transitions = ref [] in
    let accept = ref [] in
    for s1 = 0 to dfa1.d_states - 1 do
      for s2 = 0 to dfa2.d_states - 1 do
        let id = pair_to_id s1 s2 in
        let a1 = StateSet.mem s1 dfa1.d_accept in
        let a2 = StateSet.mem s2 dfa2.d_accept in
        let is_accept = match mode with
          | Intersection -> a1 && a2
          | Union -> a1 || a2
          | Difference -> a1 && not a2
          | SymDifference -> (a1 && not a2) || (not a1 && a2)
        in
        if is_accept then accept := id :: !accept;
        List.iter (fun c ->
          match dfa_step dfa1 s1 c, dfa_step dfa2 s2 c with
          | Some t1, Some t2 ->
            transitions := (id, c, pair_to_id t1 t2) :: !transitions
          | _ -> ()
        ) alphabet
      done
    done;
    dfa_create ~states:total ~alphabet
      ~transitions:(List.rev !transitions)
      ~start:(pair_to_id dfa1.d_start dfa2.d_start)
      ~accept:(List.rev !accept)

  let dfa_intersection = dfa_product Intersection
  let dfa_union = dfa_product Union
  let dfa_difference = dfa_product Difference
  let dfa_sym_difference = dfa_product SymDifference

  (* ── Language Emptiness / Equivalence ──────────────────────── *)

  let dfa_reachable_states dfa =
    let rec bfs visited queue =
      match queue with
      | [] -> visited
      | s :: rest ->
        if StateSet.mem s visited then bfs visited rest
        else
          let visited = StateSet.add s visited in
          let nexts = List.filter_map (fun c -> dfa_step dfa s c) dfa.d_alphabet in
          bfs visited (rest @ nexts)
    in
    bfs StateSet.empty [dfa.d_start]

  let dfa_is_empty dfa =
    let reachable = dfa_reachable_states dfa in
    StateSet.is_empty (StateSet.inter reachable dfa.d_accept)

  let dfa_equivalent dfa1 dfa2 =
    dfa_is_empty (dfa_sym_difference dfa1 dfa2)

  let dfa_subset dfa1 dfa2 =
    dfa_is_empty (dfa_difference dfa1 dfa2)

  (* ── Dead State Removal ────────────────────────────────────── *)

  let dfa_remove_unreachable dfa =
    let reachable = dfa_reachable_states dfa in
    let states = StateSet.elements reachable in
    let remap = List.mapi (fun i s -> (s, i)) states in
    let find_new s = List.assoc s remap in
    let transitions = ref [] in
    List.iter (fun s ->
      List.iter (fun c ->
        match dfa_step dfa s c with
        | Some t when StateSet.mem t reachable ->
          transitions := (find_new s, c, find_new t) :: !transitions
        | _ -> ()
      ) dfa.d_alphabet
    ) states;
    let accept = StateSet.elements dfa.d_accept
      |> List.filter (fun s -> StateSet.mem s reachable)
      |> List.map find_new in
    dfa_create ~states:(List.length states) ~alphabet:dfa.d_alphabet
      ~transitions:(List.rev !transitions)
      ~start:(find_new dfa.d_start) ~accept

  (* ── NFA Reverse ───────────────────────────────────────────── *)

  let nfa_reverse nfa =
    let new_start = nfa.n_states in
    let rev_transitions = ref [] in
    StateMap.iter (fun s cm ->
      CharMap.iter (fun c targets ->
        StateSet.iter (fun t ->
          rev_transitions := (t, c, s) :: !rev_transitions
        ) targets
      ) cm
    ) nfa.n_trans;
    let rev_epsilon = ref [] in
    StateMap.iter (fun s targets ->
      StateSet.iter (fun t ->
        rev_epsilon := (t, s) :: !rev_epsilon
      ) targets
    ) nfa.n_epsilon;
    let eps_from_new = StateSet.fold (fun s acc ->
      (new_start, s) :: acc
    ) nfa.n_accept [] in
    nfa_create
      ~states:(nfa.n_states + 1)
      ~alphabet:nfa.n_alphabet
      ~transitions:(List.rev !rev_transitions)
      ~epsilon:(eps_from_new @ !rev_epsilon)
      ~start:new_start
      ~accept:[nfa.n_start]

  (* ── DFA Reverse (via NFA) ─────────────────────────────────── *)

  let dfa_reverse dfa =
    let transitions = ref [] in
    StateMap.iter (fun s cm ->
      CharMap.iter (fun c t ->
        transitions := (s, c, t) :: !transitions
      ) cm
    ) dfa.d_trans;
    let nfa = nfa_create
      ~states:dfa.d_states ~alphabet:dfa.d_alphabet
      ~transitions:(List.rev !transitions)
      ~epsilon:[] ~start:dfa.d_start
      ~accept:(StateSet.elements dfa.d_accept) in
    let rev_nfa = nfa_reverse nfa in
    nfa_to_dfa rev_nfa

  (* ── NFA Concatenation ─────────────────────────────────────── *)

  let nfa_concat nfa1 nfa2 =
    let offset = nfa1.n_states in
    let trans2 = ref [] in
    StateMap.iter (fun s cm ->
      CharMap.iter (fun c targets ->
        StateSet.iter (fun t ->
          trans2 := (s + offset, c, t + offset) :: !trans2
        ) targets
      ) cm
    ) nfa2.n_trans;
    let eps2 = ref [] in
    StateMap.iter (fun s targets ->
      StateSet.iter (fun t ->
        eps2 := (s + offset, t + offset) :: !eps2
      ) targets
    ) nfa2.n_epsilon;
    let trans1 = ref [] in
    StateMap.iter (fun s cm ->
      CharMap.iter (fun c targets ->
        StateSet.iter (fun t ->
          trans1 := (s, c, t) :: !trans1
        ) targets
      ) cm
    ) nfa1.n_trans;
    let eps1 = ref [] in
    StateMap.iter (fun s targets ->
      StateSet.iter (fun t ->
        eps1 := (s, t) :: !eps1
      ) targets
    ) nfa1.n_epsilon;
    let bridge = StateSet.fold (fun s acc ->
      (s, nfa2.n_start + offset) :: acc
    ) nfa1.n_accept [] in
    let alphabet = List.sort_uniq Char.compare
      (nfa1.n_alphabet @ nfa2.n_alphabet) in
    nfa_create
      ~states:(nfa1.n_states + nfa2.n_states)
      ~alphabet
      ~transitions:(!trans1 @ !trans2)
      ~epsilon:(!eps1 @ !eps2 @ bridge)
      ~start:nfa1.n_start
      ~accept:(List.map (fun s -> s + offset) (StateSet.elements nfa2.n_accept))

  (* ── NFA Union ─────────────────────────────────────────────── *)

  let nfa_union nfa1 nfa2 =
    let offset = nfa1.n_states in
    let new_start = nfa1.n_states + nfa2.n_states in
    let trans1 = ref [] in
    StateMap.iter (fun s cm ->
      CharMap.iter (fun c targets ->
        StateSet.iter (fun t -> trans1 := (s, c, t) :: !trans1) targets
      ) cm
    ) nfa1.n_trans;
    let eps1 = ref [] in
    StateMap.iter (fun s targets ->
      StateSet.iter (fun t -> eps1 := (s, t) :: !eps1) targets
    ) nfa1.n_epsilon;
    let trans2 = ref [] in
    StateMap.iter (fun s cm ->
      CharMap.iter (fun c targets ->
        StateSet.iter (fun t ->
          trans2 := (s + offset, c, t + offset) :: !trans2
        ) targets
      ) cm
    ) nfa2.n_trans;
    let eps2 = ref [] in
    StateMap.iter (fun s targets ->
      StateSet.iter (fun t ->
        eps2 := (s + offset, t + offset) :: !eps2
      ) targets
    ) nfa2.n_epsilon;
    let alphabet = List.sort_uniq Char.compare
      (nfa1.n_alphabet @ nfa2.n_alphabet) in
    let accept1 = StateSet.elements nfa1.n_accept in
    let accept2 = List.map (fun s -> s + offset) (StateSet.elements nfa2.n_accept) in
    nfa_create
      ~states:(nfa1.n_states + nfa2.n_states + 1)
      ~alphabet
      ~transitions:(!trans1 @ !trans2)
      ~epsilon:(!eps1 @ !eps2 @
        [(new_start, nfa1.n_start); (new_start, nfa2.n_start + offset)])
      ~start:new_start
      ~accept:(accept1 @ accept2)

  (* ── NFA Kleene Star ───────────────────────────────────────── *)

  let nfa_star nfa =
    let new_start = nfa.n_states in
    let trans = ref [] in
    StateMap.iter (fun s cm ->
      CharMap.iter (fun c targets ->
        StateSet.iter (fun t -> trans := (s, c, t) :: !trans) targets
      ) cm
    ) nfa.n_trans;
    let eps = ref [(new_start, nfa.n_start)] in
    StateMap.iter (fun s targets ->
      StateSet.iter (fun t -> eps := (s, t) :: !eps) targets
    ) nfa.n_epsilon;
    StateSet.iter (fun s ->
      eps := (s, nfa.n_start) :: !eps
    ) nfa.n_accept;
    nfa_create
      ~states:(nfa.n_states + 1)
      ~alphabet:nfa.n_alphabet
      ~transitions:!trans
      ~epsilon:!eps
      ~start:new_start
      ~accept:[new_start]

  (* ── String Generation ─────────────────────────────────────── *)

  let dfa_accepted_strings dfa max_len =
    let results = ref [] in
    let rec go state path len =
      if StateSet.mem state dfa.d_accept then
        results := (String.concat "" (List.rev_map (String.make 1) path)) :: !results;
      if len < max_len then
        List.iter (fun c ->
          match dfa_step dfa state c with
          | Some next -> go next (c :: path) (len + 1)
          | None -> ()
        ) dfa.d_alphabet
    in
    go dfa.d_start [] 0;
    List.rev !results

  let dfa_shortest_accepted dfa =
    let queue = Queue.create () in
    Queue.push (dfa.d_start, []) queue;
    let visited = Hashtbl.create 16 in
    Hashtbl.add visited dfa.d_start true;
    let result = ref None in
    while not (Queue.is_empty queue) && !result = None do
      let (state, path) = Queue.pop queue in
      if StateSet.mem state dfa.d_accept then
        result := Some (String.concat "" (List.rev_map (String.make 1) path))
      else
        List.iter (fun c ->
          match dfa_step dfa state c with
          | Some next when not (Hashtbl.mem visited next) ->
            Hashtbl.add visited next true;
            Queue.push (next, c :: path) queue
          | _ -> ()
        ) dfa.d_alphabet
    done;
    !result

  (* ── Automaton Statistics ──────────────────────────────────── *)

  type dfa_stats = {
    num_states: int;
    num_transitions: int;
    num_accept: int;
    num_reachable: int;
    is_complete: bool;
    is_empty_language: bool;
    alphabet_size: int;
  }

  let dfa_stats dfa =
    let reachable = dfa_reachable_states dfa in
    let num_transitions = StateMap.fold (fun _ cm acc ->
      acc + CharMap.cardinal cm) dfa.d_trans 0 in
    let is_complete =
      let expected = dfa.d_states * List.length dfa.d_alphabet in
      num_transitions >= expected in
    { num_states = dfa.d_states;
      num_transitions;
      num_accept = StateSet.cardinal dfa.d_accept;
      num_reachable = StateSet.cardinal reachable;
      is_complete;
      is_empty_language = dfa_is_empty dfa;
      alphabet_size = List.length dfa.d_alphabet }

  (* ── DOT Export ────────────────────────────────────────────── *)

  let dfa_to_dot dfa =
    let buf = Buffer.create 256 in
    Buffer.add_string buf "digraph DFA {\n";
    Buffer.add_string buf "  rankdir=LR;\n";
    Buffer.add_string buf "  node [shape=circle];\n";
    StateSet.iter (fun s ->
      Buffer.add_string buf (Printf.sprintf "  %d [shape=doublecircle];\n" s)
    ) dfa.d_accept;
    Buffer.add_string buf "  start [shape=point];\n";
    Buffer.add_string buf (Printf.sprintf "  start -> %d;\n" dfa.d_start);
    StateMap.iter (fun s cm ->
      CharMap.iter (fun c t ->
        Buffer.add_string buf
          (Printf.sprintf "  %d -> %d [label=\"%c\"];\n" s t c)
      ) cm
    ) dfa.d_trans;
    Buffer.add_string buf "}\n";
    Buffer.contents buf

  let nfa_to_dot nfa =
    let buf = Buffer.create 256 in
    Buffer.add_string buf "digraph NFA {\n";
    Buffer.add_string buf "  rankdir=LR;\n";
    Buffer.add_string buf "  node [shape=circle];\n";
    StateSet.iter (fun s ->
      Buffer.add_string buf (Printf.sprintf "  %d [shape=doublecircle];\n" s)
    ) nfa.n_accept;
    Buffer.add_string buf "  start [shape=point];\n";
    Buffer.add_string buf (Printf.sprintf "  start -> %d;\n" nfa.n_start);
    StateMap.iter (fun s cm ->
      CharMap.iter (fun c targets ->
        StateSet.iter (fun t ->
          Buffer.add_string buf
            (Printf.sprintf "  %d -> %d [label=\"%c\"];\n" s t c)
        ) targets
      ) cm
    ) nfa.n_trans;
    StateMap.iter (fun s targets ->
      StateSet.iter (fun t ->
        Buffer.add_string buf
          (Printf.sprintf "  %d -> %d [label=\"e\", style=dashed];\n" s t)
      ) targets
    ) nfa.n_epsilon;
    Buffer.add_string buf "}\n";
    Buffer.contents buf

  (* ── Text Report ───────────────────────────────────────────── *)

  let dfa_report dfa =
    let s = dfa_stats dfa in
    let lines = [
      "=== DFA Report ===";
      Printf.sprintf "States:       %d (%d reachable)" s.num_states s.num_reachable;
      Printf.sprintf "Alphabet:     %d symbols" s.alphabet_size;
      Printf.sprintf "Transitions:  %d" s.num_transitions;
      Printf.sprintf "Accept:       %d states [%s]" s.num_accept
        (String.concat "," (List.map string_of_int (StateSet.elements dfa.d_accept)));
      Printf.sprintf "Start:        %d" dfa.d_start;
      Printf.sprintf "Complete:     %b" s.is_complete;
      Printf.sprintf "Empty lang:   %b" s.is_empty_language;
    ] in
    String.concat "\n" lines

end

(* ═══════════════════════════════════════════════════════════════ *)
(* TESTS                                                          *)
(* ═══════════════════════════════════════════════════════════════ *)

let () =
  let open Automata in
  let passed = ref 0 in
  let failed = ref 0 in
  let test name f =
    try
      f ();
      incr passed
    with e ->
      incr failed;
      Printf.printf "FAIL: %s -- %s\n" name (Printexc.to_string e)
  in
  let assert_true msg b = if not b then failwith msg in
  let assert_false msg b = if b then failwith msg in
  let assert_eq msg a b = if a <> b then failwith (Printf.sprintf "%s: %d <> %d" msg a b) in

  let ends_b = dfa_create ~states:2 ~alphabet:['a';'b']
    ~transitions:[(0,'a',0);(0,'b',1);(1,'a',0);(1,'b',1)]
    ~start:0 ~accept:[1] in

  test "dfa accepts 'b'" (fun () ->
    assert_true "should accept" (dfa_accepts ends_b "b"));
  test "dfa accepts 'ab'" (fun () ->
    assert_true "should accept" (dfa_accepts ends_b "ab"));
  test "dfa accepts 'aab'" (fun () ->
    assert_true "should accept" (dfa_accepts ends_b "aab"));
  test "dfa accepts 'bab'" (fun () ->
    assert_true "should accept" (dfa_accepts ends_b "bab"));
  test "dfa rejects empty" (fun () ->
    assert_false "should reject" (dfa_accepts ends_b ""));
  test "dfa rejects 'a'" (fun () ->
    assert_false "should reject" (dfa_accepts ends_b "a"));
  test "dfa rejects 'ba'" (fun () ->
    assert_false "should reject" (dfa_accepts ends_b "ba"));

  let just_ab = dfa_create ~states:3 ~alphabet:['a';'b']
    ~transitions:[(0,'a',1);(1,'b',2)]
    ~start:0 ~accept:[2] in

  test "dfa accepts 'ab' exactly" (fun () ->
    assert_true "should accept" (dfa_accepts just_ab "ab"));
  test "dfa rejects 'a' (just_ab)" (fun () ->
    assert_false "should reject" (dfa_accepts just_ab "a"));
  test "dfa rejects 'aba'" (fun () ->
    assert_false "should reject" (dfa_accepts just_ab "aba"));
  test "dfa rejects empty (just_ab)" (fun () ->
    assert_false "should reject" (dfa_accepts just_ab ""));

  let contains_ab = nfa_create ~states:3 ~alphabet:['a';'b']
    ~transitions:[(0,'a',0);(0,'b',0);(0,'a',1);(1,'b',2);(2,'a',2);(2,'b',2)]
    ~epsilon:[] ~start:0 ~accept:[2] in

  test "nfa accepts 'ab'" (fun () ->
    assert_true "should accept" (nfa_accepts contains_ab "ab"));
  test "nfa accepts 'aab'" (fun () ->
    assert_true "should accept" (nfa_accepts contains_ab "aab"));
  test "nfa accepts 'bab'" (fun () ->
    assert_true "should accept" (nfa_accepts contains_ab "bab"));
  test "nfa accepts 'abba'" (fun () ->
    assert_true "should accept" (nfa_accepts contains_ab "abba"));
  test "nfa rejects empty" (fun () ->
    assert_false "should reject" (nfa_accepts contains_ab ""));
  test "nfa rejects 'a'" (fun () ->
    assert_false "should reject" (nfa_accepts contains_ab "a"));
  test "nfa rejects 'ba'" (fun () ->
    assert_false "should reject" (nfa_accepts contains_ab "ba"));
  test "nfa rejects 'bbb'" (fun () ->
    assert_false "should reject" (nfa_accepts contains_ab "bbb"));

  let eps_nfa = nfa_create ~states:3 ~alphabet:['a']
    ~transitions:[(0,'a',1);(2,'a',2)]
    ~epsilon:[(1,2)] ~start:0 ~accept:[2] in

  test "epsilon nfa accepts 'a'" (fun () ->
    assert_true "should accept" (nfa_accepts eps_nfa "a"));
  test "epsilon nfa accepts 'aa'" (fun () ->
    assert_true "should accept" (nfa_accepts eps_nfa "aa"));
  test "epsilon nfa accepts 'aaa'" (fun () ->
    assert_true "should accept" (nfa_accepts eps_nfa "aaa"));
  test "epsilon nfa rejects empty" (fun () ->
    assert_false "should reject" (nfa_accepts eps_nfa ""));

  test "nfa_to_dfa preserves language" (fun () ->
    let dfa = nfa_to_dfa contains_ab in
    assert_true "ab" (dfa_accepts dfa "ab");
    assert_true "aab" (dfa_accepts dfa "aab");
    assert_true "bab" (dfa_accepts dfa "bab");
    assert_false "empty" (dfa_accepts dfa "");
    assert_false "a" (dfa_accepts dfa "a");
    assert_false "ba" (dfa_accepts dfa "ba"));

  test "nfa_to_dfa with epsilon" (fun () ->
    let dfa = nfa_to_dfa eps_nfa in
    assert_true "a" (dfa_accepts dfa "a");
    assert_true "aa" (dfa_accepts dfa "aa");
    assert_false "empty" (dfa_accepts dfa ""));

  let redundant = dfa_create ~states:4 ~alphabet:['a';'b']
    ~transitions:[
      (0,'a',1);(0,'b',2);
      (1,'a',3);(1,'b',3);
      (2,'a',3);(2,'b',3);
      (3,'a',3);(3,'b',3)]
    ~start:0 ~accept:[3] in

  test "minimization reduces states" (fun () ->
    let min_dfa = dfa_minimize redundant in
    assert_true "fewer states" (min_dfa.d_states <= redundant.d_states));

  test "minimization preserves language" (fun () ->
    let min_dfa = dfa_minimize redundant in
    assert_true "aa" (dfa_accepts min_dfa "aa");
    assert_true "ab" (dfa_accepts min_dfa "ab");
    assert_true "ba" (dfa_accepts min_dfa "ba");
    assert_true "bb" (dfa_accepts min_dfa "bb");
    assert_true "aaa" (dfa_accepts min_dfa "aaa");
    assert_false "empty" (dfa_accepts min_dfa "");
    assert_false "a" (dfa_accepts min_dfa "a");
    assert_false "b" (dfa_accepts min_dfa "b"));

  test "minimize already minimal" (fun () ->
    let min = dfa_minimize ends_b in
    assert_eq "states" min.d_states 2);

  test "complement flips acceptance" (fun () ->
    let comp = dfa_complement ends_b in
    assert_true "empty accepted" (dfa_accepts comp "");
    assert_true "a accepted" (dfa_accepts comp "a");
    assert_false "b rejected" (dfa_accepts comp "b");
    assert_false "ab rejected" (dfa_accepts comp "ab"));

  test "double complement = original" (fun () ->
    let comp2 = dfa_complement (dfa_complement ends_b) in
    assert_true "same language" (dfa_equivalent comp2 ends_b));

  let starts_a = dfa_create ~states:3 ~alphabet:['a';'b']
    ~transitions:[(0,'a',1);(0,'b',2);(1,'a',1);(1,'b',1);(2,'a',2);(2,'b',2)]
    ~start:0 ~accept:[1] in

  test "intersection" (fun () ->
    let inter = dfa_intersection starts_a ends_b in
    assert_true "ab" (dfa_accepts inter "ab");
    assert_true "aab" (dfa_accepts inter "aab");
    assert_false "b" (dfa_accepts inter "b");
    assert_false "ba" (dfa_accepts inter "ba");
    assert_false "a" (dfa_accepts inter "a"));

  test "union" (fun () ->
    let u = dfa_union starts_a ends_b in
    assert_true "a" (dfa_accepts u "a");
    assert_true "b" (dfa_accepts u "b");
    assert_true "ab" (dfa_accepts u "ab");
    assert_false "empty" (dfa_accepts u "");
    assert_false "ba" (dfa_accepts u "ba"));

  test "difference" (fun () ->
    let d = dfa_difference starts_a ends_b in
    assert_true "a" (dfa_accepts d "a");
    assert_true "aa" (dfa_accepts d "aa");
    assert_false "ab" (dfa_accepts d "ab");
    assert_false "b" (dfa_accepts d "b"));

  test "sym_difference" (fun () ->
    let sd = dfa_sym_difference starts_a ends_b in
    assert_true "a" (dfa_accepts sd "a");
    assert_true "b" (dfa_accepts sd "b");
    assert_false "ab" (dfa_accepts sd "ab");
    assert_false "empty" (dfa_accepts sd ""));

  test "dfa equivalent to itself" (fun () ->
    assert_true "self equivalent" (dfa_equivalent ends_b ends_b));

  test "dfa not equivalent to complement" (fun () ->
    assert_false "not equivalent" (dfa_equivalent ends_b (dfa_complement ends_b)));

  test "minimized equivalent to original" (fun () ->
    assert_true "equivalent" (dfa_equivalent redundant (dfa_minimize redundant)));

  test "subset reflexive" (fun () ->
    assert_true "self subset" (dfa_subset ends_b ends_b));

  test "intersection subset of operands" (fun () ->
    let inter = dfa_intersection starts_a ends_b in
    assert_true "subset of starts_a" (dfa_subset inter starts_a);
    assert_true "subset of ends_b" (dfa_subset inter ends_b));

  test "non-empty language" (fun () ->
    assert_false "not empty" (dfa_is_empty ends_b));

  test "empty intersection" (fun () ->
    let empty = dfa_intersection starts_a (dfa_complement starts_a) in
    assert_true "empty" (dfa_is_empty empty));

  test "generate accepted strings" (fun () ->
    let strings = dfa_accepted_strings ends_b 2 in
    assert_true "contains b" (List.mem "b" strings);
    assert_true "contains ab" (List.mem "ab" strings);
    assert_true "contains bb" (List.mem "bb" strings);
    assert_false "no a" (List.mem "a" strings));

  test "shortest accepted string" (fun () ->
    let s = dfa_shortest_accepted ends_b in
    assert_true "found" (s = Some "b"));

  test "shortest for just_ab" (fun () ->
    let s = dfa_shortest_accepted just_ab in
    assert_true "found" (s = Some "ab"));

  let just_a = nfa_create ~states:2 ~alphabet:['a';'b']
    ~transitions:[(0,'a',1)] ~epsilon:[] ~start:0 ~accept:[1] in
  let just_b = nfa_create ~states:2 ~alphabet:['a';'b']
    ~transitions:[(0,'b',1)] ~epsilon:[] ~start:0 ~accept:[1] in

  test "nfa concat ab" (fun () ->
    let ab = nfa_concat just_a just_b in
    assert_true "accepts ab" (nfa_accepts ab "ab");
    assert_false "rejects a" (nfa_accepts ab "a");
    assert_false "rejects b" (nfa_accepts ab "b");
    assert_false "rejects ba" (nfa_accepts ab "ba");
    assert_false "rejects empty" (nfa_accepts ab ""));

  test "nfa union a|b" (fun () ->
    let a_or_b = nfa_union just_a just_b in
    assert_true "accepts a" (nfa_accepts a_or_b "a");
    assert_true "accepts b" (nfa_accepts a_or_b "b");
    assert_false "rejects ab" (nfa_accepts a_or_b "ab");
    assert_false "rejects empty" (nfa_accepts a_or_b ""));

  test "nfa star a*" (fun () ->
    let a_star = nfa_star just_a in
    assert_true "accepts empty" (nfa_accepts a_star "");
    assert_true "accepts a" (nfa_accepts a_star "a");
    assert_true "accepts aa" (nfa_accepts a_star "aa");
    assert_true "accepts aaa" (nfa_accepts a_star "aaa");
    assert_false "rejects b" (nfa_accepts a_star "b");
    assert_false "rejects ab" (nfa_accepts a_star "ab"));

  test "nfa reverse of ab accepts ba" (fun () ->
    let ab = nfa_concat just_a just_b in
    let rev = nfa_reverse ab in
    assert_true "accepts ba" (nfa_accepts rev "ba");
    assert_false "rejects ab" (nfa_accepts rev "ab"));

  test "dfa reverse ends_b -> starts_b" (fun () ->
    let rev = dfa_reverse ends_b in
    assert_true "b" (dfa_accepts rev "b");
    assert_true "ba" (dfa_accepts rev "ba");
    assert_true "baa" (dfa_accepts rev "baa");
    assert_false "a" (dfa_accepts rev "a");
    assert_false "ab" (dfa_accepts rev "ab");
    assert_false "empty" (dfa_accepts rev ""));

  let with_unreachable = dfa_create ~states:4 ~alphabet:['a']
    ~transitions:[(0,'a',1);(1,'a',0);(2,'a',3);(3,'a',2)]
    ~start:0 ~accept:[1] in

  test "remove unreachable" (fun () ->
    let cleaned = dfa_remove_unreachable with_unreachable in
    assert_eq "2 states" cleaned.d_states 2;
    assert_true "still accepts a" (dfa_accepts cleaned "a"));

  test "complete adds sink state" (fun () ->
    let comp = dfa_complete just_ab in
    assert_true "more states" (comp.d_states > just_ab.d_states);
    assert_true "still accepts ab" (dfa_accepts comp "ab");
    assert_false "rejects a" (dfa_accepts comp "a"));

  test "stats correct" (fun () ->
    let s = dfa_stats ends_b in
    assert_eq "states" s.num_states 2;
    assert_eq "accept" s.num_accept 1;
    assert_eq "reachable" s.num_reachable 2;
    assert_true "complete" s.is_complete;
    assert_false "not empty" s.is_empty_language);

  test "dfa to dot" (fun () ->
    let dot = dfa_to_dot ends_b in
    assert_true "has digraph" (String.length dot > 20));

  test "nfa to dot" (fun () ->
    let dot = nfa_to_dot contains_ab in
    assert_true "has digraph" (String.length dot > 20));

  test "report generated" (fun () ->
    let r = dfa_report ends_b in
    assert_true "has DFA Report" (String.length r > 50));

  test "accepts_all batch" (fun () ->
    let results = dfa_accepts_all ends_b ["b";"ab";"a";"ba"] in
    assert_true "b" (List.assoc "b" results);
    assert_true "ab" (List.assoc "ab" results);
    assert_false "a" (List.assoc "a" results);
    assert_false "ba" (List.assoc "ba" results));

  test "complex: (a|b)*ab determinize and minimize" (fun () ->
    let a_or_b = nfa_union just_a just_b in
    let star_ab = nfa_star a_or_b in
    let ab = nfa_concat just_a just_b in
    let lang = nfa_concat star_ab ab in
    assert_true "ab" (nfa_accepts lang "ab");
    assert_true "aab" (nfa_accepts lang "aab");
    assert_true "bab" (nfa_accepts lang "bab");
    assert_true "abab" (nfa_accepts lang "abab");
    assert_false "empty" (nfa_accepts lang "");
    assert_false "a" (nfa_accepts lang "a");
    assert_false "ba" (nfa_accepts lang "ba");
    let dfa = nfa_to_dfa lang in
    let min_dfa = dfa_minimize dfa in
    assert_true "min accepts ab" (dfa_accepts min_dfa "ab");
    assert_true "min accepts bab" (dfa_accepts min_dfa "bab");
    assert_false "min rejects ba" (dfa_accepts min_dfa "ba");
    assert_true "equivalent" (dfa_equivalent dfa min_dfa);
    assert_true "fewer or equal states" (min_dfa.d_states <= dfa.d_states));

  test "DeMorgan: complement(A int B) = complement(A) union complement(B)" (fun () ->
    let lhs = dfa_complement (dfa_intersection starts_a ends_b) in
    let rhs = dfa_union (dfa_complement starts_a) (dfa_complement ends_b) in
    assert_true "DeMorgan" (dfa_equivalent lhs rhs));

  test "A union complement(A) = universal" (fun () ->
    let all = dfa_union ends_b (dfa_complement ends_b) in
    assert_true "empty" (dfa_accepts all "");
    assert_true "a" (dfa_accepts all "a");
    assert_true "b" (dfa_accepts all "b");
    assert_true "ab" (dfa_accepts all "ab"));

  test "A inter complement(A) = empty" (fun () ->
    let empty = dfa_intersection ends_b (dfa_complement ends_b) in
    assert_true "empty" (dfa_is_empty empty));

  let chain = nfa_create ~states:4 ~alphabet:['a']
    ~transitions:[(3,'a',3)] ~epsilon:[(0,1);(1,2);(2,3)]
    ~start:0 ~accept:[3] in

  test "epsilon chain closure" (fun () ->
    assert_true "accepts empty" (nfa_accepts chain "");
    assert_true "accepts a" (nfa_accepts chain "a");
    assert_true "accepts aaa" (nfa_accepts chain "aaa"));

  let multi_accept = nfa_create ~states:3 ~alphabet:['a';'b']
    ~transitions:[(0,'a',1);(0,'b',2)]
    ~epsilon:[] ~start:0 ~accept:[1;2] in

  test "multi accept nfa" (fun () ->
    assert_true "a" (nfa_accepts multi_accept "a");
    assert_true "b" (nfa_accepts multi_accept "b");
    assert_false "empty" (nfa_accepts multi_accept ""));

  Printf.printf "\nautomata.ml: %d passed, %d failed, %d total\n"
    !passed !failed (!passed + !failed);
  if !failed > 0 then exit 1
