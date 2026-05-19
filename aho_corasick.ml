(* aho_corasick.ml — Multi-Pattern String Matching *)
(* Aho–Corasick builds a trie over a dictionary of patterns, augments it *)
(* with BFS-computed failure links (and dictionary suffix links), and    *)
(* then scans any input text in a single linear pass, reporting every    *)
(* occurrence of every pattern.                                          *)
(*                                                                       *)
(* Complexity:                                                           *)
(*   build : O(sum of pattern lengths)                                   *)
(*   search: O(n + m + z)  where n=|text|, m=sum|patterns|, z=#matches   *)
(*                                                                       *)
(* No allocation per character in the hot search loop beyond match       *)
(* reporting itself; this is asymptotically optimal.                     *)
(*                                                                       *)
(* Demonstrates: imperative arrays, Hashtbl, BFS via Queue, mutable      *)
(* records, functional API on top of an imperative core, and "build      *)
(* once, query many" automaton design.                                   *)

module AhoCorasick = struct

  (* Each automaton state is identified by an int.  State 0 is the root. *)
  (* We store transitions in a per-state Hashtbl rather than a dense     *)
  (* array so the alphabet can be the full 0..255 byte range without     *)
  (* paying O(256) memory per state.  After build_failure_links, the     *)
  (* `goto` table is *not* path-compressed (we do not collapse failure   *)
  (* edges into goto), so memory stays O(sum |patterns|).                *)
  type state = {
    mutable goto    : (char, int) Hashtbl.t; (* labelled child edges    *)
    mutable fail    : int;                   (* failure link            *)
    mutable dict    : int;                   (* dict-suffix link (-1)   *)
    mutable outputs : int list;              (* pattern indices ending  *)
                                             (* exactly at this state   *)
  }

  type t = {
    mutable states   : state array;          (* index -> state          *)
    mutable n_states : int;                  (* live count              *)
    patterns         : string array;         (* original dictionary     *)
    mutable built    : bool;                 (* failure links computed? *)
  }

  (* A reported match: pattern index, pattern text, and the 0-based      *)
  (* starting offset in the searched text.                               *)
  type match_ = {
    pattern_index : int;
    pattern       : string;
    start_pos     : int;
  }

  (* ---- Internal helpers ---- *)

  let new_state () =
    { goto    = Hashtbl.create 4
    ; fail    = 0
    ; dict    = -1
    ; outputs = []
    }

  let alloc_state ac =
    if ac.n_states >= Array.length ac.states then begin
      let new_cap = max 16 (Array.length ac.states * 2) in
      let new_arr = Array.make new_cap (new_state ()) in
      Array.blit ac.states 0 new_arr 0 ac.n_states;
      for i = ac.n_states to new_cap - 1 do
        new_arr.(i) <- new_state ()
      done;
      ac.states <- new_arr
    end;
    let id = ac.n_states in
    ac.n_states <- id + 1;
    id

  (* ---- Construction ---- *)

  (** [create patterns] builds an Aho–Corasick automaton for the given   *)
  (** dictionary.  Empty patterns are ignored (they would match at every *)
  (** position, which is rarely useful and never what callers expect).   *)
  let create patterns =
    let patterns = Array.of_list patterns in
    let initial_cap = 16 in
    let states = Array.init initial_cap (fun _ -> new_state ()) in
    let ac =
      { states; n_states = 0; patterns; built = false }
    in
    let _root = alloc_state ac in   (* state 0 *)
    (* Insert each non-empty pattern into the trie. *)
    Array.iteri (fun pi pat ->
      if String.length pat > 0 then begin
        let node = ref 0 in
        String.iter (fun c ->
          let s = ac.states.(!node) in
          match Hashtbl.find_opt s.goto c with
          | Some next -> node := next
          | None ->
            let next = alloc_state ac in
            Hashtbl.add ac.states.(!node).goto c next;
            node := next
        ) pat;
        let final = ac.states.(!node) in
        final.outputs <- pi :: final.outputs
      end
    ) patterns;
    ac

  (** [build_failure_links ac] computes the BFS failure function and     *)
  (** dictionary-suffix links.  Idempotent: safe to call more than once. *)
  let build_failure_links ac =
    if not ac.built then begin
      let q = Queue.create () in
      (* All depth-1 nodes fail to root. *)
      let root = ac.states.(0) in
      Hashtbl.iter (fun _ child ->
        ac.states.(child).fail <- 0;
        Queue.push child q
      ) root.goto;
      while not (Queue.is_empty q) do
        let u = Queue.pop q in
        let su = ac.states.(u) in
        Hashtbl.iter (fun c v ->
          Queue.push v q;
          (* Walk the failure chain of u to find the longest proper     *)
          (* suffix that also has a c-transition.                       *)
          let f = ref su.fail in
          while !f <> 0 && not (Hashtbl.mem ac.states.(!f).goto c) do
            f := ac.states.(!f).fail
          done;
          let new_fail =
            match Hashtbl.find_opt ac.states.(!f).goto c with
            | Some next when next <> v -> next
            | _ -> 0
          in
          let sv = ac.states.(v) in
          sv.fail <- new_fail;
          (* Merge outputs along the failure chain via dict-suffix link.*)
          let fv = ac.states.(new_fail) in
          if fv.outputs <> [] then sv.dict <- new_fail
          else sv.dict <- fv.dict
        ) su.goto
      done;
      ac.built <- true
    end

  (* ---- Search ---- *)

  let goto_step ac state c =
    let s = ref state in
    while
      !s <> 0 && not (Hashtbl.mem ac.states.(!s).goto c)
    do
      s := ac.states.(!s).fail
    done;
    match Hashtbl.find_opt ac.states.(!s).goto c with
    | Some next -> next
    | None      -> 0       (* fell back to root with no edge *)

  (** [search ac text] returns every match of every dictionary pattern   *)
  (** inside [text], in left-to-right, pattern-index-tiebroken order.    *)
  (** Automatically calls {!build_failure_links} the first time.         *)
  let search ac text =
    build_failure_links ac;
    let out = ref [] in
    let state = ref 0 in
    String.iteri (fun i c ->
      state := goto_step ac !state c;
      (* Emit outputs at current state, then walk dict-suffix links.    *)
      let emit node =
        List.iter (fun pi ->
          let plen = String.length ac.patterns.(pi) in
          out := { pattern_index = pi
                 ; pattern       = ac.patterns.(pi)
                 ; start_pos     = i - plen + 1
                 } :: !out
        ) (ac.states.(node).outputs)
      in
      emit !state;
      let d = ref (ac.states.(!state).dict) in
      while !d <> -1 do
        emit !d;
        d := ac.states.(!d).dict
      done
    ) text;
    List.sort (fun a b ->
      let c = compare a.start_pos b.start_pos in
      if c <> 0 then c else compare a.pattern_index b.pattern_index
    ) (List.rev !out)

  (** [contains_any ac text] is true iff at least one pattern appears in *)
  (** [text].  Stops at the first hit — O(n) worst case but typically    *)
  (** much faster on negatives because of early exit.                    *)
  let contains_any ac text =
    build_failure_links ac;
    let state = ref 0 in
    let len = String.length text in
    let i = ref 0 in
    let found = ref false in
    while not !found && !i < len do
      state := goto_step ac !state (String.unsafe_get text !i);
      if (ac.states.(!state).outputs <> [])
         || ac.states.(!state).dict <> -1
      then found := true;
      incr i
    done;
    !found

  (** [num_states ac] returns the number of trie states.  Useful for     *)
  (** sanity-checking memory budget on very large dictionaries.          *)
  let num_states ac = ac.n_states

  (** [num_patterns ac] returns the dictionary size (including any empty *)
  (** patterns that were silently ignored during {!create}).             *)
  let num_patterns ac = Array.length ac.patterns
end

(* ---- Demo ---- *)

let () =
  let open AhoCorasick in
  let patterns = ["he"; "she"; "his"; "hers"] in
  let ac = create patterns in
  let text = "ushers" in
  Printf.printf "Aho-Corasick demo\n";
  Printf.printf "  patterns : [%s]\n"
    (String.concat "; " (List.map (Printf.sprintf "%S") patterns));
  Printf.printf "  text     : %S\n" text;
  Printf.printf "  states   : %d\n" (num_states ac);
  let matches = search ac text in
  Printf.printf "  matches  : %d\n" (List.length matches);
  List.iter (fun m ->
    Printf.printf "    @%d  %S  (pattern #%d)\n"
      m.start_pos m.pattern m.pattern_index
  ) matches;

  (* Larger demo: scan a sentence for several keywords. *)
  let kws = ["ocaml"; "functional"; "pattern"; "type"; "match"] in
  let ac2 = create kws in
  let sentence =
    "ocaml is a functional language with pattern matching and a \
     powerful type system; functional pattern matching is great."
  in
  Printf.printf "\nKeyword scan\n";
  Printf.printf "  sentence : %S\n" sentence;
  let hits = search ac2 sentence in
  Printf.printf "  hits     : %d\n" (List.length hits);
  List.iter (fun m ->
    Printf.printf "    @%3d  %S\n" m.start_pos m.pattern
  ) hits;

  (* Quick early-exit check. *)
  let ac3 = create ["zebra"; "giraffe"] in
  Printf.printf "\ncontains_any %S = %b\n"
    "the quick brown fox"
    (contains_any ac3 "the quick brown fox");
  Printf.printf "contains_any %S = %b\n"
    "I saw a giraffe today"
    (contains_any ac3 "I saw a giraffe today")
