(* CCS Process Calculus Simulator
   ===============================
   An implementation of Milner's Calculus of Communicating Systems (CCS)
   for modeling and analyzing concurrent communicating processes.

   Features:
   - Full CCS syntax: prefix, choice, parallel, restriction, relabeling
   - Labeled Transition System (LTS) generation
   - Strong and weak bisimulation checking
   - Trace equivalence
   - Deadlock detection
   - Reachability analysis
   - ASCII visualization of LTS
   - Built-in examples (mutex, handshake, buffer, scheduler)
   - Interactive REPL

   Agency: Processes as autonomous communicating agents that synchronize
   on shared channels — a foundation for modeling multi-agent systems.

   Usage: ocaml process_calculus.ml
*)

(* ══════════════════════════════════════════════════════════════════════
   Core Types
   ══════════════════════════════════════════════════════════════════════ *)

type action =
  | Send of string       (* a   — output on channel a *)
  | Recv of string       (* a'  — input on channel a *)
  | Tau                  (* τ   — internal/silent action *)

type process =
  | Nil                                    (* 0 — terminated process *)
  | Prefix of action * process             (* a.P — action prefix *)
  | Choice of process * process            (* P + Q — nondeterministic choice *)
  | Parallel of process * process          (* P | Q — parallel composition *)
  | Restrict of process * string list      (* P \ {a,b} — restriction *)
  | Relabel of process * (string * string) list  (* P[b/a] — relabeling *)
  | Ident of string                        (* process identifier for recursion *)

(* A process definition: name = process *)
type definition = {
  def_name: string;
  def_body: process;
}

type environment = definition list

(* LTS types *)
type state_id = int

type lts_transition = {
  src: state_id;
  act: action;
  dst: state_id;
}

type lts = {
  states: (state_id * process) list;
  transitions: lts_transition list;
  initial: state_id;
}

(* ══════════════════════════════════════════════════════════════════════
   Pretty Printing
   ══════════════════════════════════════════════════════════════════════ *)

let action_to_string = function
  | Send ch -> ch
  | Recv ch -> ch ^ "'"
  | Tau -> "τ"

let rec process_to_string = function
  | Nil -> "0"
  | Prefix (a, p) ->
    action_to_string a ^ "." ^ process_to_string_atom p
  | Choice (p, q) ->
    process_to_string_sum p ^ " + " ^ process_to_string_sum q
  | Parallel (p, q) ->
    process_to_string_par p ^ " | " ^ process_to_string_par q
  | Restrict (p, chans) ->
    process_to_string_atom p ^ " \\ {" ^ String.concat "," chans ^ "}"
  | Relabel (p, rels) ->
    let rel_strs = List.map (fun (a, b) -> b ^ "/" ^ a) rels in
    process_to_string_atom p ^ "[" ^ String.concat "," rel_strs ^ "]"
  | Ident name -> name

and process_to_string_atom = function
  | Nil | Ident _ as p -> process_to_string p
  | p -> "(" ^ process_to_string p ^ ")"

and process_to_string_sum = function
  | Choice _ as p -> process_to_string p
  | p -> process_to_string p

and process_to_string_par = function
  | Parallel _ as p -> process_to_string p
  | Choice _ as p -> "(" ^ process_to_string p ^ ")"
  | p -> process_to_string p

(* ══════════════════════════════════════════════════════════════════════
   Action Helpers
   ══════════════════════════════════════════════════════════════════════ *)

let complement = function
  | Send ch -> Some (Recv ch)
  | Recv ch -> Some (Send ch)
  | Tau -> None

let is_complement a b =
  match a, b with
  | Send ch1, Recv ch2 | Recv ch1, Send ch2 -> ch1 = ch2
  | _ -> false

let relabel_action rels a =
  match a with
  | Send ch ->
    (match List.assoc_opt ch rels with
     | Some ch' -> Send ch'
     | None -> a)
  | Recv ch ->
    (match List.assoc_opt ch rels with
     | Some ch' -> Recv ch'
     | None -> a)
  | Tau -> Tau

let action_channel = function
  | Send ch | Recv ch -> Some ch
  | Tau -> None

(* ══════════════════════════════════════════════════════════════════════
   Operational Semantics — SOS Rules
   ══════════════════════════════════════════════════════════════════════ *)

(* Compute all possible transitions from a process *)
let rec transitions (env : environment) (p : process) : (action * process) list =
  match p with
  | Nil -> []

  | Prefix (a, p') -> [(a, p')]

  | Choice (p1, p2) ->
    transitions env p1 @ transitions env p2

  | Parallel (p1, p2) ->
    (* Left moves *)
    let left = List.map (fun (a, p1') -> (a, Parallel (p1', p2)))
        (transitions env p1) in
    (* Right moves *)
    let right = List.map (fun (a, p2') -> (a, Parallel (p1, p2')))
        (transitions env p2) in
    (* Synchronization: a.P | a'.Q → τ.(P | Q) *)
    let syncs = List.concat_map (fun (a1, p1') ->
        List.filter_map (fun (a2, p2') ->
            if is_complement a1 a2 then
              Some (Tau, Parallel (p1', p2'))
            else None
          ) (transitions env p2)
      ) (transitions env p1) in
    left @ right @ syncs

  | Restrict (p', chans) ->
    transitions env p'
    |> List.filter (fun (a, _) ->
        match action_channel a with
        | Some ch -> not (List.mem ch chans)
        | None -> true)
    |> List.map (fun (a, q) -> (a, Restrict (q, chans)))

  | Relabel (p', rels) ->
    transitions env p'
    |> List.map (fun (a, q) -> (relabel_action rels a, Relabel (q, rels)))

  | Ident name ->
    (match List.find_opt (fun d -> d.def_name = name) env with
     | Some def -> transitions env def.def_body
     | None -> [])

(* ══════════════════════════════════════════════════════════════════════
   LTS Generation (BFS exploration)
   ══════════════════════════════════════════════════════════════════════ *)

(* Structural equality for processes (simplified) *)
let proc_equal p1 p2 = (process_to_string p1 = process_to_string p2)

let generate_lts ?(max_states=200) (env : environment) (p : process) : lts =
  let states = ref [(0, p)] in
  let trans = ref [] in
  let next_id = ref 1 in
  let queue = Queue.create () in
  Queue.push (0, p) queue;

  let find_or_add proc =
    match List.find_opt (fun (_, q) -> proc_equal proc q) !states with
    | Some (id, _) -> id
    | None ->
      let id = !next_id in
      incr next_id;
      states := (id, proc) :: !states;
      Queue.push (id, proc) queue;
      id
  in

  while not (Queue.is_empty queue) && !next_id <= max_states do
    let (sid, proc) = Queue.pop queue in
    let ts = transitions env proc in
    List.iter (fun (a, proc') ->
        let did = find_or_add proc' in
        trans := { src = sid; act = a; dst = did } :: !trans
      ) ts
  done;

  { states = List.rev !states;
    transitions = List.rev !trans;
    initial = 0 }

(* ══════════════════════════════════════════════════════════════════════
   Analysis: Deadlock Detection
   ══════════════════════════════════════════════════════════════════════ *)

let find_deadlocks (l : lts) : (state_id * process) list =
  List.filter (fun (sid, _) ->
      not (List.exists (fun t -> t.src = sid) l.transitions)
    ) l.states

(* ══════════════════════════════════════════════════════════════════════
   Analysis: Traces
   ══════════════════════════════════════════════════════════════════════ *)

let traces ?(max_depth=10) (l : lts) : action list list =
  let rec explore sid depth =
    if depth <= 0 then [[]]
    else
      let outgoing = List.filter (fun t -> t.src = sid) l.transitions in
      if outgoing = [] then [[]]
      else
        List.concat_map (fun t ->
            List.map (fun tr -> t.act :: tr) (explore t.dst (depth - 1))
          ) outgoing
  in
  explore l.initial max_depth

let visible_traces ?(max_depth=10) (l : lts) : action list list =
  traces ~max_depth l
  |> List.map (List.filter (fun a -> a <> Tau))
  |> List.sort_uniq compare

(* ══════════════════════════════════════════════════════════════════════
   Strong Bisimulation (Partition Refinement)
   ══════════════════════════════════════════════════════════════════════ *)

(* Check if two states in an LTS are strongly bisimilar *)
let strong_bisimilar (l : lts) (s1 : state_id) (s2 : state_id) : bool =
  let all_ids = List.map fst l.states in
  let n = List.length all_ids in
  (* Start: all states in one partition *)
  let partition = Array.make n 0 in
  let id_to_idx = Hashtbl.create n in
  List.iteri (fun i sid -> Hashtbl.replace id_to_idx sid i) all_ids;
  let idx_of sid = Hashtbl.find id_to_idx sid in

  let outgoing sid =
    List.filter_map (fun t ->
        if t.src = sid then Some (t.act, t.dst) else None
      ) l.transitions
  in

  let changed = ref true in
  let num_classes = ref 1 in

  while !changed do
    changed := false;
    let new_partition = Array.copy partition in
    let next_class = ref !num_classes in

    (* For each current class, try to split *)
    for cls = 0 to !num_classes - 1 do
      let members = List.filter (fun sid -> partition.(idx_of sid) = cls) all_ids in
      match members with
      | [] | [_] -> ()
      | representative :: rest ->
        let rep_sig =
          outgoing representative
          |> List.map (fun (a, d) -> (a, partition.(idx_of d)))
          |> List.sort compare
        in
        List.iter (fun sid ->
            let sig_ =
              outgoing sid
              |> List.map (fun (a, d) -> (a, partition.(idx_of d)))
              |> List.sort compare
            in
            if sig_ <> rep_sig then begin
              new_partition.(idx_of sid) <- !next_class;
              changed := true
            end
          ) rest;
        if !changed then incr next_class
    done;

    Array.blit new_partition 0 partition 0 n;
    num_classes := !next_class
  done;

  partition.(idx_of s1) = partition.(idx_of s2)

(* ══════════════════════════════════════════════════════════════════════
   Weak Bisimulation
   ══════════════════════════════════════════════════════════════════════ *)

(* Weak transitions: =a=> means ==tau==> -a-> ==tau==> *)
let tau_closure (l : lts) (sid : state_id) : state_id list =
  let visited = Hashtbl.create 16 in
  let rec explore s =
    if Hashtbl.mem visited s then ()
    else begin
      Hashtbl.replace visited s ();
      List.iter (fun t ->
          if t.src = s && t.act = Tau then explore t.dst
        ) l.transitions
    end
  in
  explore sid;
  Hashtbl.fold (fun s () acc -> s :: acc) visited []

let weak_transitions (l : lts) (sid : state_id) : (action * state_id) list =
  let tau_reach = tau_closure l sid in
  (* Tau transitions: can reach any state in tau_closure *)
  let tau_dests = List.map (fun s -> (Tau, s)) tau_reach in
  (* Visible transitions: tau* . a . tau* *)
  let visible = List.concat_map (fun s ->
      List.filter_map (fun t ->
          if t.src = s && t.act <> Tau then
            let after_tau = tau_closure l t.dst in
            Some (List.map (fun d -> (t.act, d)) after_tau)
          else None
        ) l.transitions
      |> List.concat
    ) tau_reach in
  tau_dests @ visible

let weak_bisimilar (l : lts) (s1 : state_id) (s2 : state_id) : bool =
  (* Naive fixpoint: maintain a relation R, check conditions *)
  let all_ids = List.map fst l.states in

  (* Start with all pairs related *)
  let relation = Hashtbl.create 64 in
  List.iter (fun a ->
      List.iter (fun b ->
          Hashtbl.replace relation (a, b) true
        ) all_ids
    ) all_ids;

  let changed = ref true in
  while !changed do
    changed := false;
    List.iter (fun a ->
        List.iter (fun b ->
            if Hashtbl.find_opt relation (a, b) = Some true then begin
              let a_trans = List.filter (fun t -> t.src = a) l.transitions in
              let ok = List.for_all (fun t ->
                  let wt = weak_transitions l b in
                  let matching_action = if t.act = Tau then Tau else t.act in
                  List.exists (fun (wa, wd) ->
                      wa = matching_action &&
                      Hashtbl.find_opt relation (t.dst, wd) = Some true
                    ) wt
                ) a_trans
              in
              let b_trans = List.filter (fun t -> t.src = b) l.transitions in
              let ok2 = List.for_all (fun t ->
                  let wt = weak_transitions l a in
                  let matching_action = if t.act = Tau then Tau else t.act in
                  List.exists (fun (wa, wd) ->
                      wa = matching_action &&
                      Hashtbl.find_opt relation (wd, t.dst) = Some true
                    ) wt
                ) b_trans
              in
              if not (ok && ok2) then begin
                Hashtbl.replace relation (a, b) false;
                changed := true
              end
            end
          ) all_ids
      ) all_ids
  done;

  Hashtbl.find_opt relation (s1, s2) = Some true

(* ══════════════════════════════════════════════════════════════════════
   Trace Equivalence
   ══════════════════════════════════════════════════════════════════════ *)

let trace_equivalent (env : environment) (p1 : process) (p2 : process) : bool =
  let l1 = generate_lts env p1 in
  let l2 = generate_lts env p2 in
  let t1 = visible_traces ~max_depth:8 l1 in
  let t2 = visible_traces ~max_depth:8 l2 in
  t1 = t2

(* ══════════════════════════════════════════════════════════════════════
   ASCII Visualization
   ══════════════════════════════════════════════════════════════════════ *)

let print_lts (l : lts) =
  Printf.printf "\n╔══════════════════════════════════════════╗\n";
  Printf.printf "║      Labeled Transition System           ║\n";
  Printf.printf "╠══════════════════════════════════════════╣\n";
  Printf.printf "║ States: %-32d ║\n" (List.length l.states);
  Printf.printf "║ Transitions: %-27d ║\n" (List.length l.transitions);
  Printf.printf "║ Initial: S%-30d ║\n" l.initial;
  Printf.printf "╚══════════════════════════════════════════╝\n\n";

  Printf.printf "States:\n";
  List.iter (fun (sid, proc) ->
      let mark = if sid = l.initial then "→ " else "  " in
      Printf.printf "  %sS%d = %s\n" mark sid (process_to_string proc)
    ) l.states;

  Printf.printf "\nTransitions:\n";
  List.iter (fun t ->
      Printf.printf "  S%d --[%s]--> S%d\n" t.src (action_to_string t.act) t.dst
    ) l.transitions;

  let deadlocks = find_deadlocks l in
  if deadlocks <> [] then begin
    Printf.printf "\n⚠ Deadlock states:\n";
    List.iter (fun (sid, proc) ->
        Printf.printf "  S%d = %s\n" sid (process_to_string proc)
      ) deadlocks
  end else
    Printf.printf "\n✓ No deadlocks found.\n"

(* ══════════════════════════════════════════════════════════════════════
   DOT Export
   ══════════════════════════════════════════════════════════════════════ *)

let lts_to_dot (l : lts) : string =
  let buf = Buffer.create 256 in
  Buffer.add_string buf "digraph LTS {\n";
  Buffer.add_string buf "  rankdir=LR;\n";
  Buffer.add_string buf "  node [shape=circle fontname=\"monospace\"];\n";
  Buffer.add_string buf "  __start [shape=point];\n";
  Buffer.add_string buf (Printf.sprintf "  __start -> S%d;\n" l.initial);

  let deadlocks = find_deadlocks l in
  List.iter (fun (sid, _) ->
      if List.exists (fun (d, _) -> d = sid) deadlocks then
        Buffer.add_string buf (Printf.sprintf "  S%d [shape=doublecircle color=red];\n" sid)
    ) l.states;

  List.iter (fun t ->
      Buffer.add_string buf (Printf.sprintf "  S%d -> S%d [label=\"%s\"];\n"
                               t.src t.dst (action_to_string t.act))
    ) l.transitions;

  Buffer.add_string buf "}\n";
  Buffer.contents buf

(* ══════════════════════════════════════════════════════════════════════
   Built-in Examples
   ══════════════════════════════════════════════════════════════════════ *)

(* Simple handshake: Client sends request, Server receives and responds *)
let handshake_env : environment = [
  { def_name = "Client";
    def_body = Prefix (Send "req", Prefix (Recv "resp", Ident "Client")) };
  { def_name = "Server";
    def_body = Prefix (Recv "req", Prefix (Send "resp", Ident "Server")) };
]

let handshake_system =
  Restrict (
    Parallel (Ident "Client", Ident "Server"),
    ["req"; "resp"]
  )

(* Mutual exclusion with a lock *)
let mutex_env : environment = [
  { def_name = "Lock";
    def_body = Prefix (Send "acquire", Prefix (Recv "release", Ident "Lock")) };
  { def_name = "Proc1";
    def_body = Prefix (Recv "acquire",
                        Prefix (Tau, (* critical section *)
                                Prefix (Send "release", Ident "Proc1"))) };
  { def_name = "Proc2";
    def_body = Prefix (Recv "acquire",
                        Prefix (Tau, (* critical section *)
                                Prefix (Send "release", Ident "Proc2"))) };
]

let mutex_system =
  Restrict (
    Parallel (Ident "Lock", Parallel (Ident "Proc1", Ident "Proc2")),
    ["acquire"; "release"]
  )

(* One-place buffer *)
let buffer_env : environment = [
  { def_name = "Buffer";
    def_body = Prefix (Recv "put", Prefix (Send "get", Ident "Buffer")) };
  { def_name = "Producer";
    def_body = Prefix (Send "put", Ident "Producer") };
  { def_name = "Consumer";
    def_body = Prefix (Recv "get", Ident "Consumer") };
]

let buffer_system =
  Restrict (
    Parallel (Ident "Buffer", Parallel (Ident "Producer", Ident "Consumer")),
    ["put"; "get"]
  )

(* Simple scheduler: alternates between two processes *)
let scheduler_env : environment = [
  { def_name = "Sched";
    def_body = Prefix (Send "go1",
                        Prefix (Recv "done1",
                                Prefix (Send "go2",
                                        Prefix (Recv "done2", Ident "Sched")))) };
  { def_name = "Worker1";
    def_body = Prefix (Recv "go1",
                        Prefix (Tau, Prefix (Send "done1", Ident "Worker1"))) };
  { def_name = "Worker2";
    def_body = Prefix (Recv "go2",
                        Prefix (Tau, Prefix (Send "done2", Ident "Worker2"))) };
]

let scheduler_system =
  Restrict (
    Parallel (Ident "Sched", Parallel (Ident "Worker1", Ident "Worker2")),
    ["go1"; "done1"; "go2"; "done2"]
  )

(* Bisimulation test: these two processes are strongly bisimilar *)
let bisim_p1 = Prefix (Send "a", Prefix (Send "b", Nil))
let bisim_p2 = Prefix (Send "a", Prefix (Send "b", Nil))

(* These are NOT strongly bisimilar but are trace equivalent *)
let bisim_p3 =
  Choice (
    Prefix (Send "a", Prefix (Send "b", Nil)),
    Prefix (Send "a", Prefix (Send "c", Nil))
  )
let bisim_p4 =
  Prefix (Send "a", Choice (Prefix (Send "b", Nil), Prefix (Send "c", Nil)))

(* ══════════════════════════════════════════════════════════════════════
   Parser (Minimal CCS Parser for REPL)
   ══════════════════════════════════════════════════════════════════════ *)

exception Parse_error of string

type token =
  | TOK_IDENT of string
  | TOK_DOT
  | TOK_PLUS
  | TOK_BAR
  | TOK_LPAREN
  | TOK_RPAREN
  | TOK_ZERO
  | TOK_TICK        (* ' for complement *)
  | TOK_TAU
  | TOK_BACKSLASH
  | TOK_LBRACE
  | TOK_RBRACE
  | TOK_COMMA
  | TOK_EOF

let tokenize (s : string) : token list =
  let len = String.length s in
  let i = ref 0 in
  let tokens = ref [] in
  while !i < len do
    match s.[!i] with
    | ' ' | '\t' | '\r' | '\n' -> incr i
    | '.' -> tokens := TOK_DOT :: !tokens; incr i
    | '+' -> tokens := TOK_PLUS :: !tokens; incr i
    | '|' -> tokens := TOK_BAR :: !tokens; incr i
    | '(' -> tokens := TOK_LPAREN :: !tokens; incr i
    | ')' -> tokens := TOK_RPAREN :: !tokens; incr i
    | '0' -> tokens := TOK_ZERO :: !tokens; incr i
    | '\'' -> tokens := TOK_TICK :: !tokens; incr i
    | '\\' -> tokens := TOK_BACKSLASH :: !tokens; incr i
    | '{' -> tokens := TOK_LBRACE :: !tokens; incr i
    | '}' -> tokens := TOK_RBRACE :: !tokens; incr i
    | ',' -> tokens := TOK_COMMA :: !tokens; incr i
    | c when (c >= 'a' && c <= 'z') || (c >= 'A' && c <= 'Z') || c = '_' ->
      let start = !i in
      while !i < len &&
            let c = s.[!i] in
            (c >= 'a' && c <= 'z') || (c >= 'A' && c <= 'Z') ||
            (c >= '0' && c <= '9') || c = '_'
      do incr i done;
      let word = String.sub s start (!i - start) in
      if word = "tau" then tokens := TOK_TAU :: !tokens
      else tokens := TOK_IDENT word :: !tokens
    | c -> raise (Parse_error (Printf.sprintf "Unexpected character: %c" c))
  done;
  List.rev (TOK_EOF :: !tokens)

(* Recursive descent parser *)
(* Grammar:
   proc     := par (('+') par)*
   par      := prefix (('|') prefix)*
   prefix   := action '.' prefix | atom
   action   := IDENT | IDENT' | tau
   atom     := '0' | IDENT | '(' proc ')' | atom '\' '{' names '}'
*)

let parse (tokens : token list) : process =
  let toks = ref tokens in
  let peek () = List.hd !toks in
  let advance () = toks := List.tl !toks in
  let expect t =
    if peek () = t then advance ()
    else raise (Parse_error (Printf.sprintf "Unexpected token"))
  in

  let rec parse_proc () =
    let p = parse_par () in
    parse_choice p

  and parse_choice p =
    if peek () = TOK_PLUS then begin
      advance ();
      let q = parse_par () in
      parse_choice (Choice (p, q))
    end else p

  and parse_par () =
    let p = parse_prefix () in
    parse_parallel p

  and parse_parallel p =
    if peek () = TOK_BAR then begin
      advance ();
      let q = parse_prefix () in
      parse_parallel (Parallel (p, q))
    end else p

  and parse_prefix () =
    match peek () with
    | TOK_TAU ->
      advance ();
      if peek () = TOK_DOT then begin
        advance ();
        let p = parse_prefix () in
        Prefix (Tau, p)
      end else
        (* Just tau alone — treat as tau.0 *)
        Prefix (Tau, Nil)
    | TOK_IDENT name ->
      (* Could be action prefix or process identifier *)
      advance ();
      if peek () = TOK_TICK then begin
        advance ();
        if peek () = TOK_DOT then begin
          advance ();
          let p = parse_prefix () in
          Prefix (Recv name, p)
        end else
          Prefix (Recv name, Nil)
      end else if peek () = TOK_DOT then begin
        advance ();
        let p = parse_prefix () in
        Prefix (Send name, p)
      end else
        (* It's a process identifier *)
        let p = Ident name in
        parse_restrict p
    | _ -> parse_atom ()

  and parse_atom () =
    match peek () with
    | TOK_ZERO ->
      advance ();
      let p = Nil in
      parse_restrict p
    | TOK_LPAREN ->
      advance ();
      let p = parse_proc () in
      expect TOK_RPAREN;
      parse_restrict p
    | _ -> raise (Parse_error "Expected process expression")

  and parse_restrict p =
    if peek () = TOK_BACKSLASH then begin
      advance ();
      expect TOK_LBRACE;
      let names = parse_names () in
      expect TOK_RBRACE;
      let p' = Restrict (p, names) in
      parse_restrict p'
    end else p

  and parse_names () =
    match peek () with
    | TOK_IDENT name ->
      advance ();
      if peek () = TOK_COMMA then begin
        advance ();
        name :: parse_names ()
      end else [name]
    | _ -> []
  in

  let result = parse_proc () in
  (match peek () with
   | TOK_EOF -> ()
   | _ -> raise (Parse_error "Unexpected tokens after expression"));
  result

let parse_process (s : string) : process =
  parse (tokenize s)

(* ══════════════════════════════════════════════════════════════════════
   Interactive REPL
   ══════════════════════════════════════════════════════════════════════ *)

let print_help () =
  Printf.printf "\n";
  Printf.printf "╔══════════════════════════════════════════════════════════════╗\n";
  Printf.printf "║            CCS Process Calculus — Commands                  ║\n";
  Printf.printf "╠══════════════════════════════════════════════════════════════╣\n";
  Printf.printf "║  def Name = <process>   Define a named process             ║\n";
  Printf.printf "║  lts <process>          Generate & show LTS                ║\n";
  Printf.printf "║  traces <process>       Show visible traces                ║\n";
  Printf.printf "║  bisim <p> ~ <q>        Check strong bisimulation          ║\n";
  Printf.printf "║  wbisim <p> ~ <q>       Check weak bisimulation            ║\n";
  Printf.printf "║  traceq <p> ~ <q>       Check trace equivalence            ║\n";
  Printf.printf "║  dot <process>          Export LTS as DOT                  ║\n";
  Printf.printf "║  step <process>         Show one-step transitions          ║\n";
  Printf.printf "║  env                    Show defined processes             ║\n";
  Printf.printf "║  examples               Load built-in examples             ║\n";
  Printf.printf "║  help                   Show this help                     ║\n";
  Printf.printf "║  quit                   Exit                               ║\n";
  Printf.printf "╠══════════════════════════════════════════════════════════════╣\n";
  Printf.printf "║  CCS Syntax:                                               ║\n";
  Printf.printf "║    0          Nil (stopped process)                        ║\n";
  Printf.printf "║    a.P        Send on channel a, then P                    ║\n";
  Printf.printf "║    a'.P       Receive on channel a, then P                 ║\n";
  Printf.printf "║    tau.P      Silent/internal action                       ║\n";
  Printf.printf "║    P + Q      Nondeterministic choice                      ║\n";
  Printf.printf "║    P | Q      Parallel composition                         ║\n";
  Printf.printf "║    P\\{a,b}    Restriction (hide channels)                  ║\n";
  Printf.printf "║    (P)        Grouping                                     ║\n";
  Printf.printf "╚══════════════════════════════════════════════════════════════╝\n\n"

let run_repl () =
  Printf.printf "\n";
  Printf.printf "╔══════════════════════════════════════════════════════════════╗\n";
  Printf.printf "║         CCS Process Calculus Simulator v1.0                 ║\n";
  Printf.printf "║   Milner's Calculus of Communicating Systems                ║\n";
  Printf.printf "║   Type 'help' for commands, 'examples' to load demos       ║\n";
  Printf.printf "╚══════════════════════════════════════════════════════════════╝\n\n";

  let env = ref [] in
  let running = ref true in

  while !running do
    Printf.printf "ccs> ";
    flush stdout;
    match input_line stdin with
    | exception End_of_file -> running := false
    | line ->
      let line = String.trim line in
      if line = "" then ()
      else if line = "quit" || line = "exit" then running := false
      else if line = "help" then print_help ()
      else if line = "env" then begin
        if !env = [] then Printf.printf "  (no definitions)\n"
        else List.iter (fun d ->
            Printf.printf "  %s = %s\n" d.def_name (process_to_string d.def_body)
          ) !env
      end
      else if line = "examples" then begin
        env := handshake_env @ mutex_env @ buffer_env @ scheduler_env;
        Printf.printf "  Loaded: Client, Server, Lock, Proc1, Proc2,\n";
        Printf.printf "          Buffer, Producer, Consumer,\n";
        Printf.printf "          Sched, Worker1, Worker2\n";
        Printf.printf "  Try: lts (Client | Server)\\{req,resp}\n"
      end
      else begin
        try
          if String.length line > 4 && String.sub line 0 4 = "def " then begin
            let rest = String.sub line 4 (String.length line - 4) in
            match String.split_on_char '=' rest with
            | [name_part; body_part] ->
              let name = String.trim name_part in
              let body = parse_process (String.trim body_part) in
              env := { def_name = name; def_body = body } ::
                     List.filter (fun d -> d.def_name <> name) !env;
              Printf.printf "  %s = %s\n" name (process_to_string body)
            | _ -> Printf.printf "  Error: use 'def Name = <process>'\n"
          end
          else if String.length line > 4 && String.sub line 0 4 = "lts " then begin
            let expr = String.sub line 4 (String.length line - 4) in
            let p = parse_process (String.trim expr) in
            let l = generate_lts !env p in
            print_lts l
          end
          else if String.length line > 5 && String.sub line 0 5 = "step " then begin
            let expr = String.sub line 5 (String.length line - 5) in
            let p = parse_process (String.trim expr) in
            let ts = transitions !env p in
            if ts = [] then Printf.printf "  (no transitions — deadlocked)\n"
            else begin
              Printf.printf "  Possible transitions:\n";
              List.iter (fun (a, p') ->
                  Printf.printf "    --[%s]--> %s\n"
                    (action_to_string a) (process_to_string p')
                ) ts
            end
          end
          else if String.length line > 7 && String.sub line 0 7 = "traces " then begin
            let expr = String.sub line 7 (String.length line - 7) in
            let p = parse_process (String.trim expr) in
            let l = generate_lts !env p in
            let vt = visible_traces ~max_depth:6 l in
            Printf.printf "  Visible traces (%d):\n" (List.length vt);
            List.iter (fun tr ->
                let s = List.map action_to_string tr |> String.concat " → " in
                Printf.printf "    ⟨%s⟩\n" (if s = "" then "ε" else s)
              ) (List.filteri (fun i _ -> i < 20) vt);
            if List.length vt > 20 then
              Printf.printf "    ... (%d more)\n" (List.length vt - 20)
          end
          else if String.length line > 4 && String.sub line 0 4 = "dot " then begin
            let expr = String.sub line 4 (String.length line - 4) in
            let p = parse_process (String.trim expr) in
            let l = generate_lts !env p in
            Printf.printf "%s" (lts_to_dot l)
          end
          else if String.length line > 6 && String.sub line 0 6 = "bisim " then begin
            let rest = String.sub line 6 (String.length line - 6) in
            match String.split_on_char '~' rest with
            | [lhs; rhs] ->
              let p1 = parse_process (String.trim lhs) in
              let p2 = parse_process (String.trim rhs) in
              let combined = Parallel (p1, p2) in
              let l = generate_lts !env combined in
              (* Find states corresponding to p1 and p2 components *)
              (* For bisim we generate separate LTS and check *)
              let l1 = generate_lts !env p1 in
              let l2 = generate_lts !env p2 in
              (* Merge into one LTS with offset *)
              let offset = List.length l1.states in
              let merged_states = l1.states @
                                  List.map (fun (i, p) -> (i + offset, p)) l2.states in
              let merged_trans = l1.transitions @
                                 List.map (fun t ->
                                     { src = t.src + offset;
                                       act = t.act;
                                       dst = t.dst + offset }
                                   ) l2.transitions in
              let merged = { states = merged_states;
                             transitions = merged_trans;
                             initial = l1.initial } in
              let result = strong_bisimilar merged l1.initial (l2.initial + offset) in
              Printf.printf "  %s %s %s  (strong bisimulation)\n"
                (process_to_string p1)
                (if result then "≈" else "≉")
                (process_to_string p2);
              ignore (l; combined)
            | _ -> Printf.printf "  Error: use 'bisim P ~ Q'\n"
          end
          else if String.length line > 7 && String.sub line 0 7 = "wbisim " then begin
            let rest = String.sub line 7 (String.length line - 7) in
            match String.split_on_char '~' rest with
            | [lhs; rhs] ->
              let p1 = parse_process (String.trim lhs) in
              let p2 = parse_process (String.trim rhs) in
              let l1 = generate_lts !env p1 in
              let l2 = generate_lts !env p2 in
              let offset = List.length l1.states in
              let merged_states = l1.states @
                                  List.map (fun (i, p) -> (i + offset, p)) l2.states in
              let merged_trans = l1.transitions @
                                 List.map (fun t ->
                                     { src = t.src + offset;
                                       act = t.act;
                                       dst = t.dst + offset }
                                   ) l2.transitions in
              let merged = { states = merged_states;
                             transitions = merged_trans;
                             initial = l1.initial } in
              let result = weak_bisimilar merged l1.initial (l2.initial + offset) in
              Printf.printf "  %s %s %s  (weak bisimulation)\n"
                (process_to_string p1)
                (if result then "≈w" else "≉w")
                (process_to_string p2)
            | _ -> Printf.printf "  Error: use 'wbisim P ~ Q'\n"
          end
          else if String.length line > 7 && String.sub line 0 7 = "traceq " then begin
            let rest = String.sub line 7 (String.length line - 7) in
            match String.split_on_char '~' rest with
            | [lhs; rhs] ->
              let p1 = parse_process (String.trim lhs) in
              let p2 = parse_process (String.trim rhs) in
              let result = trace_equivalent !env p1 p2 in
              Printf.printf "  %s %s %s  (trace equivalence)\n"
                (process_to_string p1)
                (if result then "=t" else "≠t")
                (process_to_string p2)
            | _ -> Printf.printf "  Error: use 'traceq P ~ Q'\n"
          end
          else begin
            (* Try to parse as a process and show it *)
            let p = parse_process line in
            Printf.printf "  Parsed: %s\n" (process_to_string p);
            let ts = transitions !env p in
            Printf.printf "  Transitions: %d\n" (List.length ts)
          end
        with
        | Parse_error msg -> Printf.printf "  Parse error: %s\n" msg
        | e -> Printf.printf "  Error: %s\n" (Printexc.to_string e)
      end
  done;
  Printf.printf "\nGoodbye!\n"

(* ══════════════════════════════════════════════════════════════════════
   Demo Mode
   ══════════════════════════════════════════════════════════════════════ *)

let run_demo () =
  Printf.printf "╔══════════════════════════════════════════════════════════════╗\n";
  Printf.printf "║         CCS Process Calculus Simulator v1.0                 ║\n";
  Printf.printf "║   Milner's Calculus of Communicating Systems                ║\n";
  Printf.printf "╚══════════════════════════════════════════════════════════════╝\n\n";

  (* Demo 1: Handshake protocol *)
  Printf.printf "━━━ Demo 1: Client-Server Handshake ━━━\n";
  Printf.printf "  Client = req.resp'.Client\n";
  Printf.printf "  Server = req'.resp.Server\n";
  Printf.printf "  System = (Client | Server) \\ {req, resp}\n\n";
  let l1 = generate_lts handshake_env handshake_system in
  print_lts l1;
  Printf.printf "\n";

  (* Demo 2: Mutex *)
  Printf.printf "━━━ Demo 2: Mutual Exclusion ━━━\n";
  Printf.printf "  Lock  = acquire.release'.Lock\n";
  Printf.printf "  Proc1 = acquire'.τ.release.Proc1\n";
  Printf.printf "  Proc2 = acquire'.τ.release.Proc2\n";
  Printf.printf "  System = (Lock | Proc1 | Proc2) \\ {acquire, release}\n\n";
  let l2 = generate_lts mutex_env mutex_system in
  print_lts l2;
  Printf.printf "\n";

  (* Demo 3: Buffer *)
  Printf.printf "━━━ Demo 3: Producer-Consumer Buffer ━━━\n";
  Printf.printf "  Buffer   = put'.get.Buffer\n";
  Printf.printf "  Producer = put.Producer\n";
  Printf.printf "  Consumer = get'.Consumer\n\n";
  let l3 = generate_lts buffer_env buffer_system in
  print_lts l3;
  Printf.printf "\n";

  (* Demo 4: Bisimulation *)
  Printf.printf "━━━ Demo 4: Bisimulation Checks ━━━\n\n";

  Printf.printf "  P = a.(b.0 + c.0)\n";
  Printf.printf "  Q = a.b.0 + a.c.0\n\n";

  let te = trace_equivalent [] bisim_p3 bisim_p4 in
  Printf.printf "  Trace equivalent?   %s\n" (if te then "Yes ✓" else "No ✗");

  let l_combined =
    let l1 = generate_lts [] bisim_p3 in
    let l2 = generate_lts [] bisim_p4 in
    let offset = List.length l1.states in
    { states = l1.states @ List.map (fun (i, p) -> (i + offset, p)) l2.states;
      transitions = l1.transitions @
                    List.map (fun t -> { src = t.src + offset; act = t.act;
                                         dst = t.dst + offset }) l2.transitions;
      initial = l1.initial }
  in
  let sb = strong_bisimilar l_combined 0
      (List.length (generate_lts [] bisim_p3).states) in
  Printf.printf "  Strongly bisimilar? %s\n" (if sb then "Yes ✓" else "No ✗");
  Printf.printf "  → These are trace equivalent but NOT bisimilar!\n";
  Printf.printf "    (Classic CCS example of the difference)\n\n";

  (* Demo 5: Scheduler *)
  Printf.printf "━━━ Demo 5: Round-Robin Scheduler ━━━\n";
  Printf.printf "  Sched   = go1.done1'.go2.done2'.Sched\n";
  Printf.printf "  Worker1 = go1'.τ.done1.Worker1\n";
  Printf.printf "  Worker2 = go2'.τ.done2.Worker2\n\n";
  let l5 = generate_lts scheduler_env scheduler_system in
  print_lts l5;
  Printf.printf "\n";

  Printf.printf "Run with no arguments for interactive REPL mode.\n"

(* ══════════════════════════════════════════════════════════════════════
   Main
   ══════════════════════════════════════════════════════════════════════ *)

let () =
  let args = Array.to_list Sys.argv in
  if List.mem "--demo" args then
    run_demo ()
  else
    run_repl ()
