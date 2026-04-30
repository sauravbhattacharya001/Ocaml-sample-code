(* Bayesian Network Inference Engine
   - Directed acyclic graph of random variables
   - Conditional probability tables (CPTs)
   - Exact inference: enumeration & variable elimination
   - D-separation test
   - 3 classic example networks (alarm, sprinkler, asia)
   - Interactive REPL *)

(* ── Types ─────────────────────────────────────────── *)

type variable = string
type assignment = (variable * bool) list
type cpt_entry = { parents_vals: bool list; prob_true: float }
type node = {
  name: variable;
  parents: variable list;
  cpt: cpt_entry list;
}
type network = {
  nodes: node list;
}

(* ── Index caches ──────────────────────────────────── *)

(* Lazily-built Hashtbl indexes per network.  Keyed by the physical
   identity of the node list so each network gets its own cache entry.
   This turns every find_node from O(N) to O(1) and every children_of
   from O(N*P) to O(1). *)

let _node_idx_cache : (node list, (string, node) Hashtbl.t) Hashtbl.t =
  Hashtbl.create 4

let _children_idx_cache : (node list, (string, string list) Hashtbl.t) Hashtbl.t =
  Hashtbl.create 4

let _build_node_index nodes =
  let tbl = Hashtbl.create (List.length nodes) in
  List.iter (fun n -> Hashtbl.replace tbl n.name n) nodes;
  Hashtbl.replace _node_idx_cache nodes tbl;
  tbl

let _build_children_index nodes =
  let tbl = Hashtbl.create (List.length nodes) in
  (* Initialize every node to empty children list *)
  List.iter (fun n -> Hashtbl.replace tbl n.name []) nodes;
  (* For each node, register it as a child of each parent *)
  List.iter (fun n ->
    List.iter (fun p ->
      let cur = try Hashtbl.find tbl p with Not_found -> [] in
      Hashtbl.replace tbl p (n.name :: cur)
    ) n.parents
  ) nodes;
  Hashtbl.replace _children_idx_cache nodes tbl;
  tbl

let _get_node_index nodes =
  try Hashtbl.find _node_idx_cache nodes
  with Not_found -> _build_node_index nodes

let _get_children_index nodes =
  try Hashtbl.find _children_idx_cache nodes
  with Not_found -> _build_children_index nodes

(* ── Utilities ─────────────────────────────────────── *)

let find_node net v =
  Hashtbl.find (_get_node_index net.nodes) v

let all_vars net = List.map (fun n -> n.name) net.nodes

let children_of net v =
  try Hashtbl.find (_get_children_index net.nodes) v
  with Not_found -> []

let lookup_cpt node parent_vals =
  (* Find matching CPT entry for given parent assignment *)
  try
    let e = List.find (fun e -> e.parents_vals = parent_vals) node.cpt in
    e.prob_true
  with Not_found ->
    (* Default: uniform *)
    0.5

let prob_of_val node parent_vals value =
  let p = lookup_cpt node parent_vals in
  if value then p else 1.0 -. p

let get_parent_vals assignment parents =
  List.map (fun p ->
    try List.assoc p assignment
    with Not_found -> false
  ) parents

(* ── Topological sort ──────────────────────────────── *)

let topo_sort net =
  let visited = Hashtbl.create 16 in
  let order = ref [] in
  let rec visit v =
    if not (Hashtbl.mem visited v) then begin
      Hashtbl.add visited v true;
      let node = find_node net v in
      List.iter visit node.parents;
      order := v :: !order
    end
  in
  List.iter (fun n -> visit n.name) net.nodes;
  List.rev !order

(* ── Enumeration-based exact inference ─────────────── *)

(* P(query=true | evidence) by full enumeration *)
let enumerate_ask net query evidence =
  let vars = topo_sort net in
  let rec enumerate_all vars assignment =
    match vars with
    | [] -> 1.0
    | v :: rest ->
      let node = find_node net v in
      let parent_vals = get_parent_vals assignment node.parents in
      if List.mem_assoc v assignment then
        let value = List.assoc v assignment in
        let p = prob_of_val node parent_vals value in
        p *. enumerate_all rest assignment
      else
        (* Sum over both values *)
        let p_true = prob_of_val node parent_vals true in
        let p_false = prob_of_val node parent_vals false in
        p_true *. enumerate_all rest ((v, true) :: assignment)
        +. p_false *. enumerate_all rest ((v, false) :: assignment)
  in
  (* Compute P(query=true, evidence) and P(query=false, evidence) *)
  let p_true = enumerate_all vars ((query, true) :: evidence) in
  let p_false = enumerate_all vars ((query, false) :: evidence) in
  let total = p_true +. p_false in
  if total = 0.0 then 0.5
  else p_true /. total

(* ── Variable Elimination ──────────────────────────── *)

(* A factor is a table over a set of variables *)
type factor = {
  vars: variable list;
  table: (bool list * float) list;
}

let all_assignments vars =
  let rec go = function
    | [] -> [[]]
    | _ :: rest ->
      let sub = go rest in
      List.map (fun a -> true :: a) sub @ List.map (fun a -> false :: a) sub
  in
  go vars

let make_factor net node evidence =
  let all = node.parents @ [node.name] in
  (* Filter out observed variables, fix their values *)
  let assignments = all_assignments all in
  let table = List.filter_map (fun vals ->
    let assignment = List.combine all vals in
    (* Check consistency with evidence *)
    let consistent = List.for_all (fun (v, ev) ->
      try List.assoc v assignment = ev with Not_found -> true
    ) evidence in
    if not consistent then None
    else begin
      let parent_vals = List.map (fun p -> List.assoc p assignment) node.parents in
      let value = List.assoc node.name assignment in
      let p = prob_of_val node parent_vals value in
      Some (vals, p)
    end
  ) assignments in
  (* Determine which variables are not fixed by evidence *)
  let free_vars = List.filter (fun v -> not (List.mem_assoc v evidence)) all in
  (* Project table to free vars *)
  let free_indices = List.mapi (fun i v ->
    if List.mem v free_vars then Some i else None
  ) all in
  let free_indices = List.filter_map Fun.id free_indices in
  let projected = List.map (fun (vals, p) ->
    let fv = List.map (fun i -> List.nth vals i) free_indices in
    (fv, p)
  ) table in
  (* Merge duplicate rows *)
  let merged = Hashtbl.create 16 in
  List.iter (fun (fv, p) ->
    let key = fv in
    let old = try Hashtbl.find merged key with Not_found -> 0.0 in
    Hashtbl.replace merged key (old +. p)
  ) projected;
  let table = Hashtbl.fold (fun k v acc -> (k, v) :: acc) merged [] in
  { vars = free_vars; table }

let _factor_to_hashtbl (table : (bool list * float) list) =
  let h = Hashtbl.create (List.length table) in
  List.iter (fun (k, v) -> Hashtbl.replace h k v) table;
  h

let multiply_factors f1 f2 =
  let all_vars = f1.vars @ List.filter (fun v -> not (List.mem v f1.vars)) f2.vars in
  let assignments = all_assignments all_vars in
  (* Build variable-index maps for O(1) positional lookup *)
  let var_idx = Hashtbl.create (List.length all_vars) in
  List.iteri (fun i v -> Hashtbl.replace var_idx v i) all_vars;
  let f1_indices = List.map (fun v -> Hashtbl.find var_idx v) f1.vars in
  let f2_indices = List.map (fun v -> Hashtbl.find var_idx v) f2.vars in
  (* O(1) factor table lookups via Hashtbl *)
  let h1 = _factor_to_hashtbl f1.table in
  let h2 = _factor_to_hashtbl f2.table in
  let table = List.filter_map (fun vals ->
    let arr = Array.of_list vals in
    let v1 = List.map (fun i -> arr.(i)) f1_indices in
    let v2 = List.map (fun i -> arr.(i)) f2_indices in
    let p1 = try Hashtbl.find h1 v1 with Not_found -> 0.0 in
    let p2 = try Hashtbl.find h2 v2 with Not_found -> 0.0 in
    Some (vals, p1 *. p2)
  ) assignments in
  { vars = all_vars; table }

let sum_out factor var =
  let idx = let rec find i = function
    | [] -> -1
    | v :: _ when v = var -> i
    | _ :: rest -> find (i + 1) rest
  in find 0 factor.vars in
  if idx < 0 then factor
  else begin
    let new_vars = List.filter (fun v -> v <> var) factor.vars in
    let merged = Hashtbl.create 16 in
    List.iter (fun (vals, p) ->
      let key = List.filteri (fun i _ -> i <> idx) vals in
      let old = try Hashtbl.find merged key with Not_found -> 0.0 in
      Hashtbl.replace merged key (old +. p)
    ) factor.table;
    let table = Hashtbl.fold (fun k v acc -> (k, v) :: acc) merged [] in
    { vars = new_vars; table }
  end

let variable_elimination net query evidence =
  let factors = List.map (fun node -> make_factor net node evidence) net.nodes in
  (* Eliminate all vars except query *)
  let hidden = List.filter (fun v ->
    v <> query && not (List.mem_assoc v evidence)
  ) (all_vars net) in
  let factors = List.fold_left (fun fs h ->
    (* Collect factors mentioning h *)
    let relevant, rest = List.partition (fun f -> List.mem h f.vars) fs in
    let product = match relevant with
      | [] -> { vars = []; table = [([],1.0)] }
      | f :: fs -> List.fold_left multiply_factors f fs
    in
    let new_factor = sum_out product h in
    new_factor :: rest
  ) factors hidden in
  (* Multiply remaining factors *)
  let result = match factors with
    | [] -> { vars = []; table = [([],1.0)] }
    | f :: fs -> List.fold_left multiply_factors f fs
  in
  (* Normalize — use Hashtbl for O(1) lookup on final result *)
  let result_ht = _factor_to_hashtbl result.table in
  let p_true = (try Hashtbl.find result_ht [true] with Not_found -> 0.0) in
  let p_false = (try Hashtbl.find result_ht [false] with Not_found -> 0.0) in
  let total = p_true +. p_false in
  if total = 0.0 then 0.5 else p_true /. total

(* ── D-Separation ──────────────────────────────────── *)

(* Bayes-Ball algorithm for d-separation *)
let d_separated net x y evidence =
  (* BFS/reachability with active trail rules *)
  let evidence_ht = Hashtbl.create (List.length evidence) in
  List.iter (fun (v, _) -> Hashtbl.replace evidence_ht v true) evidence;
  let visited = Hashtbl.create 16 in
  let queue = Queue.create () in
  (* (node, direction: `Up means from child, `Down means from parent) *)
  Queue.push (x, `Up) queue;
  let reachable = ref false in
  while not (Queue.is_empty queue) do
    let (v, dir) = Queue.pop queue in
    if v = y then reachable := true;
    let key = (v, dir) in
    if not (Hashtbl.mem visited key) then begin
      Hashtbl.add visited key true;
      let is_evidence = Hashtbl.mem evidence_ht v in
      match dir with
      | `Up ->
        (* Came from a child *)
        if not is_evidence then begin
          (* Pass through to parents and other children *)
          let node = find_node net v in
          List.iter (fun p -> Queue.push (p, `Up) queue) node.parents;
          List.iter (fun c -> Queue.push (c, `Down) queue) (children_of net v)
        end
      | `Down ->
        (* Came from a parent *)
        if not is_evidence then
          (* Pass to children *)
          List.iter (fun c -> Queue.push (c, `Down) queue) (children_of net v);
        (* Always pass to parents (explaining away) *)
        let node = find_node net v in
        if is_evidence then
          List.iter (fun p -> Queue.push (p, `Up) queue) node.parents
    end
  done;
  not !reachable

(* ── Example Networks ──────────────────────────────── *)

(* Classic sprinkler network *)
let sprinkler_network = {
  nodes = [
    { name = "cloudy";
      parents = [];
      cpt = [{ parents_vals = []; prob_true = 0.5 }] };
    { name = "sprinkler";
      parents = ["cloudy"];
      cpt = [
        { parents_vals = [true]; prob_true = 0.1 };
        { parents_vals = [false]; prob_true = 0.5 };
      ] };
    { name = "rain";
      parents = ["cloudy"];
      cpt = [
        { parents_vals = [true]; prob_true = 0.8 };
        { parents_vals = [false]; prob_true = 0.2 };
      ] };
    { name = "wet_grass";
      parents = ["sprinkler"; "rain"];
      cpt = [
        { parents_vals = [true; true]; prob_true = 0.99 };
        { parents_vals = [true; false]; prob_true = 0.9 };
        { parents_vals = [false; true]; prob_true = 0.9 };
        { parents_vals = [false; false]; prob_true = 0.0 };
      ] };
  ]
}

(* Alarm / burglary network (AIMA classic) *)
let alarm_network = {
  nodes = [
    { name = "burglary"; parents = [];
      cpt = [{ parents_vals = []; prob_true = 0.001 }] };
    { name = "earthquake"; parents = [];
      cpt = [{ parents_vals = []; prob_true = 0.002 }] };
    { name = "alarm"; parents = ["burglary"; "earthquake"];
      cpt = [
        { parents_vals = [true; true]; prob_true = 0.95 };
        { parents_vals = [true; false]; prob_true = 0.94 };
        { parents_vals = [false; true]; prob_true = 0.29 };
        { parents_vals = [false; false]; prob_true = 0.001 };
      ] };
    { name = "john_calls"; parents = ["alarm"];
      cpt = [
        { parents_vals = [true]; prob_true = 0.9 };
        { parents_vals = [false]; prob_true = 0.05 };
      ] };
    { name = "mary_calls"; parents = ["alarm"];
      cpt = [
        { parents_vals = [true]; prob_true = 0.7 };
        { parents_vals = [false]; prob_true = 0.01 };
      ] };
  ]
}

(* Asia / Chest Clinic network *)
let asia_network = {
  nodes = [
    { name = "asia"; parents = [];
      cpt = [{ parents_vals = []; prob_true = 0.01 }] };
    { name = "smoking"; parents = [];
      cpt = [{ parents_vals = []; prob_true = 0.5 }] };
    { name = "tuberculosis"; parents = ["asia"];
      cpt = [
        { parents_vals = [true]; prob_true = 0.05 };
        { parents_vals = [false]; prob_true = 0.01 };
      ] };
    { name = "lung_cancer"; parents = ["smoking"];
      cpt = [
        { parents_vals = [true]; prob_true = 0.1 };
        { parents_vals = [false]; prob_true = 0.01 };
      ] };
    { name = "bronchitis"; parents = ["smoking"];
      cpt = [
        { parents_vals = [true]; prob_true = 0.6 };
        { parents_vals = [false]; prob_true = 0.3 };
      ] };
    { name = "tub_or_cancer"; parents = ["tuberculosis"; "lung_cancer"];
      cpt = [
        { parents_vals = [true; true]; prob_true = 1.0 };
        { parents_vals = [true; false]; prob_true = 1.0 };
        { parents_vals = [false; true]; prob_true = 1.0 };
        { parents_vals = [false; false]; prob_true = 0.0 };
      ] };
    { name = "xray"; parents = ["tub_or_cancer"];
      cpt = [
        { parents_vals = [true]; prob_true = 0.98 };
        { parents_vals = [false]; prob_true = 0.05 };
      ] };
    { name = "dyspnea"; parents = ["tub_or_cancer"; "bronchitis"];
      cpt = [
        { parents_vals = [true; true]; prob_true = 0.9 };
        { parents_vals = [true; false]; prob_true = 0.7 };
        { parents_vals = [false; true]; prob_true = 0.8 };
        { parents_vals = [false; false]; prob_true = 0.1 };
      ] };
  ]
}

(* ── Display ───────────────────────────────────────── *)

let print_network net =
  Printf.printf "Bayesian Network (%d nodes):\n" (List.length net.nodes);
  let sorted = topo_sort net in
  List.iter (fun v ->
    let node = find_node net v in
    if node.parents = [] then
      Printf.printf "  %s (root)\n" v
    else
      Printf.printf "  %s <- [%s]\n" v (String.concat ", " node.parents);
    List.iter (fun e ->
      if node.parents = [] then
        Printf.printf "    P(%s=T) = %.3f\n" v e.prob_true
      else begin
        let pv = List.map2 (fun p b ->
          Printf.sprintf "%s=%s" p (if b then "T" else "F")
        ) node.parents e.parents_vals in
        Printf.printf "    P(%s=T | %s) = %.3f\n" v (String.concat ", " pv) e.prob_true
      end
    ) node.cpt
  ) sorted;
  print_newline ()

let print_marginals net evidence =
  let vars = all_vars net in
  Printf.printf "\nMarginal probabilities";
  if evidence <> [] then begin
    let ev_str = List.map (fun (v, b) ->
      Printf.sprintf "%s=%s" v (if b then "T" else "F")
    ) evidence in
    Printf.printf " given %s" (String.concat ", " ev_str)
  end;
  Printf.printf ":\n";
  List.iter (fun v ->
    if not (List.mem_assoc v evidence) then begin
      let p_enum = enumerate_ask net v evidence in
      let p_ve = variable_elimination net v evidence in
      Printf.printf "  P(%s=T) = %.6f  (VE: %.6f)\n" v p_enum p_ve
    end else
      Printf.printf "  P(%s=T) = [observed %s]\n" v
        (if List.assoc v evidence then "T" else "F")
  ) vars

(* ── REPL ──────────────────────────────────────────── *)

let current_net = ref sprinkler_network
let current_evidence = ref []

let parse_bool s =
  match String.lowercase_ascii (String.trim s) with
  | "t" | "true" | "1" | "yes" -> Some true
  | "f" | "false" | "0" | "no" -> Some false
  | _ -> None

let help () =
  print_string {|
Bayesian Network Inference REPL
═══════════════════════════════
Commands:
  net sprinkler    Load sprinkler network (default)
  net alarm        Load alarm/burglary network
  net asia         Load asia/chest-clinic network
  show             Display current network structure & CPTs
  marginals        Show all marginal probabilities
  query <var>      Query P(var=T | evidence)
  observe <v> <T|F>  Add evidence
  clear            Clear all evidence
  dsep <x> <y>     Test d-separation of x and y given evidence
  compare          Compare enumeration vs variable elimination
  demo             Run classic demo queries
  help             Show this help
  quit             Exit

Examples:
  observe wet_grass true
  query rain
  dsep sprinkler rain
|}

let run_demo () =
  Printf.printf "\n══ Demo: Sprinkler Network ══\n";
  current_net := sprinkler_network;
  current_evidence := [];
  print_network !current_net;

  Printf.printf "── Prior marginals ──\n";
  print_marginals !current_net [];

  Printf.printf "\n── Given wet_grass=T ──\n";
  let ev = [("wet_grass", true)] in
  print_marginals !current_net ev;

  Printf.printf "\n── Given wet_grass=T, rain=T ──\n";
  let ev2 = [("wet_grass", true); ("rain", true)] in
  print_marginals !current_net ev2;

  Printf.printf "\n── D-separation tests ──\n";
  Printf.printf "  sprinkler ⊥ rain | {} ? %b\n"
    (d_separated !current_net "sprinkler" "rain" []);
  Printf.printf "  sprinkler ⊥ rain | {wet_grass=T} ? %b\n"
    (d_separated !current_net "sprinkler" "rain" [("wet_grass", true)]);

  Printf.printf "\n══ Demo: Alarm Network ══\n";
  current_net := alarm_network;
  Printf.printf "── P(burglary=T | john_calls=T, mary_calls=T) ──\n";
  let ev3 = [("john_calls", true); ("mary_calls", true)] in
  let p = enumerate_ask alarm_network "burglary" ev3 in
  Printf.printf "  Enumeration: %.6f\n" p;
  let p2 = variable_elimination alarm_network "burglary" ev3 in
  Printf.printf "  Var Elim:    %.6f\n" p2;

  Printf.printf "\n══ Demo: Asia Network ══\n";
  current_net := asia_network;
  let ev4 = [("dyspnea", true); ("smoking", true)] in
  Printf.printf "── P(lung_cancer=T | dyspnea=T, smoking=T) ──\n";
  let p3 = enumerate_ask asia_network "lung_cancer" ev4 in
  Printf.printf "  = %.6f\n" p3;
  print_newline ()

let rec repl () =
  Printf.printf "bayes> %!";
  match input_line stdin with
  | exception End_of_file -> Printf.printf "\nGoodbye!\n"
  | line ->
    let parts = String.split_on_char ' ' (String.trim line) in
    let parts = List.filter (fun s -> s <> "") parts in
    (match parts with
    | [] -> ()
    | ["help"] | ["h"] | ["?"] -> help ()
    | ["quit"] | ["exit"] | ["q"] -> Printf.printf "Goodbye!\n"; exit 0
    | ["show"] -> print_network !current_net
    | ["marginals"] | ["marg"] ->
      print_marginals !current_net !current_evidence
    | ["net"; name] ->
      (match String.lowercase_ascii name with
      | "sprinkler" ->
        current_net := sprinkler_network;
        current_evidence := [];
        Printf.printf "Loaded sprinkler network.\n"
      | "alarm" ->
        current_net := alarm_network;
        current_evidence := [];
        Printf.printf "Loaded alarm network.\n"
      | "asia" ->
        current_net := asia_network;
        current_evidence := [];
        Printf.printf "Loaded asia network.\n"
      | _ -> Printf.printf "Unknown network: %s (try: sprinkler, alarm, asia)\n" name)
    | ["query"; var] | ["q"; var] ->
      (try
        let _ = find_node !current_net var in
        let p = enumerate_ask !current_net var !current_evidence in
        let p2 = variable_elimination !current_net var !current_evidence in
        Printf.printf "P(%s=T | evidence) = %.6f\n" var p;
        Printf.printf "  (VE check: %.6f)\n" p2
      with Not_found ->
        Printf.printf "Unknown variable: %s\n" var)
    | ["observe"; var; bval] | ["obs"; var; bval] ->
      (match parse_bool bval with
      | None -> Printf.printf "Invalid boolean: %s (use T/F/true/false)\n" bval
      | Some b ->
        (try
          let _ = find_node !current_net var in
          current_evidence := (var, b) :: (List.remove_assoc var !current_evidence);
          Printf.printf "Observed %s = %s\n" var (if b then "T" else "F");
          let ev_str = List.map (fun (v, b) ->
            Printf.sprintf "%s=%s" v (if b then "T" else "F")
          ) !current_evidence in
          Printf.printf "Evidence: {%s}\n" (String.concat ", " ev_str)
        with Not_found ->
          Printf.printf "Unknown variable: %s\n" var))
    | ["clear"] ->
      current_evidence := [];
      Printf.printf "Evidence cleared.\n"
    | ["dsep"; x; y] ->
      let sep = d_separated !current_net x y !current_evidence in
      Printf.printf "%s %s %s given evidence: %s\n" x
        (if sep then "⊥" else "not ⊥") y
        (if sep then "d-separated" else "d-connected")
    | ["compare"] | ["cmp"] ->
      let vars = all_vars !current_net in
      Printf.printf "\nComparison: Enumeration vs Variable Elimination\n";
      Printf.printf "%-20s  %12s  %12s  %s\n" "Variable" "Enum" "VarElim" "Match?";
      Printf.printf "%s\n" (String.make 60 '-');
      List.iter (fun v ->
        if not (List.mem_assoc v !current_evidence) then begin
          let p1 = enumerate_ask !current_net v !current_evidence in
          let p2 = variable_elimination !current_net v !current_evidence in
          let ok = abs_float (p1 -. p2) < 0.001 in
          Printf.printf "%-20s  %12.6f  %12.6f  %s\n" v p1 p2
            (if ok then "✓" else "✗ MISMATCH")
        end
      ) vars
    | ["demo"] -> run_demo ()
    | cmd :: _ -> Printf.printf "Unknown command: %s (type 'help')\n" cmd);
    repl ()

let () =
  Printf.printf "╔══════════════════════════════════════════╗\n";
  Printf.printf "║   Bayesian Network Inference Engine      ║\n";
  Printf.printf "║   Enumeration & Variable Elimination     ║\n";
  Printf.printf "╚══════════════════════════════════════════╝\n";
  Printf.printf "3 networks: sprinkler (default), alarm, asia\n";
  Printf.printf "Type 'help' for commands, 'demo' for examples.\n\n";
  if Array.length Sys.argv > 1 && Sys.argv.(1) = "--demo" then
    (run_demo (); exit 0)
  else
    repl ()
