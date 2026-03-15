(* graph_db.ml — Property Graph Query Engine
 *
 * An in-memory property graph database with a Cypher-inspired query
 * language.  Nodes and edges carry typed property maps; queries use
 * pattern matching to find subgraphs, filter on properties, and
 * return projections.
 *
 * Concepts demonstrated:
 * - Property graphs (labeled nodes + typed relationships)
 * - Pattern matching via backtracking search
 * - Query planning and execution
 * - Cypher-inspired DSL (MATCH, WHERE, RETURN, CREATE)
 * - Index structures for fast label/property lookups
 * - Aggregation (COUNT, SUM, AVG, MIN, MAX, COLLECT)
 * - Path finding (shortest path, all paths, variable-length)
 * - Graph mutations (CREATE, SET, DELETE)
 * - Pretty-printed table output
 *
 * No external dependencies — pure OCaml, runs with just the stdlib.
 *)

(* ── Property values ────────────────────────────────────────────────── *)

type value =
  | VString of string
  | VInt of int
  | VFloat of float
  | VBool of bool
  | VNull
  | VList of value list

let string_of_value = function
  | VString s -> Printf.sprintf "%S" s
  | VInt n -> string_of_int n
  | VFloat f -> Printf.sprintf "%.4g" f
  | VBool b -> string_of_bool b
  | VNull -> "NULL"
  | VList vs ->
    "[" ^ String.concat ", " (List.map (fun v ->
      match v with
      | VString s -> Printf.sprintf "%S" s
      | VInt n -> string_of_int n
      | VFloat f -> Printf.sprintf "%.4g" f
      | VBool b -> string_of_bool b
      | VNull -> "NULL"
      | VList _ -> "[...]"
    ) vs) ^ "]"

let value_to_float = function
  | VInt n -> Some (float_of_int n)
  | VFloat f -> Some f
  | _ -> None

let rec compare_values a b =
  match a, b with
  | VNull, VNull -> 0
  | VNull, _ -> -1
  | _, VNull -> 1
  | VBool x, VBool y -> compare x y
  | VBool _, _ -> -1
  | _, VBool _ -> 1
  | VInt x, VInt y -> compare x y
  | VInt x, VFloat y -> compare (float_of_int x) y
  | VFloat x, VInt y -> compare x (float_of_int y)
  | VFloat x, VFloat y -> compare x y
  | (VInt _ | VFloat _), _ -> -1
  | _, (VInt _ | VFloat _) -> 1
  | VString x, VString y -> compare x y
  | VString _, VList _ -> -1
  | VList _, VString _ -> 1
  | VList xs, VList ys ->
    let rec cmp xs ys =
      match xs, ys with
      | [], [] -> 0
      | [], _ -> -1
      | _, [] -> 1
      | x :: xs', y :: ys' ->
        let c = compare_values x y in
        if c <> 0 then c else cmp xs' ys'
    in cmp xs ys

(* ── Nodes and edges ────────────────────────────────────────────────── *)

type node = {
  id         : int;
  labels     : string list;
  properties : (string * value) list;
}

type edge = {
  eid        : int;
  src        : int;
  dst        : int;
  rel_type   : string;
  properties : (string * value) list;
}

(* ── Graph database ─────────────────────────────────────────────────── *)

type graph = {
  mutable next_node_id : int;
  mutable next_edge_id : int;
  mutable nodes        : node list;
  mutable edges        : edge list;
  (* Indexes for fast lookup *)
  mutable label_index  : (string, int list) Hashtbl.t;
  mutable rel_index    : (string, int list) Hashtbl.t;
  mutable out_edges    : (int, edge list) Hashtbl.t;
  mutable in_edges     : (int, edge list) Hashtbl.t;
}

let create_graph () = {
  next_node_id = 1;
  next_edge_id = 1;
  nodes = [];
  edges = [];
  label_index = Hashtbl.create 16;
  rel_index = Hashtbl.create 16;
  out_edges = Hashtbl.create 16;
  in_edges = Hashtbl.create 16;
}

(* ── Graph mutations ────────────────────────────────────────────────── *)

let add_node g ?(labels=[]) ?(props=[]) () =
  let nid = g.next_node_id in
  let n = { id = nid; labels; properties = props } in
  g.next_node_id <- nid + 1;
  g.nodes <- n :: g.nodes;
  (* Update label index *)
  List.iter (fun lbl ->
    let existing = try Hashtbl.find g.label_index lbl with Not_found -> [] in
    Hashtbl.replace g.label_index lbl (nid :: existing)
  ) labels;
  Hashtbl.replace g.out_edges nid [];
  Hashtbl.replace g.in_edges nid [];
  n

let add_edge g ~src ~dst ~rel_type ?(props=[]) () =
  let eid = g.next_edge_id in
  let e = { eid; src; dst; rel_type; properties = props } in
  g.next_edge_id <- eid + 1;
  g.edges <- e :: g.edges;
  (* Update indexes *)
  let existing_rel = try Hashtbl.find g.rel_index rel_type with Not_found -> [] in
  Hashtbl.replace g.rel_index rel_type (eid :: existing_rel);
  let out = try Hashtbl.find g.out_edges src with Not_found -> [] in
  Hashtbl.replace g.out_edges src (e :: out);
  let ins = try Hashtbl.find g.in_edges dst with Not_found -> [] in
  Hashtbl.replace g.in_edges dst (e :: ins);
  e

let find_node g nid =
  List.find_opt (fun n -> n.id = nid) g.nodes

let get_property props key =
  match List.assoc_opt key props with
  | Some v -> v
  | None -> VNull

let set_property props key value =
  (key, value) :: List.filter (fun (k, _) -> k <> key) props

let update_node_props g nid new_props =
  g.nodes <- List.map (fun n ->
    if n.id = nid then
      { n with properties =
        List.fold_left (fun ps (k, v) -> set_property ps k v)
          n.properties new_props }
    else n
  ) g.nodes

let delete_node g nid =
  g.nodes <- List.filter (fun n -> n.id <> nid) g.nodes;
  g.edges <- List.filter (fun e -> e.src <> nid && e.dst <> nid) g.edges;
  (* Rebuild edge indexes for simplicity *)
  Hashtbl.remove g.out_edges nid;
  Hashtbl.remove g.in_edges nid;
  Hashtbl.iter (fun k es ->
    Hashtbl.replace g.out_edges k
      (List.filter (fun e -> e.dst <> nid) es)
  ) g.out_edges;
  Hashtbl.iter (fun k es ->
    Hashtbl.replace g.in_edges k
      (List.filter (fun e -> e.src <> nid) es)
  ) g.in_edges

let delete_edge g eid =
  g.edges <- List.filter (fun e -> e.eid <> eid) g.edges;
  Hashtbl.iter (fun k es ->
    Hashtbl.replace g.out_edges k
      (List.filter (fun e -> e.eid <> eid) es)
  ) g.out_edges;
  Hashtbl.iter (fun k es ->
    Hashtbl.replace g.in_edges k
      (List.filter (fun e -> e.eid <> eid) es)
  ) g.in_edges

(* ── Query pattern types ────────────────────────────────────────────── *)

(** A node pattern: optional variable binding, optional label filter *)
type node_pattern = {
  np_var   : string option;
  np_label : string option;
}

(** Direction of a relationship in a pattern *)
type direction = Outgoing | Incoming | Both

(** A relationship pattern *)
type rel_pattern = {
  rp_var      : string option;
  rp_type     : string option;
  rp_dir      : direction;
  rp_min_hops : int;   (** 1 for fixed-length, variable for var-length *)
  rp_max_hops : int;   (** same as min for fixed, or upper bound *)
}

(** A path pattern: alternating node and relationship patterns *)
type path_pattern =
  | PNode of node_pattern
  | PStep of path_pattern * rel_pattern * node_pattern

(** Filter expressions for WHERE clauses *)
type expr =
  | EVar of string * string     (** variable.property *)
  | ELit of value               (** literal value *)
  | EEq of expr * expr          (** = *)
  | ENeq of expr * expr         (** <> *)
  | ELt of expr * expr          (** < *)
  | EGt of expr * expr          (** > *)
  | ELte of expr * expr         (** <= *)
  | EGte of expr * expr         (** >= *)
  | EAnd of expr * expr         (** AND *)
  | EOr of expr * expr          (** OR *)
  | ENot of expr                (** NOT *)
  | EContains of expr * expr    (** CONTAINS *)
  | EStartsWith of expr * expr  (** STARTS WITH *)
  | EHasLabel of string * string(** variable HAS label *)
  | EIsNull of expr             (** IS NULL *)
  | EIsNotNull of expr          (** IS NOT NULL *)

(** What to return from a query *)
type return_item =
  | RVar of string                      (** return whole node/edge *)
  | RProp of string * string            (** variable.property *)
  | RAggCount of string option          (** COUNT(*) or COUNT(var) *)
  | RAggSum of string * string          (** SUM(var.prop) *)
  | RAggAvg of string * string          (** AVG(var.prop) *)
  | RAggMin of string * string          (** MIN(var.prop) *)
  | RAggMax of string * string          (** MAX(var.prop) *)
  | RAggCollect of string * string      (** COLLECT(var.prop) *)

(** Sort direction *)
type sort_dir = Asc | Desc

(** A full query *)
type query = {
  q_match   : path_pattern;
  q_where   : expr option;
  q_return  : return_item list;
  q_order   : (return_item * sort_dir) list;
  q_limit   : int option;
  q_skip    : int;
  q_distinct: bool;
}

(* ── Binding environment ────────────────────────────────────────────── *)

(** A binding maps variable names to graph entities *)
type binding_value =
  | BNode of node
  | BEdge of edge
  | BPath of node list

type bindings = (string * binding_value) list

let bind_get var bindings =
  List.assoc_opt var bindings

let resolve_expr bindings = function
  | EVar (var, prop) ->
    (match bind_get var bindings with
     | Some (BNode n) -> get_property n.properties prop
     | Some (BEdge e) -> get_property e.properties prop
     | _ -> VNull)
  | ELit v -> v
  | _ -> VNull  (* nested exprs handled by eval_expr *)

(* ── Expression evaluation ──────────────────────────────────────────── *)

let rec eval_expr bindings expr =
  match expr with
  | EVar (var, prop) ->
    (match bind_get var bindings with
     | Some (BNode n) -> get_property n.properties prop
     | Some (BEdge e) -> get_property e.properties prop
     | _ -> VNull)
  | ELit v -> v
  | EEq (a, b) ->
    let va = eval_expr bindings a and vb = eval_expr bindings b in
    VBool (compare_values va vb = 0)
  | ENeq (a, b) ->
    let va = eval_expr bindings a and vb = eval_expr bindings b in
    VBool (compare_values va vb <> 0)
  | ELt (a, b) ->
    let va = eval_expr bindings a and vb = eval_expr bindings b in
    VBool (compare_values va vb < 0)
  | EGt (a, b) ->
    let va = eval_expr bindings a and vb = eval_expr bindings b in
    VBool (compare_values va vb > 0)
  | ELte (a, b) ->
    let va = eval_expr bindings a and vb = eval_expr bindings b in
    VBool (compare_values va vb <= 0)
  | EGte (a, b) ->
    let va = eval_expr bindings a and vb = eval_expr bindings b in
    VBool (compare_values va vb >= 0)
  | EAnd (a, b) ->
    (match eval_expr bindings a, eval_expr bindings b with
     | VBool x, VBool y -> VBool (x && y)
     | _ -> VBool false)
  | EOr (a, b) ->
    (match eval_expr bindings a, eval_expr bindings b with
     | VBool x, VBool y -> VBool (x || y)
     | _ -> VBool false)
  | ENot a ->
    (match eval_expr bindings a with
     | VBool x -> VBool (not x)
     | _ -> VBool true)
  | EContains (a, b) ->
    (match eval_expr bindings a, eval_expr bindings b with
     | VString haystack, VString needle ->
       let hl = String.length haystack and nl = String.length needle in
       let rec search i =
         if i + nl > hl then false
         else if String.sub haystack i nl = needle then true
         else search (i + 1)
       in VBool (search 0)
     | _ -> VBool false)
  | EStartsWith (a, b) ->
    (match eval_expr bindings a, eval_expr bindings b with
     | VString s, VString prefix ->
       let pl = String.length prefix in
       VBool (String.length s >= pl && String.sub s 0 pl = prefix)
     | _ -> VBool false)
  | EHasLabel (var, label) ->
    (match bind_get var bindings with
     | Some (BNode n) -> VBool (List.mem label n.labels)
     | _ -> VBool false)
  | EIsNull e ->
    VBool (eval_expr bindings e = VNull)
  | EIsNotNull e ->
    VBool (eval_expr bindings e <> VNull)

let eval_filter bindings expr =
  match eval_expr bindings expr with
  | VBool true -> true
  | _ -> false

(* ── Pattern matching engine ────────────────────────────────────────── *)

(** Check if a node matches a node pattern *)
let node_matches np n =
  match np.np_label with
  | None -> true
  | Some lbl -> List.mem lbl n.labels

(** Get candidate nodes for a pattern, using label index when possible *)
let candidates g np =
  match np.np_label with
  | Some lbl ->
    let ids = try Hashtbl.find g.label_index lbl with Not_found -> [] in
    List.filter_map (fun nid -> find_node g nid) ids
  | None -> g.nodes

(** Get edges between src and dst matching a rel pattern *)
let matching_edges g rp src_id dst_id =
  let check_type e = match rp.rp_type with
    | None -> true
    | Some t -> e.rel_type = t
  in
  match rp.rp_dir with
  | Outgoing ->
    let out = try Hashtbl.find g.out_edges src_id with Not_found -> [] in
    List.filter (fun e -> e.dst = dst_id && check_type e) out
  | Incoming ->
    let ins = try Hashtbl.find g.in_edges src_id with Not_found -> [] in
    List.filter (fun e -> e.src = dst_id && check_type e) ins
  | Both ->
    let out = try Hashtbl.find g.out_edges src_id with Not_found -> [] in
    let ins = try Hashtbl.find g.in_edges src_id with Not_found -> [] in
    List.filter (fun e -> e.dst = dst_id && check_type e) out @
    List.filter (fun e -> e.src = dst_id && check_type e) ins

(** Get all neighbors reachable via one hop matching a rel pattern *)
let neighbors g rp src_id =
  let check_type e = match rp.rp_type with
    | None -> true
    | Some t -> e.rel_type = t
  in
  let from_out =
    if rp.rp_dir = Incoming then []
    else
      let out = try Hashtbl.find g.out_edges src_id with Not_found -> [] in
      List.filter_map (fun e ->
        if check_type e then Some (e.dst, e) else None
      ) out
  in
  let from_in =
    if rp.rp_dir = Outgoing then []
    else
      let ins = try Hashtbl.find g.in_edges src_id with Not_found -> [] in
      List.filter_map (fun e ->
        if check_type e then Some (e.src, e) else None
      ) ins
  in
  from_out @ from_in

(** Variable-length path expansion with cycle detection *)
let var_length_paths g rp src_id dst_np min_hops max_hops =
  let results = ref [] in
  let rec dfs path_nodes current_id depth =
    if depth >= min_hops then begin
      (* Check if current node matches the destination pattern *)
      match find_node g current_id with
      | Some n when node_matches dst_np n ->
        results := (n, List.rev path_nodes) :: !results
      | _ -> ()
    end;
    if depth < max_hops then begin
      let nbrs = neighbors g rp current_id in
      List.iter (fun (nid, _edge) ->
        if not (List.mem nid path_nodes) then  (* cycle detection *)
          dfs (nid :: path_nodes) nid (depth + 1)
      ) nbrs
    end
  in
  dfs [src_id] src_id 0;
  !results

(** Match a full path pattern against the graph *)
let rec match_pattern g pat bindings =
  match pat with
  | PNode np ->
    let cands = candidates g np in
    List.filter_map (fun n ->
      if node_matches np n then
        let b = match np.np_var with
          | Some v -> (v, BNode n) :: bindings
          | None -> bindings
        in
        (* Check variable consistency *)
        match np.np_var with
        | Some v ->
          (match bind_get v bindings with
           | Some (BNode existing) when existing.id <> n.id -> None
           | _ -> Some b)
        | None -> Some b
      else None
    ) cands

  | PStep (left_pat, rp, right_np) ->
    let left_bindings = match_pattern g left_pat bindings in
    List.concat_map (fun lbinds ->
      (* Find the rightmost bound node from the left pattern *)
      let src_id = find_rightmost_node_id left_pat lbinds in
      match src_id with
      | None -> []
      | Some sid ->
        if rp.rp_min_hops = 1 && rp.rp_max_hops = 1 then begin
          (* Fixed-length: one hop *)
          let right_cands = candidates g right_np in
          List.filter_map (fun dst_n ->
            if node_matches right_np dst_n then begin
              let edges = matching_edges g rp sid dst_n.id in
              match edges with
              | [] -> None
              | e :: _ ->
                let b = match right_np.np_var with
                  | Some v -> (v, BNode dst_n) :: lbinds
                  | None -> lbinds
                in
                let b = match rp.rp_var with
                  | Some v -> (v, BEdge e) :: b
                  | None -> b
                in
                Some b
            end else None
          ) right_cands
        end else begin
          (* Variable-length path *)
          let paths = var_length_paths g rp sid right_np
            rp.rp_min_hops rp.rp_max_hops in
          List.filter_map (fun (dst_n, _path_nodes) ->
            let b = match right_np.np_var with
              | Some v -> (v, BNode dst_n) :: lbinds
              | None -> lbinds
            in
            Some b
          ) paths
        end
    ) left_bindings

and find_rightmost_node_id pat bindings =
  match pat with
  | PNode np ->
    (match np.np_var with
     | Some v ->
       (match bind_get v bindings with
        | Some (BNode n) -> Some n.id
        | _ -> None)
     | None -> None)
  | PStep (_, _, np) ->
    (match np.np_var with
     | Some v ->
       (match bind_get v bindings with
        | Some (BNode n) -> Some n.id
        | _ -> None)
     | None -> None)

(* ── Query execution ────────────────────────────────────────────────── *)

(** Extract a return value from bindings *)
let extract_return_item bindings item =
  match item with
  | RVar var ->
    (match bind_get var bindings with
     | Some (BNode n) ->
       let label_str = String.concat ":" n.labels in
       let props = List.map (fun (k, v) ->
         k ^ ": " ^ string_of_value v) n.properties in
       VString (Printf.sprintf "(%s {%s})" label_str
         (String.concat ", " props))
     | Some (BEdge e) ->
       let props = List.map (fun (k, v) ->
         k ^ ": " ^ string_of_value v) e.properties in
       VString (Printf.sprintf "[:%s {%s}]" e.rel_type
         (String.concat ", " props))
     | Some (BPath ns) ->
       VString (Printf.sprintf "Path(%d nodes)" (List.length ns))
     | None -> VNull)
  | RProp (var, prop) ->
    (match bind_get var bindings with
     | Some (BNode n) -> get_property n.properties prop
     | Some (BEdge e) -> get_property e.properties prop
     | _ -> VNull)
  | RAggCount _ | RAggSum _ | RAggAvg _ | RAggMin _ | RAggMax _
  | RAggCollect _ -> VNull  (* handled in aggregation phase *)

(** Check if any return items are aggregations *)
let has_aggregation items =
  List.exists (function
    | RAggCount _ | RAggSum _ | RAggAvg _ | RAggMin _
    | RAggMax _ | RAggCollect _ -> true
    | _ -> false
  ) items

(** Compute aggregations over a set of bindings *)
let compute_aggregation all_bindings items =
  List.map (fun item ->
    match item with
    | RAggCount None ->
      VInt (List.length all_bindings)
    | RAggCount (Some var) ->
      let count = List.length (List.filter (fun b ->
        bind_get var b <> None
      ) all_bindings) in
      VInt count
    | RAggSum (var, prop) ->
      let sum = List.fold_left (fun acc b ->
        match bind_get var b with
        | Some (BNode n) ->
          (match value_to_float (get_property n.properties prop) with
           | Some f -> acc +. f | None -> acc)
        | Some (BEdge e) ->
          (match value_to_float (get_property e.properties prop) with
           | Some f -> acc +. f | None -> acc)
        | _ -> acc
      ) 0.0 all_bindings in
      VFloat sum
    | RAggAvg (var, prop) ->
      let sum = ref 0.0 and cnt = ref 0 in
      List.iter (fun b ->
        match bind_get var b with
        | Some (BNode n) ->
          (match value_to_float (get_property n.properties prop) with
           | Some f -> sum := !sum +. f; incr cnt | None -> ())
        | Some (BEdge e) ->
          (match value_to_float (get_property e.properties prop) with
           | Some f -> sum := !sum +. f; incr cnt | None -> ())
        | _ -> ()
      ) all_bindings;
      if !cnt > 0 then VFloat (!sum /. float_of_int !cnt) else VNull
    | RAggMin (var, prop) ->
      let vals = List.filter_map (fun b ->
        match bind_get var b with
        | Some (BNode n) ->
          let v = get_property n.properties prop in
          if v <> VNull then Some v else None
        | Some (BEdge e) ->
          let v = get_property e.properties prop in
          if v <> VNull then Some v else None
        | _ -> None
      ) all_bindings in
      (match vals with
       | [] -> VNull
       | _ -> List.fold_left (fun acc v ->
           if compare_values v acc < 0 then v else acc) (List.hd vals) vals)
    | RAggMax (var, prop) ->
      let vals = List.filter_map (fun b ->
        match bind_get var b with
        | Some (BNode n) ->
          let v = get_property n.properties prop in
          if v <> VNull then Some v else None
        | Some (BEdge e) ->
          let v = get_property e.properties prop in
          if v <> VNull then Some v else None
        | _ -> None
      ) all_bindings in
      (match vals with
       | [] -> VNull
       | _ -> List.fold_left (fun acc v ->
           if compare_values v acc > 0 then v else acc) (List.hd vals) vals)
    | RAggCollect (var, prop) ->
      let vals = List.filter_map (fun b ->
        match bind_get var b with
        | Some (BNode n) ->
          let v = get_property n.properties prop in
          if v <> VNull then Some v else None
        | Some (BEdge e) ->
          let v = get_property e.properties prop in
          if v <> VNull then Some v else None
        | _ -> None
      ) all_bindings in
      VList vals
    | RVar _ | RProp _ ->
      (* For non-aggregation items in a GROUP BY context, take first *)
      (match all_bindings with
       | b :: _ -> extract_return_item b item
       | [] -> VNull)
  ) items

(** Execute a query against the graph *)
let execute g query =
  (* 1. Pattern match *)
  let all_bindings = match_pattern g query.q_match [] in

  (* 2. Apply WHERE filter *)
  let filtered = match query.q_where with
    | None -> all_bindings
    | Some expr ->
      List.filter (fun b -> eval_filter b expr) all_bindings
  in

  (* 3. Extract results *)
  if has_aggregation query.q_return then begin
    (* Aggregation query — compute over all filtered bindings *)
    [compute_aggregation filtered query.q_return]
  end else begin
    (* Regular query — extract per-binding *)
    let rows = List.map (fun b ->
      List.map (extract_return_item b) query.q_return
    ) filtered in

    (* 4. Distinct *)
    let rows = if query.q_distinct then
      List.sort_uniq (fun a b ->
        compare a b
      ) rows
    else rows in

    (* 5. Order by *)
    let rows = match query.q_order with
      | [] -> rows
      | orders ->
        List.sort (fun row_a row_b ->
          List.fold_left (fun acc (item, dir) ->
            if acc <> 0 then acc
            else
              let idx =
                let rec find_idx i = function
                  | [] -> 0
                  | x :: _ when x = item -> i
                  | _ :: rest -> find_idx (i + 1) rest
                in find_idx 0 query.q_return in
              let va = List.nth row_a idx and vb = List.nth row_b idx in
              let cmp = compare_values va vb in
              if dir = Desc then -cmp else cmp
          ) 0 orders
        ) rows
    in

    (* 6. Skip *)
    let rows = if query.q_skip > 0 then
      let rec drop n = function
        | [] -> []
        | _ :: rest as l -> if n <= 0 then l else drop (n - 1) rest
      in drop query.q_skip rows
    else rows in

    (* 7. Limit *)
    let rows = match query.q_limit with
      | None -> rows
      | Some lim ->
        let rec take n = function
          | [] -> []
          | x :: rest -> if n <= 0 then [] else x :: take (n - 1) rest
        in take lim rows
    in
    rows
  end

(* ── Shortest path ──────────────────────────────────────────────────── *)

(** BFS shortest path between two nodes, optionally filtered by rel type *)
let shortest_path g ?rel_type src_id dst_id =
  if src_id = dst_id then Some [src_id]
  else begin
    let visited = Hashtbl.create 16 in
    let queue = Queue.create () in
    Queue.push (src_id, [src_id]) queue;
    Hashtbl.replace visited src_id true;
    let result = ref None in
    while not (Queue.is_empty queue) && !result = None do
      let (curr, path) = Queue.pop queue in
      let out = try Hashtbl.find g.out_edges curr with Not_found -> [] in
      List.iter (fun e ->
        let type_ok = match rel_type with
          | None -> true | Some t -> e.rel_type = t in
        if type_ok && not (Hashtbl.mem visited e.dst) then begin
          let new_path = path @ [e.dst] in
          if e.dst = dst_id then
            result := Some new_path
          else begin
            Hashtbl.replace visited e.dst true;
            Queue.push (e.dst, new_path) queue
          end
        end
      ) out
    done;
    !result
  end

(** Find all simple paths up to a max length *)
let all_paths g ?rel_type ?(max_length=10) src_id dst_id =
  let results = ref [] in
  let rec dfs visited current path =
    if current = dst_id && List.length path > 1 then
      results := List.rev path :: !results
    else if List.length path <= max_length then begin
      let out = try Hashtbl.find g.out_edges current with Not_found -> [] in
      List.iter (fun e ->
        let type_ok = match rel_type with
          | None -> true | Some t -> e.rel_type = t in
        if type_ok && not (List.mem e.dst visited) then
          dfs (e.dst :: visited) e.dst (e.dst :: path)
      ) out
    end
  in
  dfs [src_id] src_id [src_id];
  !results

(* ── Graph statistics ───────────────────────────────────────────────── *)

type graph_stats = {
  node_count     : int;
  edge_count     : int;
  label_counts   : (string * int) list;
  rel_type_counts: (string * int) list;
  avg_degree     : float;
  max_out_degree : int;
  max_in_degree  : int;
  density        : float;
}

let graph_stats g =
  let nc = List.length g.nodes and ec = List.length g.edges in
  let label_counts = Hashtbl.fold (fun k v acc ->
    (k, List.length v) :: acc
  ) g.label_index [] in
  let rel_counts = Hashtbl.fold (fun k v acc ->
    (k, List.length v) :: acc
  ) g.rel_index [] in
  let max_out = Hashtbl.fold (fun _ es acc ->
    max acc (List.length es)) g.out_edges 0 in
  let max_in = Hashtbl.fold (fun _ es acc ->
    max acc (List.length es)) g.in_edges 0 in
  let avg_deg = if nc > 0 then float_of_int (2 * ec) /. float_of_int nc
    else 0.0 in
  let density = if nc > 1 then
    float_of_int ec /. float_of_int (nc * (nc - 1))
  else 0.0 in
  { node_count = nc; edge_count = ec;
    label_counts; rel_type_counts = rel_counts;
    avg_degree = avg_deg; max_out_degree = max_out;
    max_in_degree = max_in; density }

(* ── Pretty printing ────────────────────────────────────────────────── *)

let render_table headers rows =
  let ncols = List.length headers in
  let all_rows = headers :: List.map (List.map string_of_value) rows in
  let widths = List.init ncols (fun i ->
    List.fold_left (fun acc row ->
      max acc (String.length (List.nth row i))
    ) 0 all_rows
  ) in
  let sep = "+" ^ String.concat "+"
    (List.map (fun w -> String.make (w + 2) '-') widths) ^ "+" in
  let fmt_row row =
    "| " ^ String.concat " | "
      (List.mapi (fun i cell ->
        let w = List.nth widths i in
        let pad = w - String.length cell in
        cell ^ String.make (max 0 pad) ' '
      ) row) ^ " |"
  in
  let buf = Buffer.create 256 in
  Buffer.add_string buf sep;
  Buffer.add_char buf '\n';
  Buffer.add_string buf (fmt_row headers);
  Buffer.add_char buf '\n';
  Buffer.add_string buf sep;
  Buffer.add_char buf '\n';
  List.iter (fun row ->
    Buffer.add_string buf (fmt_row (List.map string_of_value row));
    Buffer.add_char buf '\n'
  ) rows;
  Buffer.add_string buf sep;
  Buffer.contents buf

let render_stats stats =
  let buf = Buffer.create 256 in
  Buffer.add_string buf "=== Graph Statistics ===\n";
  Buffer.add_string buf (Printf.sprintf "  Nodes: %d\n" stats.node_count);
  Buffer.add_string buf (Printf.sprintf "  Edges: %d\n" stats.edge_count);
  Buffer.add_string buf (Printf.sprintf "  Avg degree: %.2f\n" stats.avg_degree);
  Buffer.add_string buf (Printf.sprintf "  Max out-degree: %d\n" stats.max_out_degree);
  Buffer.add_string buf (Printf.sprintf "  Max in-degree: %d\n" stats.max_in_degree);
  Buffer.add_string buf (Printf.sprintf "  Density: %.4f\n" stats.density);
  Buffer.add_string buf "  Labels:\n";
  List.iter (fun (l, c) ->
    Buffer.add_string buf (Printf.sprintf "    :%s (%d)\n" l c)
  ) stats.label_counts;
  Buffer.add_string buf "  Relationship types:\n";
  List.iter (fun (t, c) ->
    Buffer.add_string buf (Printf.sprintf "    :%s (%d)\n" t c)
  ) stats.rel_type_counts;
  Buffer.contents buf

(* ── Query builder DSL ──────────────────────────────────────────────── *)

(** Convenience: create a node pattern *)
let n ?var ?label () =
  { np_var = var; np_label = label }

(** Convenience: create a relationship pattern *)
let r ?(var="") ?(rel_type="") ?(dir=Outgoing)
    ?(min_hops=1) ?(max_hops=1) () =
  { rp_var = (if var = "" then None else Some var);
    rp_type = (if rel_type = "" then None else Some rel_type);
    rp_dir = dir; rp_min_hops = min_hops; rp_max_hops = max_hops }

(** Build a path step: node -[rel]-> node *)
let step left rel right =
  PStep (left, rel, right)

(** Build a query with defaults *)
let query ?(where=None) ?(order=[]) ?(limit=None) ?(skip=0)
    ?(distinct=false) pattern returns =
  { q_match = pattern; q_where = where; q_return = returns;
    q_order = order; q_limit = limit; q_skip = skip;
    q_distinct = distinct }


(* ── Demo: Social network ──────────────────────────────────────────── *)

let demo () =
  let g = create_graph () in

  (* Create people *)
  let alice = add_node g ~labels:["Person"]
    ~props:["name", VString "Alice"; "age", VInt 30;
            "city", VString "Seattle"] () in
  let bob = add_node g ~labels:["Person"]
    ~props:["name", VString "Bob"; "age", VInt 25;
            "city", VString "Portland"] () in
  let charlie = add_node g ~labels:["Person"]
    ~props:["name", VString "Charlie"; "age", VInt 35;
            "city", VString "Seattle"] () in
  let diana = add_node g ~labels:["Person"]
    ~props:["name", VString "Diana"; "age", VInt 28;
            "city", VString "San Francisco"] () in
  let eve = add_node g ~labels:["Person"]
    ~props:["name", VString "Eve"; "age", VInt 32;
            "city", VString "Seattle"] () in

  (* Create companies *)
  let techco = add_node g ~labels:["Company"]
    ~props:["name", VString "TechCo"; "industry", VString "Software"] () in
  let startupx = add_node g ~labels:["Company"]
    ~props:["name", VString "StartupX"; "industry", VString "AI"] () in

  (* Create friendships *)
  let _ = add_edge g ~src:alice.id ~dst:bob.id ~rel_type:"FRIENDS_WITH"
    ~props:["since", VInt 2020] () in
  let _ = add_edge g ~src:alice.id ~dst:charlie.id ~rel_type:"FRIENDS_WITH"
    ~props:["since", VInt 2018] () in
  let _ = add_edge g ~src:bob.id ~dst:diana.id ~rel_type:"FRIENDS_WITH"
    ~props:["since", VInt 2021] () in
  let _ = add_edge g ~src:charlie.id ~dst:eve.id ~rel_type:"FRIENDS_WITH"
    ~props:["since", VInt 2019] () in
  let _ = add_edge g ~src:diana.id ~dst:eve.id ~rel_type:"FRIENDS_WITH"
    ~props:["since", VInt 2022] () in

  (* Employment *)
  let _ = add_edge g ~src:alice.id ~dst:techco.id ~rel_type:"WORKS_AT"
    ~props:["role", VString "Engineer"; "salary", VInt 120000] () in
  let _ = add_edge g ~src:bob.id ~dst:startupx.id ~rel_type:"WORKS_AT"
    ~props:["role", VString "Data Scientist"; "salary", VInt 95000] () in
  let _ = add_edge g ~src:charlie.id ~dst:techco.id ~rel_type:"WORKS_AT"
    ~props:["role", VString "Manager"; "salary", VInt 150000] () in
  let _ = add_edge g ~src:eve.id ~dst:startupx.id ~rel_type:"WORKS_AT"
    ~props:["role", VString "CTO"; "salary", VInt 180000] () in

  Printf.printf "=== Property Graph Query Engine Demo ===\n\n";

  (* Query 1: Find all people in Seattle *)
  Printf.printf "--- Query 1: People in Seattle ---\n";
  let q1 = query
    (PNode (n ~var:"p" ~label:"Person" ()))
    ~where:(Some (EEq (EVar ("p", "city"), ELit (VString "Seattle"))))
    [RProp ("p", "name"); RProp ("p", "age")] in
  let rows = execute g q1 in
  Printf.printf "%s\n\n" (render_table ["name"; "age"] rows);

  (* Query 2: Who is friends with whom? *)
  Printf.printf "--- Query 2: Friendships ---\n";
  let q2 = query
    (PStep (PNode (n ~var:"a" ~label:"Person" ()),
            r ~rel_type:"FRIENDS_WITH" (),
            n ~var:"b" ~label:"Person" ()))
    [RProp ("a", "name"); RProp ("b", "name")] in
  let rows = execute g q2 in
  Printf.printf "%s\n\n" (render_table ["person"; "friend"] rows);

  (* Query 3: Friends of friends (2-hop) *)
  Printf.printf "--- Query 3: Friends of Alice's friends ---\n";
  let step1 = PStep (PNode (n ~var:"a" ~label:"Person" ()),
                      r ~rel_type:"FRIENDS_WITH" (),
                      n ~var:"b" ~label:"Person" ()) in
  let step2 = PStep (step1,
                      r ~rel_type:"FRIENDS_WITH" (),
                      n ~var:"c" ~label:"Person" ()) in
  let q3 = query step2
    ~where:(Some (EAnd (
      EEq (EVar ("a", "name"), ELit (VString "Alice")),
      ENeq (EVar ("a", "name"), EVar ("c", "name"))
    )))
    [RProp ("c", "name"); RProp ("c", "city")] in
  let rows = execute g q3 in
  Printf.printf "%s\n\n" (render_table ["friend_of_friend"; "city"] rows);

  (* Query 4: Count people by city *)
  Printf.printf "--- Query 4: People count (aggregation) ---\n";
  let q4 = query
    (PNode (n ~var:"p" ~label:"Person" ()))
    [RAggCount None] in
  let rows = execute g q4 in
  Printf.printf "%s\n\n" (render_table ["count"] rows);

  (* Query 5: Average salary at each company *)
  Printf.printf "--- Query 5: Average salary ---\n";
  let q5 = query
    (PStep (PNode (n ~var:"p" ~label:"Person" ()),
            r ~var:"w" ~rel_type:"WORKS_AT" (),
            n ~var:"c" ~label:"Company" ()))
    [RAggAvg ("w", "salary")] in
  let rows = execute g q5 in
  Printf.printf "%s\n\n" (render_table ["avg_salary"] rows);

  (* Query 6: Shortest path *)
  Printf.printf "--- Query 6: Shortest path Alice -> Eve ---\n";
  (match shortest_path g alice.id eve.id with
   | None -> Printf.printf "  No path found\n"
   | Some path ->
     let names = List.filter_map (fun nid ->
       match find_node g nid with
       | Some n -> Some (match get_property n.properties "name" with
                         | VString s -> s | _ -> "?")
       | None -> None
     ) path in
     Printf.printf "  Path: %s\n" (String.concat " -> " names));

  Printf.printf "\n--- Query 7: Shortest path Bob -> Charlie ---\n";
  (match shortest_path g ~rel_type:"FRIENDS_WITH" bob.id charlie.id with
   | None -> Printf.printf "  No path found\n"
   | Some path ->
     let names = List.filter_map (fun nid ->
       match find_node g nid with
       | Some n -> Some (match get_property n.properties "name" with
                         | VString s -> s | _ -> "?")
       | None -> None
     ) path in
     Printf.printf "  Path: %s\n" (String.concat " -> " names));

  (* Graph stats *)
  Printf.printf "\n%s" (render_stats (graph_stats g));

  Printf.printf "\nDone.\n"

(* ── Entry point (only when run as main program) ────────────────────── *)

let () =
  (* Only run demo when this is the main program, not when loaded as a module.
     Check if the executable name ends with "graph_db" *)
  let prog = Sys.argv.(0) in
  let base = Filename.basename prog in
  let base = try Filename.chop_extension base with Invalid_argument _ -> base in
  if base = "graph_db" then demo ()
