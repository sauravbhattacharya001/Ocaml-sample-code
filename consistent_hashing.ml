(* consistent_hashing.ml — Consistent Hashing Ring *)
(* A purely functional consistent hashing implementation for distributed     *)
(* systems key distribution. When nodes are added or removed, only K/N keys  *)
(* need to be remapped on average (K = total keys, N = total nodes).         *)
(*                                                                            *)
(* Supports: add_node, remove_node, lookup, virtual nodes (vnodes) for       *)
(* better load balance, node listing, key distribution stats.                *)
(*                                                                            *)
(* The ring is implemented as a sorted association list of (hash, node_id)   *)
(* pairs. Virtual nodes replicate each physical node at multiple positions   *)
(* around the ring for more uniform distribution.                            *)

module ConsistentHash = struct

  (** A point on the ring: hash position + owning node id *)
  type ring_point = {
    position : int;
    node_id  : string;
  }

  (** The hash ring *)
  type t = {
    ring       : ring_point list;   (** sorted by position *)
    vnodes     : int;               (** virtual nodes per physical node *)
    node_set   : string list;       (** physical nodes in insertion order *)
  }

  (** Simple DJB2-style hash, deterministic and portable *)
  let hash_string s =
    let h = ref 5381 in
    String.iter (fun c -> h := !h * 33 + Char.code c) s;
    !h land 0x3FFFFFFF  (* keep positive *)

  (** Create an empty ring with the given number of virtual nodes *)
  let create ?(vnodes = 150) () =
    { ring = []; vnodes; node_set = [] }

  (** Insert a ring_point into a sorted list *)
  let rec insert_sorted pt = function
    | [] -> [pt]
    | hd :: tl when pt.position < hd.position -> pt :: hd :: tl
    | hd :: tl -> hd :: insert_sorted pt tl

  (** Generate virtual-node keys for a physical node *)
  let vnode_keys node_id vnodes =
    List.init vnodes (fun i ->
      let key = Printf.sprintf "%s#vn%d" node_id i in
      { position = hash_string key; node_id })

  (** Add a physical node to the ring *)
  let add_node t node_id =
    if List.mem node_id t.node_set then t
    else
      let points = vnode_keys node_id t.vnodes in
      let ring = List.fold_left (fun r pt -> insert_sorted pt r) t.ring points in
      { t with ring; node_set = t.node_set @ [node_id] }

  (** Remove a physical node from the ring *)
  let remove_node t node_id =
    if not (List.mem node_id t.node_set) then t
    else
      let ring = List.filter (fun pt -> pt.node_id <> node_id) t.ring in
      let node_set = List.filter (fun n -> n <> node_id) t.node_set in
      { t with ring; node_set }

  (** Look up which node owns a given key — walks clockwise from the
      key's hash position to find the first ring point *)
  let lookup t key =
    match t.ring with
    | [] -> None
    | _ ->
      let h = hash_string key in
      (* Find first point with position >= h (clockwise walk) *)
      let rec find = function
        | [] -> None
        | pt :: _ when pt.position >= h -> Some pt.node_id
        | _ :: tl -> find tl
      in
      match find t.ring with
      | Some _ as result -> result
      | None ->
        (* Wrap around to the first point on the ring *)
        Some (List.hd t.ring).node_id

  (** List all physical nodes *)
  let nodes t = t.node_set

  (** Number of physical nodes *)
  let node_count t = List.length t.node_set

  (** Number of points on the ring (physical * vnodes) *)
  let ring_size t = List.length t.ring

  (** Distribution stats: given a list of keys, return a list of
      (node_id, count) pairs showing how many keys map to each node *)
  let distribution t keys =
    let counts = Hashtbl.create 16 in
    List.iter (fun node -> Hashtbl.replace counts node 0) t.node_set;
    List.iter (fun key ->
      match lookup t key with
      | Some node ->
        let c = try Hashtbl.find counts node with Not_found -> 0 in
        Hashtbl.replace counts node (c + 1)
      | None -> ()
    ) keys;
    Hashtbl.fold (fun node count acc -> (node, count) :: acc) counts []

  (** Standard deviation of key distribution — lower means more balanced *)
  let balance_score t keys =
    let dist = distribution t keys in
    let n = float_of_int (List.length dist) in
    if n = 0.0 then 0.0
    else
      let total = List.fold_left (fun acc (_, c) -> acc + c) 0 dist in
      let mean = float_of_int total /. n in
      let variance = List.fold_left (fun acc (_, c) ->
        let diff = float_of_int c -. mean in
        acc +. diff *. diff
      ) 0.0 dist /. n in
      sqrt variance

  (** Pretty-print the ring state *)
  let pp t =
    Printf.printf "Consistent Hash Ring: %d nodes, %d vnodes/node, %d ring points\n"
      (node_count t) t.vnodes (ring_size t);
    Printf.printf "Nodes: %s\n" (String.concat ", " t.node_set)

  (** Simulate adding/removing a node and show key remapping impact *)
  let remapping_impact t keys new_node =
    let before = List.map (fun k -> (k, lookup t k)) keys in
    let t' = add_node t new_node in
    let after = List.map (fun k -> (k, lookup t' k)) keys in
    let remapped = List.fold_left2 (fun acc (_, b) (_, a) ->
      if b <> a then acc + 1 else acc
    ) 0 before after in
    let total = List.length keys in
    Printf.printf "Adding node '%s': %d/%d keys remapped (%.1f%%)\n"
      new_node remapped total
      (100.0 *. float_of_int remapped /. float_of_int (max 1 total));
    (remapped, total)

end

(* === Demo === *)
let () =
  let open ConsistentHash in
  Printf.printf "=== Consistent Hashing Demo ===\n\n";

  (* Create a ring and add some server nodes *)
  let ring = create ~vnodes:150 () in
  let ring = add_node ring "server-A" in
  let ring = add_node ring "server-B" in
  let ring = add_node ring "server-C" in
  pp ring;
  Printf.printf "\n";

  (* Look up some keys *)
  let test_keys = ["user:1001"; "user:1002"; "user:1003"; "session:abc";
                    "session:def"; "cache:homepage"; "cache:profile"] in
  Printf.printf "Key assignments:\n";
  List.iter (fun key ->
    match lookup ring key with
    | Some node -> Printf.printf "  %-20s -> %s\n" key node
    | None -> Printf.printf "  %-20s -> (no nodes)\n" key
  ) test_keys;
  Printf.printf "\n";

  (* Generate many keys and check distribution *)
  let many_keys = List.init 10000 (fun i -> Printf.sprintf "key:%d" i) in
  let dist = distribution ring many_keys in
  Printf.printf "Distribution of 10,000 keys across 3 nodes:\n";
  List.iter (fun (node, count) ->
    Printf.printf "  %-12s: %d keys (%.1f%%)\n" node count
      (100.0 *. float_of_int count /. 10000.0)
  ) (List.sort compare dist);
  Printf.printf "  Std deviation: %.1f\n\n" (balance_score ring many_keys);

  (* Show remapping impact when adding a 4th node *)
  let _ = remapping_impact ring many_keys "server-D" in
  Printf.printf "\n";

  (* Show remapping impact when removing a node *)
  let ring4 = add_node ring "server-D" in
  Printf.printf "After adding server-D, removing server-B:\n";
  let before = List.map (fun k -> (k, lookup ring4 k)) many_keys in
  let ring3 = remove_node ring4 "server-B" in
  let after = List.map (fun k -> (k, lookup ring3 k)) many_keys in
  let remapped = List.fold_left2 (fun acc (_, b) (_, a) ->
    if b <> a then acc + 1 else acc
  ) 0 before after in
  Printf.printf "  %d/%d keys remapped (%.1f%%)\n"
    remapped (List.length many_keys)
    (100.0 *. float_of_int remapped /. float_of_int (List.length many_keys));

  Printf.printf "\n=== Done ===\n"
