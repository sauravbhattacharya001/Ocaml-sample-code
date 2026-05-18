(* consistent_hashing.ml — Consistent Hashing Ring *)
(* A purely functional consistent hashing implementation for distributed     *)
(* systems key distribution. When nodes are added or removed, only K/N keys  *)
(* need to be remapped on average (K = total keys, N = total nodes).         *)
(*                                                                            *)
(* Supports: add_node, remove_node, lookup, virtual nodes (vnodes) for       *)
(* better load balance, node listing, key distribution stats.                *)
(*                                                                            *)
(* Performance: the ring is stored as a sorted [array] of ring points so     *)
(* [lookup] runs in O(log R) via binary search instead of the O(R) linear    *)
(* scan a list would require (R = node_count * vnodes). [distribution] over  *)
(* K keys becomes O(K log R) instead of O(K * R), which is a large win for   *)
(* the typical use case of looking up many keys against a stable ring.       *)
(* [add_node] / [remove_node] are O(R) (array rebuild), which is fine        *)
(* because they are rare relative to lookups in real workloads.              *)

module ConsistentHash = struct

  (** A point on the ring: hash position + owning node id *)
  type ring_point = {
    position : int;
    node_id  : string;
  }

  (** The hash ring *)
  type t = {
    ring       : ring_point array;  (** sorted by position, ascending *)
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
    { ring = [||]; vnodes; node_set = [] }

  (** Generate virtual-node points for a physical node *)
  let vnode_points node_id vnodes =
    Array.init vnodes (fun i ->
      let key = Printf.sprintf "%s#vn%d" node_id i in
      { position = hash_string key; node_id })

  (** Merge two sorted arrays of ring points into a new sorted array. *)
  let merge_sorted a b =
    let la = Array.length a and lb = Array.length b in
    if la = 0 then Array.copy b
    else if lb = 0 then Array.copy a
    else begin
      let out = Array.make (la + lb) a.(0) in
      let i = ref 0 and j = ref 0 and k = ref 0 in
      while !i < la && !j < lb do
        if a.(!i).position <= b.(!j).position then begin
          out.(!k) <- a.(!i); incr i
        end else begin
          out.(!k) <- b.(!j); incr j
        end;
        incr k
      done;
      while !i < la do out.(!k) <- a.(!i); incr i; incr k done;
      while !j < lb do out.(!k) <- b.(!j); incr j; incr k done;
      out
    end

  (** Add a physical node to the ring *)
  let add_node t node_id =
    if List.mem node_id t.node_set then t
    else
      let new_points = vnode_points node_id t.vnodes in
      (* Sort the new node's own vnode points (positions are hashed and
         therefore not in order) before merging into the existing ring. *)
      Array.sort (fun p q -> compare p.position q.position) new_points;
      let ring = merge_sorted t.ring new_points in
      { t with ring; node_set = t.node_set @ [node_id] }

  (** Remove a physical node from the ring *)
  let remove_node t node_id =
    if not (List.mem node_id t.node_set) then t
    else
      let ring =
        Array.of_list
          (List.filter (fun pt -> pt.node_id <> node_id)
             (Array.to_list t.ring))
      in
      let node_set = List.filter (fun n -> n <> node_id) t.node_set in
      { t with ring; node_set }

  (** Find the index of the first ring point with position >= h using
      binary search. Returns [Array.length t.ring] if no such point exists. *)
  let bsearch_ge ring h =
    let lo = ref 0 and hi = ref (Array.length ring) in
    while !lo < !hi do
      let mid = (!lo + !hi) lsr 1 in
      if ring.(mid).position >= h then hi := mid
      else lo := mid + 1
    done;
    !lo

  (** Look up which node owns a given key — walks clockwise from the
      key's hash position to find the first ring point. O(log R). *)
  let lookup t key =
    let n = Array.length t.ring in
    if n = 0 then None
    else
      let h = hash_string key in
      let idx = bsearch_ge t.ring h in
      let idx = if idx = n then 0 else idx in  (* wrap around *)
      Some t.ring.(idx).node_id

  (** List all physical nodes *)
  let nodes t = t.node_set

  (** Number of physical nodes *)
  let node_count t = List.length t.node_set

  (** Number of points on the ring (physical * vnodes) *)
  let ring_size t = Array.length t.ring

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

  (** Simulate adding a node and show key remapping impact *)
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
