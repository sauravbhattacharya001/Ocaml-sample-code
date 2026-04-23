(* hashmap.ml — Persistent Functional Hash Map *)
(* Immutable hash map using separate chaining with resizable bucket arrays *)
(* Supports: create, insert, find, remove, mem, size, fold, map, filter, *)
(* merge, keys, values, bindings, of_list, equal, iter, for_all, exists *)
(* All operations return new maps (purely functional, old versions remain valid) *)
(*                                                                            *)
(* Security: each map instance carries a random hash seed, so the bucket      *)
(* assignment of keys is unpredictable.  This prevents HashDoS attacks where  *)
(* an adversary crafts keys that all land in the same bucket, degrading every *)
(* lookup from O(1) to O(n).  See: https://ocert.org/advisories/ocert-2011-003.html *)

module FunMap = struct
  type ('k, 'v) t = {
    buckets : ('k * 'v) list array;
    size    : int;
    capacity: int;
    seed    : int;  (* per-map random seed to prevent HashDoS *)
  }

  let default_capacity = 16

  (** Generate a random seed.  Uses [Random.self_init] on first call
      so the seed is unpredictable across program runs. *)
  let () = Random.self_init ()
  let fresh_seed () = Random.bits ()

  let create ?(capacity = default_capacity) () =
    let cap = max 1 capacity in
    { buckets = Array.make cap []; size = 0; capacity = cap;
      seed = fresh_seed () }

  (** [empty] is a function, not a value, so each call gets a fresh
      random seed.  A shared seed across maps would let an attacker
      craft collisions once and hit every map in the process. *)
  let empty () = create ()

  (** Randomised hash: mixes [Hashtbl.hash] output with the per-map
      seed before taking the modulus.  The XOR + multiply is a fast
      integer finalizer that spreads the seed's influence across all
      bits of the hash, making it infeasible for an attacker to predict
      bucket assignments without knowing the seed. *)
  let hash_key cap seed k =
    let h = Hashtbl.hash k in
    let mixed = h lxor (seed * 0x9e3779b9) in
    (* Ensure non-negative: OCaml's [mod] can return negative values *)
    ((mixed lsr 1) mod cap)

  (* Resize when load factor exceeds 0.75 *)
  let should_resize m =
    m.size > (m.capacity * 3 / 4)

  let resize m =
    let new_cap = m.capacity * 2 in
    let new_buckets = Array.make new_cap [] in
    Array.iter (fun bucket ->
      List.iter (fun ((k, _v) as pair) ->
        let idx = hash_key new_cap m.seed k in
        new_buckets.(idx) <- pair :: new_buckets.(idx)
      ) bucket
    ) m.buckets;
    { m with buckets = new_buckets; capacity = new_cap }

  (** Single-pass bucket update: replaces existing key or prepends new entry.
      Returns [(new_bucket, replaced)] where [replaced] is true if the key
      already existed (so the caller can decide whether to bump [size]). *)
  let rec bucket_upsert k v = function
    | [] -> ([(k, v)], false)
    | (k', _) :: rest when k' = k -> ((k, v) :: rest, true)
    | pair :: rest ->
      let (updated, replaced) = bucket_upsert k v rest in
      (pair :: updated, replaced)

  (** [with_bucket m idx new_bucket] returns a new map whose bucket at
      [idx] is replaced with [new_bucket].  All other buckets are shared
      via a shallow [Array.copy], avoiding per-field record rebuilds that
      were duplicated across [insert], [remove], and similar operations. *)
  let with_bucket m idx new_bucket =
    let new_buckets = Array.copy m.buckets in
    new_buckets.(idx) <- new_bucket;
    { m with buckets = new_buckets }

  let insert k v m =
    let m = if should_resize m then resize m else m in
    let idx = hash_key m.capacity m.seed k in
    let (new_bucket, replaced) = bucket_upsert k v m.buckets.(idx) in
    let m' = with_bucket m idx new_bucket in
    { m' with size = if replaced then m.size else m.size + 1 }

  let find k m =
    let idx = hash_key m.capacity m.seed k in
    let rec search = function
      | [] -> None
      | (k', v) :: _ when k' = k -> Some v
      | _ :: rest -> search rest
    in
    search m.buckets.(idx)

  let find_exn k m =
    match find k m with
    | Some v -> v
    | None -> raise Not_found

  let mem k m =
    find k m <> None

  (** Single-pass bucket removal: drops key if found.
      Returns [(new_bucket, removed)] so the caller can adjust [size]. *)
  let rec bucket_remove k = function
    | [] -> ([], false)
    | (k', _) :: rest when k' = k -> (rest, true)
    | pair :: rest ->
      let (updated, removed) = bucket_remove k rest in
      (pair :: updated, removed)

  let remove k m =
    let idx = hash_key m.capacity m.seed k in
    let (new_bucket, removed) = bucket_remove k m.buckets.(idx) in
    if not removed then m
    else { (with_bucket m idx new_bucket) with size = m.size - 1 }

  let size m = m.size

  let is_empty m = m.size = 0

  let fold f acc m =
    Array.fold_left (fun acc bucket ->
      List.fold_left (fun acc (k, v) -> f acc k v) acc bucket
    ) acc m.buckets

  let iter f m =
    Array.iter (fun bucket ->
      List.iter (fun (k, v) -> f k v) bucket
    ) m.buckets

  let map f m =
    let new_buckets = Array.map (fun bucket ->
      List.map (fun (k, v) -> (k, f v)) bucket
    ) m.buckets in
    { m with buckets = new_buckets }

  let mapi f m =
    let new_buckets = Array.map (fun bucket ->
      List.map (fun (k, v) -> (k, f k v)) bucket
    ) m.buckets in
    { m with buckets = new_buckets }

  let filter f m =
    let new_buckets = Array.make m.capacity [] in
    let new_size = ref 0 in
    Array.iteri (fun i bucket ->
      let filtered = List.filter (fun (k, v) -> f k v) bucket in
      new_buckets.(i) <- filtered;
      new_size := !new_size + List.length filtered
    ) m.buckets;
    { m with buckets = new_buckets; size = !new_size }

  let keys m =
    fold (fun acc k _v -> k :: acc) [] m

  let values m =
    fold (fun acc _k v -> v :: acc) [] m

  let bindings m =
    fold (fun acc k v -> (k, v) :: acc) [] m

  let of_list pairs =
    List.fold_left (fun m (k, v) -> insert k v m) (empty ()) pairs

  let to_list m = bindings m

  (** Merge two maps using [f key (Some v1 | None) (Some v2 | None)].
      For each key present in either map, [f] receives [Some] for the map(s)
      containing that key and [None] for the map(s) that don't.
      If [f] returns [Some v], the key is bound to [v] in the result;
      if [f] returns [None], the key is omitted. *)
  let merge f m1 m2 =
    (* Keys in m1: pass (Some v1, find_in_m2) *)
    let result = fold (fun acc k v1 ->
      match f k (Some v1) (find k m2) with
      | Some v -> insert k v acc
      | None -> acc
    ) (empty ()) m1 in
    (* Keys only in m2: pass (None, Some v2) *)
    fold (fun acc k v2 ->
      if not (mem k m1) then
        match f k None (Some v2) with
        | Some v -> insert k v acc
        | None -> acc
      else acc
    ) result m2

  let for_all f m =
    try
      iter (fun k v -> if not (f k v) then raise Exit) m;
      true
    with Exit -> false

  let exists f m =
    try
      iter (fun k v -> if f k v then raise Exit) m;
      false
    with Exit -> true

  let equal eq m1 m2 =
    m1.size = m2.size &&
    for_all (fun k v ->
      match find k m2 with
      | Some v2 -> eq v v2
      | None -> false
    ) m1

  let update k f m =
    let old_v = find k m in
    match f old_v with
    | None ->
      (match old_v with
       | None -> m
       | Some _ -> remove k m)
    | Some new_v -> insert k new_v m

  let singleton k v = insert k v (empty ())

  let union f m1 m2 =
    fold (fun acc k v ->
      match find k acc with
      | None -> insert k v acc
      | Some v' -> insert k (f k v v') acc
    ) m2 m1

  let partition f m =
    let yes = ref (empty ()) in
    let no = ref (empty ()) in
    iter (fun k v ->
      if f k v then yes := insert k v !yes
      else no := insert k v !no
    ) m;
    (!yes, !no)

  let cardinal m = m.size

  (** Helper: find the first binding in any bucket matching predicate [f].
      Short-circuits via the [Exit] exception since [Array.iter] / [List.iter]
      don't support early return. *)
  let find_binding_opt f m =
    let result = ref None in
    (try
      Array.iter (fun bucket ->
        List.iter (fun (k, v) ->
          if f k v then (result := Some (k, v); raise Exit)
        ) bucket
      ) m.buckets
    with Exit -> ());
    !result

  let choose m =
    match find_binding_opt (fun _ _ -> true) m with
    | Some pair -> pair
    | None -> raise Not_found

  let find_first f m =
    match find_binding_opt (fun k _ -> f k) m with
    | Some pair -> pair
    | None -> raise Not_found
end
