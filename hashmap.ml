(* hashmap.ml — Persistent Functional Hash Map *)
(* Immutable hash map using separate chaining with resizable bucket arrays *)
(* Supports: create, insert, find, remove, mem, size, fold, map, filter, *)
(* merge, keys, values, bindings, of_list, equal, iter, for_all, exists *)
(* All operations return new maps (purely functional, old versions remain valid) *)

module FunMap = struct
  type ('k, 'v) t = {
    buckets : ('k * 'v) list array;
    size    : int;
    capacity: int;
  }

  let default_capacity = 16

  let create ?(capacity = default_capacity) () =
    let cap = max 1 capacity in
    { buckets = Array.make cap []; size = 0; capacity = cap }

  let empty = create ()

  let hash_key cap k =
    (Hashtbl.hash k) mod cap |> abs

  (* Resize when load factor exceeds 0.75 *)
  let should_resize m =
    m.size > (m.capacity * 3 / 4)

  let resize m =
    let new_cap = m.capacity * 2 in
    let new_buckets = Array.make new_cap [] in
    Array.iter (fun bucket ->
      List.iter (fun ((k, _v) as pair) ->
        let idx = hash_key new_cap k in
        new_buckets.(idx) <- pair :: new_buckets.(idx)
      ) bucket
    ) m.buckets;
    { buckets = new_buckets; size = m.size; capacity = new_cap }

  let insert k v m =
    let m = if should_resize m then resize m else m in
    let idx = hash_key m.capacity k in
    let bucket = m.buckets.(idx) in
    let existed = List.exists (fun (k', _) -> k' = k) bucket in
    let new_bucket =
      if existed then
        List.map (fun (k', v') -> if k' = k then (k, v) else (k', v')) bucket
      else
        (k, v) :: bucket
    in
    let new_buckets = Array.copy m.buckets in
    new_buckets.(idx) <- new_bucket;
    { buckets = new_buckets;
      size = if existed then m.size else m.size + 1;
      capacity = m.capacity }

  let find k m =
    let idx = hash_key m.capacity k in
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

  let remove k m =
    let idx = hash_key m.capacity k in
    let bucket = m.buckets.(idx) in
    let existed = List.exists (fun (k', _) -> k' = k) bucket in
    if not existed then m
    else begin
      let new_bucket = List.filter (fun (k', _) -> k' <> k) bucket in
      let new_buckets = Array.copy m.buckets in
      new_buckets.(idx) <- new_bucket;
      { buckets = new_buckets;
        size = m.size - 1;
        capacity = m.capacity }
    end

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
    { buckets = new_buckets; size = !new_size; capacity = m.capacity }

  let keys m =
    fold (fun acc k _v -> k :: acc) [] m

  let values m =
    fold (fun acc _k v -> v :: acc) [] m

  let bindings m =
    fold (fun acc k v -> (k, v) :: acc) [] m

  let of_list pairs =
    List.fold_left (fun m (k, v) -> insert k v m) empty pairs

  let to_list m = bindings m

  let merge f m1 m2 =
    let result = fold (fun acc k v ->
      match find k m2 with
      | None -> insert k (f k v None) acc
      | Some v2 -> insert k (f k v (Some v2)) acc
    ) (create ()) m1 in
    fold (fun acc k v ->
      if not (mem k m1) then
        insert k (f k v None) acc
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

  let singleton k v = insert k v empty

  let union f m1 m2 =
    fold (fun acc k v ->
      match find k acc with
      | None -> insert k v acc
      | Some v' -> insert k (f k v v') acc
    ) m2 m1

  let partition f m =
    let yes = ref (create ()) in
    let no = ref (create ()) in
    iter (fun k v ->
      if f k v then yes := insert k v !yes
      else no := insert k v !no
    ) m;
    (!yes, !no)

  let cardinal m = m.size

  let choose m =
    if is_empty m then raise Not_found
    else begin
      let result = ref None in
      (try
        iter (fun k v -> result := Some (k, v); raise Exit) m
      with Exit -> ());
      match !result with
      | Some pair -> pair
      | None -> raise Not_found
    end

  let find_first f m =
    let result = ref None in
    (try
      iter (fun k v -> if f k then (result := Some (k, v); raise Exit)) m
    with Exit -> ());
    match !result with
    | Some pair -> pair
    | None -> raise Not_found
end
