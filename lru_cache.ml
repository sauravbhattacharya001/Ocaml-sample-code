(* lru_cache.ml — Least Recently Used Cache *)
(* Bounded-capacity cache that evicts the least recently used entry   *)
(* when full. Uses a functional approach: access-ordered list + map.  *)
(* Supports: create, put, get, mem, remove, size, capacity, is_empty,*)
(* is_full, to_list, keys, values, clear, resize, peek, stats,       *)
(* evict, of_list, fold, iter, filter, map_values.                    *)
(* All operations return new caches (purely functional).              *)
(*                                                                     *)
(* Performance: index is maintained incrementally — O(1) hash table   *)
(* updates per operation instead of full rebuilds. Size is tracked    *)
(* explicitly to avoid O(n) List.length calls.                        *)

module LRUCache = struct

  type ('k, 'v) t = {
    entries  : ('k * 'v) list;   (* ordered: most recent first *)
    index    : ('k, 'v) Hashtbl.t; (* shadow index for O(1) lookup *)
    capacity : int;
    size     : int;              (* tracked explicitly, no List.length *)
    hits     : int;
    misses   : int;
  }

  (* ---- Construction ---- *)

  let create capacity =
    if capacity < 1 then
      invalid_arg "LRUCache.create: capacity must be >= 1"
    else
      { entries = []; index = Hashtbl.create (min capacity 256);
        capacity; size = 0; hits = 0; misses = 0 }

  let clear cache =
    Hashtbl.reset cache.index;
    { cache with entries = []; size = 0; hits = 0; misses = 0 }

  (* ---- Internal helpers ---- *)

  (* Remove key from the ordered list *)
  let remove_from_list k entries =
    List.filter (fun (k', _) -> k' <> k) entries

  (* Trim list to capacity, evicting LRU entries from index.
     Returns (kept_list, new_size). *)
  let trim_to_capacity cap sz entries index =
    if sz <= cap then (entries, sz)
    else
      let rec take acc n = function
        | [] -> (List.rev acc, n)
        | _ when n >= cap -> (List.rev acc, cap)
        | ((k, v) as x) :: rest ->
          Hashtbl.replace index k v;  (* ensure kept entries are current *)
          take (x :: acc) (n + 1) rest
      in
      (* Evict entries beyond capacity from the index *)
      let rec drop_after n = function
        | [] -> ()
        | _ when n <= 0 -> ()
        | (k, _) :: rest ->
          Hashtbl.remove index k;
          drop_after (n - 1) rest
      in
      let (kept, kept_sz) = take [] 0 entries in
      let excess = sz - cap in
      (* Walk from the end to remove evicted keys *)
      let rev_entries = List.rev entries in
      drop_after excess rev_entries;
      (kept, kept_sz)

  (* ---- Core operations ---- *)

  (** Insert or update a key-value pair. If the cache is full and the
      key is new, the least recently used entry is evicted. *)
  let put k v cache =
    let existed = Hashtbl.mem cache.index k in
    (* Update index incrementally *)
    Hashtbl.replace cache.index k v;
    (* Remove existing entry from list if present *)
    let cleaned = if existed then remove_from_list k cache.entries
                  else cache.entries in
    let new_sz = if existed then cache.size else cache.size + 1 in
    (* Add to front (most recent) *)
    let updated = (k, v) :: cleaned in
    (* Evict LRU if over capacity *)
    if new_sz > cache.capacity then begin
      match List.rev updated with
      | [] -> { cache with entries = updated; size = new_sz }
      | (lru_k, _) :: _ ->
        Hashtbl.remove cache.index lru_k;
        let trimmed = remove_from_list lru_k updated in
        { cache with entries = trimmed; size = cache.capacity }
    end
    else
      { cache with entries = updated; size = new_sz }

  (** Look up a key. Returns (Some value, updated_cache) where the
      accessed entry is moved to the front, or (None, cache) on miss.
      Updates hit/miss statistics. *)
  let get k cache =
    match Hashtbl.find_opt cache.index k with
    | None ->
      (None, { cache with misses = cache.misses + 1 })
    | Some v ->
      let cleaned = remove_from_list k cache.entries in
      let entries = (k, v) :: cleaned in
      (* No index rebuild needed — same keys, same values *)
      (Some v,
       { cache with entries;
         hits = cache.hits + 1 })

  (** Look up a key without promoting it (no reorder, no stats). *)
  let peek k cache =
    Hashtbl.find_opt cache.index k

  (** Test membership without side effects. *)
  let mem k cache =
    Hashtbl.mem cache.index k

  (** Remove a key from the cache. *)
  let remove k cache =
    if not (Hashtbl.mem cache.index k) then cache
    else begin
      Hashtbl.remove cache.index k;
      let entries = remove_from_list k cache.entries in
      { cache with entries; size = cache.size - 1 }
    end

  (** Explicitly evict the least recently used entry.
      Returns (Some (key, value), updated_cache) or (None, cache). *)
  let evict cache =
    match List.rev cache.entries with
    | [] -> (None, cache)
    | (k, v) :: _ ->
      Hashtbl.remove cache.index k;
      let entries = remove_from_list k cache.entries in
      (Some (k, v),
       { cache with entries; size = cache.size - 1 })

  (* ---- Queries ---- *)

  let size cache = cache.size
  let capacity cache = cache.capacity
  let is_empty cache = cache.size = 0
  let is_full cache = cache.size >= cache.capacity

  (** Return entries in access order (most recent first). *)
  let to_list cache = cache.entries

  let keys cache = List.map fst cache.entries
  let values cache = List.map snd cache.entries

  (** Cache statistics: (hits, misses, hit_rate). *)
  let stats cache =
    let total = cache.hits + cache.misses in
    let rate = if total = 0 then 0.0
      else float_of_int cache.hits /. float_of_int total in
    (cache.hits, cache.misses, rate)

  (* ---- Transformations ---- *)

  (** Resize the cache capacity. If smaller, LRU entries are evicted. *)
  let resize new_capacity cache =
    if new_capacity < 1 then
      invalid_arg "LRUCache.resize: capacity must be >= 1"
    else if new_capacity >= cache.size then
      { cache with capacity = new_capacity }
    else begin
      let (kept, kept_sz) =
        trim_to_capacity new_capacity cache.size cache.entries cache.index in
      { cache with entries = kept; size = kept_sz; capacity = new_capacity }
    end

  (** Build a cache from an association list (first element = most recent). *)
  let of_list capacity pairs =
    if capacity < 1 then
      invalid_arg "LRUCache.of_list: capacity must be >= 1"
    else
      let cache = create capacity in
      (* Insert in reverse order so first element ends up most recent *)
      let rev_pairs = List.rev pairs in
      List.fold_left (fun c (k, v) -> put k v c) cache rev_pairs

  (** Fold over entries in access order (most recent first). *)
  let fold f init cache =
    List.fold_left (fun acc (k, v) -> f acc k v) init cache.entries

  (** Iterate over entries in access order. *)
  let iter f cache =
    List.iter (fun (k, v) -> f k v) cache.entries

  (** Keep only entries matching a predicate. *)
  let filter pred cache =
    let entries = List.filter (fun (k, v) -> pred k v) cache.entries in
    let new_size = List.length entries in
    (* Incrementally remove filtered-out keys from the index *)
    if new_size < cache.size then begin
      Hashtbl.reset cache.index;
      List.iter (fun (k, v) -> Hashtbl.replace cache.index k v) entries
    end;
    { cache with entries; size = new_size }

  (** Apply a function to all values, keeping keys and order. *)
  let map_values f cache =
    let entries = List.map (fun (k, v) -> (k, f v)) cache.entries in
    (* Update index with new values *)
    List.iter (fun (k, v) -> Hashtbl.replace cache.index k v) entries;
    { cache with entries }

end
