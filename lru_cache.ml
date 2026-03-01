(* lru_cache.ml — Least Recently Used Cache *)
(* Bounded-capacity cache that evicts the least recently used entry   *)
(* when full. Uses a functional approach: access-ordered list + map.  *)
(* Supports: create, put, get, mem, remove, size, capacity, is_empty,*)
(* is_full, to_list, keys, values, clear, resize, peek, stats,       *)
(* evict, of_list, fold, iter, filter, map_values.                    *)
(* All operations return new caches (purely functional).              *)

module LRUCache = struct

  type ('k, 'v) t = {
    entries  : ('k * 'v) list;   (* ordered: most recent first *)
    index    : ('k, 'v) Hashtbl.t; (* shadow index for O(1) lookup *)
    capacity : int;
    hits     : int;
    misses   : int;
  }

  (* ---- Construction ---- *)

  let create capacity =
    if capacity < 1 then
      invalid_arg "LRUCache.create: capacity must be >= 1"
    else
      { entries = []; index = Hashtbl.create capacity;
        capacity; hits = 0; misses = 0 }

  let clear cache =
    { entries = []; index = Hashtbl.create cache.capacity;
      capacity = cache.capacity; hits = 0; misses = 0 }

  (* ---- Internal helpers ---- *)

  (* Remove key from the ordered list *)
  let remove_from_list k entries =
    List.filter (fun (k', _) -> k' <> k) entries

  (* Trim list to capacity, returning (kept, evicted_keys) *)
  let trim_to_capacity cap entries =
    if List.length entries <= cap then (entries, [])
    else
      let rec take acc n = function
        | [] -> (List.rev acc, [])
        | _ when n >= cap -> (List.rev acc, [])
        | x :: rest -> take (x :: acc) (n + 1) rest
      in
      let (kept, _) = take [] 0 entries in
      let evicted_keys =
        let rec drop n = function
          | [] -> []
          | _ :: rest when n > 0 -> drop (n - 1) rest
          | remaining -> List.map fst remaining
        in
        drop cap entries
      in
      (kept, evicted_keys)

  let rebuild_index entries cap =
    let tbl = Hashtbl.create cap in
    List.iter (fun (k, v) -> Hashtbl.replace tbl k v) entries;
    tbl

  (* ---- Core operations ---- *)

  (** Insert or update a key-value pair. If the cache is full and the
      key is new, the least recently used entry is evicted. *)
  let put k v cache =
    (* Remove existing entry if present *)
    let cleaned = remove_from_list k cache.entries in
    (* Add to front (most recent) *)
    let updated = (k, v) :: cleaned in
    (* Trim if over capacity *)
    let (kept, _evicted) = trim_to_capacity cache.capacity updated in
    let idx = rebuild_index kept cache.capacity in
    { entries = kept; index = idx;
      capacity = cache.capacity;
      hits = cache.hits; misses = cache.misses }

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
      let idx = rebuild_index entries cache.capacity in
      (Some v,
       { entries; index = idx;
         capacity = cache.capacity;
         hits = cache.hits + 1; misses = cache.misses })

  (** Look up a key without promoting it (no reorder, no stats). *)
  let peek k cache =
    Hashtbl.find_opt cache.index k

  (** Test membership without side effects. *)
  let mem k cache =
    Hashtbl.mem cache.index k

  (** Remove a key from the cache. *)
  let remove k cache =
    if not (Hashtbl.mem cache.index k) then cache
    else
      let entries = remove_from_list k cache.entries in
      let idx = rebuild_index entries cache.capacity in
      { entries; index = idx;
        capacity = cache.capacity;
        hits = cache.hits; misses = cache.misses }

  (** Explicitly evict the least recently used entry.
      Returns (Some (key, value), updated_cache) or (None, cache). *)
  let evict cache =
    match List.rev cache.entries with
    | [] -> (None, cache)
    | (k, v) :: _ ->
      let entries = remove_from_list k cache.entries in
      let idx = rebuild_index entries cache.capacity in
      (Some (k, v),
       { entries; index = idx;
         capacity = cache.capacity;
         hits = cache.hits; misses = cache.misses })

  (* ---- Queries ---- *)

  let size cache = List.length cache.entries
  let capacity cache = cache.capacity
  let is_empty cache = cache.entries = []
  let is_full cache = List.length cache.entries >= cache.capacity

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
    else
      let (kept, _) = trim_to_capacity new_capacity cache.entries in
      let idx = rebuild_index kept new_capacity in
      { entries = kept; index = idx;
        capacity = new_capacity;
        hits = cache.hits; misses = cache.misses }

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
    let idx = rebuild_index entries cache.capacity in
    { entries; index = idx;
      capacity = cache.capacity;
      hits = cache.hits; misses = cache.misses }

  (** Apply a function to all values, keeping keys and order. *)
  let map_values f cache =
    let entries = List.map (fun (k, v) -> (k, f v)) cache.entries in
    let idx = rebuild_index entries cache.capacity in
    { entries; index = idx;
      capacity = cache.capacity;
      hits = cache.hits; misses = cache.misses }

end
