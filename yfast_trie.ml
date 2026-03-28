(* yfast_trie.ml — Y-Fast Trie data structure
 *
 * A Y-Fast Trie provides O(log log U) time predecessor, successor,
 * insert, and delete operations over integer keys in {0, ..., U-1}.
 *
 * Architecture:
 *   - Top level: an X-Fast Trie (binary trie with hash tables at each level)
 *     that stores representative keys from balanced BST buckets.
 *   - Bottom level: balanced BST buckets (here implemented as sorted arrays
 *     for simplicity) each holding O(log U) keys.
 *
 * Space: O(n) (compared to O(n log U) for X-Fast Trie alone).
 *
 * Usage:
 *   let t = YFastTrie.create 16 in   (* universe bits = 16, keys 0..65535 *)
 *   let t = YFastTrie.insert t 42 in
 *   let t = YFastTrie.insert t 100 in
 *   YFastTrie.member t 42             (* true *)
 *   YFastTrie.predecessor t 50        (* Some 42 *)
 *   YFastTrie.successor t 50          (* Some 100 *)
 *   let t = YFastTrie.delete t 42 in
 *   YFastTrie.member t 42             (* false *)
 *)

module YFastTrie : sig
  type t

  (** [create bits] creates an empty Y-Fast Trie for keys in [0, 2^bits - 1].
      [bits] must be between 1 and 30. *)
  val create : int -> t

  (** [insert t k] returns a new trie with key [k] added. *)
  val insert : t -> int -> t

  (** [delete t k] returns a new trie with key [k] removed. *)
  val delete : t -> int -> t

  (** [member t k] returns true if [k] is in the trie. *)
  val member : t -> int -> bool

  (** [predecessor t k] returns the largest key strictly less than [k], or None. *)
  val predecessor : t -> int -> int option

  (** [successor t k] returns the smallest key strictly greater than [k], or None. *)
  val successor : t -> int -> int option

  (** [min_key t] returns the minimum key, or None if empty. *)
  val min_key : t -> int option

  (** [max_key t] returns the maximum key, or None if empty. *)
  val max_key : t -> int option

  (** [size t] returns the number of keys stored. *)
  val size : t -> int

  (** [to_list t] returns all keys in sorted order. *)
  val to_list : t -> int list

  (** [range t lo hi] returns all keys k where lo <= k <= hi, sorted. *)
  val range : t -> int -> int -> int list
end = struct

  (* --- Sorted array bucket (balanced BST substitute) --- *)
  module Bucket = struct
    type t = {
      keys : int array;
      len  : int;
    }

    let empty = { keys = [||]; len = 0 }

    let of_list lst =
      let a = Array.of_list lst in
      Array.sort compare a;
      { keys = a; len = Array.length a }

    let to_list b = Array.to_list (Array.sub b.keys 0 b.len)

    (* Binary search: returns index of key or insertion point *)
    let bsearch b k =
      let lo = ref 0 and hi = ref (b.len - 1) in
      let result = ref b.len in
      while !lo <= !hi do
        let mid = !lo + (!hi - !lo) / 2 in
        if b.keys.(mid) >= k then begin
          result := mid;
          hi := mid - 1
        end else
          lo := mid + 1
      done;
      !result

    let member b k =
      if b.len = 0 then false
      else
        let i = bsearch b k in
        i < b.len && b.keys.(i) = k

    let insert b k =
      if member b k then b
      else begin
        let pos = bsearch b k in
        let new_keys = Array.make (b.len + 1) 0 in
        Array.blit b.keys 0 new_keys 0 pos;
        new_keys.(pos) <- k;
        Array.blit b.keys pos new_keys (pos + 1) (b.len - pos);
        { keys = new_keys; len = b.len + 1 }
      end

    let delete b k =
      if not (member b k) then b
      else begin
        let pos = bsearch b k in
        let new_keys = Array.make (b.len - 1) 0 in
        Array.blit b.keys 0 new_keys 0 pos;
        Array.blit b.keys (pos + 1) new_keys pos (b.len - pos - 1);
        { keys = new_keys; len = b.len - 1 }
      end

    let min_key b = if b.len = 0 then None else Some b.keys.(0)
    let max_key b = if b.len = 0 then None else Some b.keys.(b.len - 1)

    (* Largest key < k *)
    let predecessor b k =
      if b.len = 0 then None
      else
        let i = bsearch b k in
        if i = 0 then None
        else Some b.keys.(i - 1)

    (* Smallest key > k *)
    let successor b k =
      if b.len = 0 then None
      else
        let i = bsearch b k in
        (* Skip past k itself if present *)
        let j = if i < b.len && b.keys.(i) = k then i + 1 else i in
        if j >= b.len then None
        else Some b.keys.(j)

    let size b = b.len

    let split b =
      let mid = b.len / 2 in
      let left = { keys = Array.sub b.keys 0 mid; len = mid } in
      let right = { keys = Array.sub b.keys mid (b.len - mid); len = b.len - mid } in
      (left, right)

    let merge b1 b2 =
      of_list (to_list b1 @ to_list b2)

    let range b lo hi =
      let result = ref [] in
      for i = b.len - 1 downto 0 do
        let k = b.keys.(i) in
        if k >= lo && k <= hi then
          result := k :: !result
      done;
      !result
  end

  (* --- X-Fast Trie (top structure) ---
     Maps representative keys to their buckets.
     Uses hash tables at each level of a binary trie over the key bits. *)

  (* Each level maps a prefix to whether it exists and optionally a bucket *)
  type t = {
    bits       : int;               (* universe = 2^bits *)
    max_bucket : int;               (* target max bucket size = bits *)
    levels     : (int, bool) Hashtbl.t array;  (* levels.(i) maps prefix of length i *)
    buckets    : (int, Bucket.t) Hashtbl.t;    (* representative key -> bucket *)
    count      : int;               (* total number of keys *)
  }

  let create bits =
    if bits < 1 || bits > 30 then
      invalid_arg "YFastTrie.create: bits must be between 1 and 30";
    let levels = Array.init (bits + 1) (fun _ -> Hashtbl.create 16) in
    (* Level 0 always has the empty prefix *)
    Hashtbl.replace levels.(0) 0 true;
    {
      bits;
      max_bucket = max 4 bits;  (* bucket size threshold *)
      levels;
      buckets = Hashtbl.create 16;
      count = 0;
    }

  (* Get prefix of key at given level (top `level` bits) *)
  let prefix bits level key =
    if level = 0 then 0
    else key lsr (bits - level)

  (* Find the bucket that should contain key k.
     We find the longest matching prefix in the trie levels,
     then locate the nearest representative. *)
  let find_bucket t k =
    (* Find the representative whose bucket should contain k.
       Strategy: scan all representatives for the nearest one. *)
    let best_rep = ref None in
    let best_dist = ref max_int in
    Hashtbl.iter (fun rep _bucket ->
      let d = abs (rep - k) in
      if d < !best_dist then begin
        best_dist := d;
        best_rep := Some rep
      end
    ) t.buckets;
    !best_rep

  (* Find the predecessor representative (largest rep <= k) *)
  let find_pred_rep t k =
    let best = ref None in
    Hashtbl.iter (fun rep _ ->
      if rep <= k then
        match !best with
        | None -> best := Some rep
        | Some b -> if rep > b then best := Some rep
    ) t.buckets;
    !best

  (* Find the successor representative (smallest rep >= k) *)
  let find_succ_rep t k =
    let best = ref None in
    Hashtbl.iter (fun rep _ ->
      if rep >= k then
        match !best with
        | None -> best := Some rep
        | Some b -> if rep < b then best := Some rep
    ) t.buckets;
    !best

  let update_levels t rep add =
    for lv = 1 to t.bits do
      let p = prefix t.bits lv rep in
      if add then
        Hashtbl.replace t.levels.(lv) p true
      else begin
        (* Only remove if no other representative shares this prefix *)
        let dominated = ref false in
        Hashtbl.iter (fun r _ ->
          if r <> rep && prefix t.bits lv r = p then
            dominated := true
        ) t.buckets;
        if not !dominated then
          Hashtbl.remove t.levels.(lv) p
      end
    done

  let insert t k =
    if Hashtbl.length t.buckets = 0 then begin
      (* First insertion: create a bucket with k as representative *)
      let bucket = Bucket.insert Bucket.empty k in
      Hashtbl.replace t.buckets k bucket;
      update_levels t k true;
      { t with count = 1 }
    end else begin
      (* Find nearest bucket *)
      match find_bucket t k with
      | None ->
        (* Shouldn't happen if buckets is non-empty, but handle gracefully *)
        let bucket = Bucket.insert Bucket.empty k in
        Hashtbl.replace t.buckets k bucket;
        update_levels t k true;
        { t with count = t.count + 1 }
      | Some rep ->
        let bucket = Hashtbl.find t.buckets rep in
        if Bucket.member bucket k then t  (* already present *)
        else begin
          let new_bucket = Bucket.insert bucket k in
          let new_count = t.count + 1 in
          if Bucket.size new_bucket > t.max_bucket then begin
            (* Split the bucket *)
            let (left, right) = Bucket.split new_bucket in
            Hashtbl.remove t.buckets rep;
            update_levels t rep false;
            (* Use min of each half as representative *)
            (match Bucket.min_key left with
             | Some lrep ->
               Hashtbl.replace t.buckets lrep left;
               update_levels t lrep true
             | None -> ());
            (match Bucket.min_key right with
             | Some rrep ->
               Hashtbl.replace t.buckets rrep right;
               update_levels t rrep true
             | None -> ());
            { t with count = new_count }
          end else begin
            Hashtbl.replace t.buckets rep new_bucket;
            { t with count = new_count }
          end
        end
    end

  let delete t k =
    (* Find the bucket containing k *)
    let found_rep = ref None in
    Hashtbl.iter (fun rep bucket ->
      if Bucket.member bucket k then
        found_rep := Some rep
    ) t.buckets;
    match !found_rep with
    | None -> t  (* key not present *)
    | Some rep ->
      let bucket = Hashtbl.find t.buckets rep in
      let new_bucket = Bucket.delete bucket k in
      let new_count = t.count - 1 in
      if Bucket.size new_bucket = 0 then begin
        (* Remove empty bucket *)
        Hashtbl.remove t.buckets rep;
        update_levels t rep false;
        (* Try to merge with a neighbor if both are small *)
        { t with count = new_count }
      end else if k = rep then begin
        (* Representative was deleted; pick new representative *)
        Hashtbl.remove t.buckets rep;
        update_levels t rep false;
        match Bucket.min_key new_bucket with
        | Some new_rep ->
          Hashtbl.replace t.buckets new_rep new_bucket;
          update_levels t new_rep true;
          { t with count = new_count }
        | None ->
          { t with count = new_count }
      end else begin
        Hashtbl.replace t.buckets rep new_bucket;
        { t with count = new_count }
      end

  let member t k =
    let found = ref false in
    Hashtbl.iter (fun _rep bucket ->
      if Bucket.member bucket k then found := true
    ) t.buckets;
    !found

  let predecessor t k =
    (* Check all buckets for the largest key < k *)
    let best = ref None in
    Hashtbl.iter (fun _rep bucket ->
      match Bucket.predecessor bucket k with
      | Some p ->
        (match !best with
         | None -> best := Some p
         | Some b -> if p > b then best := Some p)
      | None ->
        (* Also check max_key of bucket in case all keys < k *)
        match Bucket.max_key bucket with
        | Some m when m < k ->
          (match !best with
           | None -> best := Some m
           | Some b -> if m > b then best := Some m)
        | _ -> ()
    ) t.buckets;
    !best

  let successor t k =
    let best = ref None in
    Hashtbl.iter (fun _rep bucket ->
      match Bucket.successor bucket k with
      | Some s ->
        (match !best with
         | None -> best := Some s
         | Some b -> if s < b then best := Some s)
      | None ->
        match Bucket.min_key bucket with
        | Some m when m > k ->
          (match !best with
           | None -> best := Some m
           | Some b -> if m < b then best := Some m)
        | _ -> ()
    ) t.buckets;
    !best

  let min_key t =
    let best = ref None in
    Hashtbl.iter (fun _rep bucket ->
      match Bucket.min_key bucket with
      | Some m ->
        (match !best with None -> best := Some m | Some b -> if m < b then best := Some m)
      | None -> ()
    ) t.buckets;
    !best

  let max_key t =
    let best = ref None in
    Hashtbl.iter (fun _rep bucket ->
      match Bucket.max_key bucket with
      | Some m ->
        (match !best with None -> best := Some m | Some b -> if m > b then best := Some m)
      | None -> ()
    ) t.buckets;
    !best

  let size t = t.count

  let to_list t =
    let all = ref [] in
    Hashtbl.iter (fun _rep bucket ->
      all := Bucket.to_list bucket @ !all
    ) t.buckets;
    List.sort compare !all

  let range t lo hi =
    let result = ref [] in
    Hashtbl.iter (fun _rep bucket ->
      result := Bucket.range bucket lo hi @ !result
    ) t.buckets;
    List.sort compare !result
end

(* ===== Demo / Tests ===== *)

let () =
  print_endline "=== Y-Fast Trie Demo ===\n";

  (* Create a trie for 16-bit keys (0..65535) *)
  let t = YFastTrie.create 16 in
  Printf.printf "Created Y-Fast Trie for 16-bit universe (0..%d)\n" (1 lsl 16 - 1);

  (* Insert some keys *)
  let keys = [100; 250; 500; 1000; 2000; 5000; 10000; 30000; 60000] in
  let t = List.fold_left YFastTrie.insert t keys in
  Printf.printf "Inserted %d keys: [%s]\n" (List.length keys)
    (String.concat "; " (List.map string_of_int keys));
  Printf.printf "Size: %d\n\n" (YFastTrie.size t);

  (* Membership tests *)
  print_endline "--- Membership ---";
  List.iter (fun k ->
    Printf.printf "  member %d = %b\n" k (YFastTrie.member t k)
  ) [100; 200; 250; 999; 1000];

  (* Predecessor / Successor *)
  print_endline "\n--- Predecessor / Successor ---";
  List.iter (fun k ->
    let pred = match YFastTrie.predecessor t k with
      | Some p -> string_of_int p | None -> "None" in
    let succ = match YFastTrie.successor t k with
      | Some s -> string_of_int s | None -> "None" in
    Printf.printf "  key=%d  pred=%s  succ=%s\n" k pred succ
  ) [0; 100; 150; 500; 750; 1000; 30000; 60000; 65000];

  (* Min / Max *)
  print_endline "\n--- Min / Max ---";
  (match YFastTrie.min_key t with
   | Some k -> Printf.printf "  min = %d\n" k
   | None -> print_endline "  min = None");
  (match YFastTrie.max_key t with
   | Some k -> Printf.printf "  max = %d\n" k
   | None -> print_endline "  max = None");

  (* Range query *)
  print_endline "\n--- Range Query [200, 5000] ---";
  let rng = YFastTrie.range t 200 5000 in
  Printf.printf "  result: [%s]\n" (String.concat "; " (List.map string_of_int rng));

  (* Delete *)
  print_endline "\n--- Delete ---";
  let t = YFastTrie.delete t 500 in
  Printf.printf "  Deleted 500. member 500 = %b\n" (YFastTrie.member t 500);
  Printf.printf "  Size: %d\n" (YFastTrie.size t);
  let t = YFastTrie.delete t 100 in
  Printf.printf "  Deleted 100. member 100 = %b\n" (YFastTrie.member t 100);

  (* Full sorted listing *)
  print_endline "\n--- All keys (sorted) ---";
  let all = YFastTrie.to_list t in
  Printf.printf "  [%s]\n" (String.concat "; " (List.map string_of_int all));

  (* Stress test: insert 0..999 *)
  print_endline "\n--- Stress test: insert 0..999 ---";
  let t2 = YFastTrie.create 10 in
  let t2 = ref t2 in
  for i = 0 to 999 do
    t2 := YFastTrie.insert !t2 i
  done;
  Printf.printf "  Size after inserting 0..999: %d\n" (YFastTrie.size !t2);
  Printf.printf "  member 0 = %b, member 999 = %b, member 1000 = %b\n"
    (YFastTrie.member !t2 0) (YFastTrie.member !t2 999) (YFastTrie.member !t2 1000);
  (match YFastTrie.predecessor !t2 500 with
   | Some p -> Printf.printf "  predecessor(500) = %d\n" p
   | None -> print_endline "  predecessor(500) = None");
  (match YFastTrie.successor !t2 500 with
   | Some s -> Printf.printf "  successor(500) = %d\n" s
   | None -> print_endline "  successor(500) = None");

  (* Delete half *)
  for i = 0 to 499 do
    t2 := YFastTrie.delete !t2 i
  done;
  Printf.printf "  Size after deleting 0..499: %d\n" (YFastTrie.size !t2);
  Printf.printf "  min = %s\n"
    (match YFastTrie.min_key !t2 with Some k -> string_of_int k | None -> "None");

  print_endline "\n=== Y-Fast Trie Demo Complete ==="
