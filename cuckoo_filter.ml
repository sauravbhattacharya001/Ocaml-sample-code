(* Cuckoo Filter - A space-efficient probabilistic data structure
   that supports membership testing AND deletion (unlike Bloom filters).

   Key properties:
   - Approximate set membership (like Bloom filter)
   - Supports deletion (Bloom filters don't)
   - Better locality of reference than Bloom filters
   - Uses fingerprints stored in a bucket-based hash table
   - False positive rate configurable via fingerprint size

   Reference: "Cuckoo Filter: Practically Better Than Bloom"
              by Fan, Andersen, Kaminsky, Mitzenmacher (2014)
*)

(* Configuration *)
let bucket_size = 4        (* entries per bucket *)
let max_kicks = 500        (* max relocations before giving up *)
let fingerprint_bits = 8   (* bits per fingerprint *)

(* Simple hash functions *)
let hash_string s =
  let h = ref 0 in
  String.iter (fun c -> h := !h * 31 + Char.code c) s;
  abs !h

let fingerprint s =
  let h = hash_string s in
  let fp = (h lsr 16) land ((1 lsl fingerprint_bits) - 1) in
  if fp = 0 then 1 else fp  (* fingerprint must be non-zero *)

let hash_fingerprint fp =
  abs (fp * 0x5bd1e995)

(* Cuckoo filter type *)
type t = {
  buckets: int array array;  (* buckets.(i).(j) = fingerprint or 0 *)
  num_buckets: int;
  mutable count: int;
}

(* Create a new cuckoo filter with given capacity *)
let create capacity =
  let num_buckets = max 1 (capacity / bucket_size) in
  let buckets = Array.init num_buckets (fun _ -> Array.make bucket_size 0) in
  { buckets; num_buckets; count = 0 }

(* Get the two candidate bucket indices for an item *)
let bucket_indices filter item =
  let fp = fingerprint item in
  let i1 = (hash_string item) mod filter.num_buckets in
  let i2 = (i1 lxor (hash_fingerprint fp mod filter.num_buckets)) mod filter.num_buckets in
  let i2 = if i2 < 0 then i2 + filter.num_buckets else i2 in
  (fp, abs i1, abs i2)

(* Try to insert a fingerprint into a specific bucket *)
let insert_into_bucket bucket fp =
  let found = ref false in
  for j = 0 to bucket_size - 1 do
    if not !found && bucket.(j) = 0 then begin
      bucket.(j) <- fp;
      found := true
    end
  done;
  !found

(* Insert an item into the filter *)
let insert filter item =
  let (fp, i1, i2) = bucket_indices filter item in
  (* Try bucket i1 *)
  if insert_into_bucket filter.buckets.(i1) fp then begin
    filter.count <- filter.count + 1;
    true
  end
  (* Try bucket i2 *)
  else if insert_into_bucket filter.buckets.(i2) fp then begin
    filter.count <- filter.count + 1;
    true
  end
  (* Both full — start kicking *)
  else begin
    let current_fp = ref fp in
    let current_i = ref (if Random.bool () then i1 else i2) in
    let success = ref false in
    let kicks = ref 0 in
    while !kicks < max_kicks && not !success do
      (* Pick random entry in bucket to evict *)
      let j = Random.int bucket_size in
      let evicted = filter.buckets.(!current_i).(j) in
      filter.buckets.(!current_i).(j) <- !current_fp;
      current_fp := evicted;
      (* Find alternate bucket for evicted fingerprint *)
      current_i := (!current_i lxor (hash_fingerprint evicted mod filter.num_buckets)) mod filter.num_buckets;
      if !current_i < 0 then current_i := !current_i + filter.num_buckets;
      current_i := abs !current_i;
      if insert_into_bucket filter.buckets.(!current_i) !current_fp then begin
        success := true;
        filter.count <- filter.count + 1
      end;
      incr kicks
    done;
    !success
  end

(* Check if an item might be in the filter *)
let lookup filter item =
  let (fp, i1, i2) = bucket_indices filter item in
  let check_bucket bucket =
    let found = ref false in
    for j = 0 to bucket_size - 1 do
      if bucket.(j) = fp then found := true
    done;
    !found
  in
  check_bucket filter.buckets.(i1) || check_bucket filter.buckets.(i2)

(* Delete an item from the filter *)
let delete filter item =
  let (fp, i1, i2) = bucket_indices filter item in
  let delete_from_bucket bucket =
    let found = ref false in
    for j = 0 to bucket_size - 1 do
      if not !found && bucket.(j) = fp then begin
        bucket.(j) <- 0;
        found := true;
        filter.count <- filter.count - 1
      end
    done;
    !found
  in
  delete_from_bucket filter.buckets.(i1) || delete_from_bucket filter.buckets.(i2)

(* Get current item count *)
let size filter = filter.count

(* Get load factor *)
let load_factor filter =
  float_of_int filter.count /. float_of_int (filter.num_buckets * bucket_size)

(* Get bucket utilization info *)
let stats filter =
  let empty = ref 0 in
  let total_slots = filter.num_buckets * bucket_size in
  Array.iter (fun bucket ->
    Array.iter (fun fp -> if fp = 0 then incr empty) bucket
  ) filter.buckets;
  let used = total_slots - !empty in
  Printf.sprintf "Cuckoo Filter Stats:\n  Buckets: %d\n  Bucket size: %d\n  Total slots: %d\n  Used slots: %d\n  Items: %d\n  Load factor: %.2f%%"
    filter.num_buckets bucket_size total_slots used filter.count
    (load_factor filter *. 100.0)

(* Demo *)
let () =
  Printf.printf "=== Cuckoo Filter Demo ===\n\n";

  (* Create a filter *)
  let cf = create 1000 in
  Printf.printf "Created cuckoo filter (capacity ~1000)\n\n";

  (* Insert some items *)
  let words = [| "apple"; "banana"; "cherry"; "date"; "elderberry";
                 "fig"; "grape"; "honeydew"; "kiwi"; "lemon";
                 "mango"; "nectarine"; "orange"; "papaya"; "quince" |] in

  Printf.printf "Inserting %d items...\n" (Array.length words);
  Array.iter (fun w ->
    let ok = insert cf w in
    Printf.printf "  insert(%s) -> %s\n" w (if ok then "ok" else "FAILED")
  ) words;

  Printf.printf "\nLookup tests:\n";
  Array.iter (fun w ->
    Printf.printf "  lookup(%s) -> %b\n" w (lookup cf w)
  ) words;

  (* Test non-members *)
  let non_members = [| "avocado"; "blueberry"; "coconut"; "dragonfruit" |] in
  Printf.printf "\nNon-member lookups (may have false positives):\n";
  Array.iter (fun w ->
    Printf.printf "  lookup(%s) -> %b\n" w (lookup cf w)
  ) non_members;

  (* Demonstrate deletion — the killer feature over Bloom filters *)
  Printf.printf "\n--- Deletion Demo (Bloom filters can't do this!) ---\n";
  Printf.printf "Before delete: lookup(banana) -> %b\n" (lookup cf "banana");
  let deleted = delete cf "banana" in
  Printf.printf "delete(banana) -> %s\n" (if deleted then "ok" else "not found");
  Printf.printf "After delete: lookup(banana) -> %b\n" (lookup cf "banana");

  (* Stats *)
  Printf.printf "\n%s\n" (stats cf);

  (* False positive rate test *)
  Printf.printf "\n--- False Positive Rate Test ---\n";
  let test_cf = create 10000 in
  let inserted = ref 0 in
  for i = 0 to 999 do
    if insert test_cf (Printf.sprintf "item_%d" i) then incr inserted
  done;
  Printf.printf "Inserted %d items\n" !inserted;
  let false_pos = ref 0 in
  let test_count = 10000 in
  for i = 0 to test_count - 1 do
    if lookup test_cf (Printf.sprintf "nonexistent_%d" i) then incr false_pos
  done;
  Printf.printf "False positives: %d / %d (%.2f%%)\n"
    !false_pos test_count
    (float_of_int !false_pos /. float_of_int test_count *. 100.0);

  Printf.printf "\nDone!\n"
