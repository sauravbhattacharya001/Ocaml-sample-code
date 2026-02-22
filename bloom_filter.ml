(* bloom_filter.ml — Probabilistic Set Membership *)
(* A Bloom filter uses k hash functions over an m-bit array to test     *)
(* set membership with tunable false-positive rate. No false negatives. *)
(* Supports: create, add, mem, count, union, false_positive_rate,      *)
(* saturation, of_list, mem_all, mem_any, clear, copy, serialize.      *)
(* Immutable — all operations return new filters.                      *)

module BloomFilter = struct

  type t = {
    bits : bytes;     (* bit array stored as bytes *)
    m    : int;       (* total bits *)
    k    : int;       (* number of hash functions *)
    n    : int;       (* number of elements added *)
  }

  (* ---- Bit manipulation helpers ---- *)

  let get_bit bits i =
    let byte_idx = i / 8 in
    let bit_idx = i mod 8 in
    Char.code (Bytes.get bits byte_idx) land (1 lsl bit_idx) <> 0

  let set_bit bits i =
    let byte_idx = i / 8 in
    let bit_idx = i mod 8 in
    let old = Char.code (Bytes.get bits byte_idx) in
    Bytes.set bits byte_idx (Char.chr (old lor (1 lsl bit_idx)))

  (* ---- Hash functions ---- *)
  (* Double hashing: h_i(x) = (h1(x) + i * h2(x)) mod m *)
  (* Uses Hashtbl.hash with salt for h1, h2 *)

  let hash1 x = Hashtbl.hash x
  let hash2 x = Hashtbl.hash (x, 0x9e3779b9)

  let hash_i m h1 h2 i =
    ((h1 + i * h2) mod m + m) mod m

  (* ---- Core API ---- *)

  (** Create an empty Bloom filter.
      [m] = number of bits, [k] = number of hash functions. *)
  let create ?(m = 1024) ?(k = 7) () =
    let m = max 8 m in
    let k = max 1 k in
    let byte_count = (m + 7) / 8 in
    { bits = Bytes.make byte_count '\000'; m; k; n = 0 }

  (** Create a Bloom filter sized for expected element count and
      desired false-positive probability. *)
  let create_optimal ~expected_elements ~fp_rate =
    let n_f = float_of_int (max 1 expected_elements) in
    let p = max 0.0001 (min 0.5 fp_rate) in
    let m_f = -.(n_f *. log p) /. (log 2.0 ** 2.0) in
    let m = max 8 (int_of_float (ceil m_f)) in
    let k_f = (float_of_int m /. n_f) *. log 2.0 in
    let k = max 1 (int_of_float (Float.round k_f)) in
    create ~m ~k ()

  (** Add an element to the filter. Returns a new filter. *)
  let add x bf =
    let new_bits = Bytes.copy bf.bits in
    let h1 = hash1 x in
    let h2 = hash2 x in
    for i = 0 to bf.k - 1 do
      let idx = hash_i bf.m h1 h2 i in
      set_bit new_bits idx
    done;
    { bf with bits = new_bits; n = bf.n + 1 }

  (** Test if an element might be in the set.
      Returns true if possibly present, false if definitely absent. *)
  let mem x bf =
    let h1 = hash1 x in
    let h2 = hash2 x in
    let rec check i =
      if i >= bf.k then true
      else
        let idx = hash_i bf.m h1 h2 i in
        if get_bit bf.bits idx then check (i + 1)
        else false
    in
    check 0

  (** Number of elements added. *)
  let count bf = bf.n

  (** Number of bits in the filter. *)
  let size bf = bf.m

  (** Number of hash functions. *)
  let num_hashes bf = bf.k

  (** Count of set bits. *)
  let popcount bf =
    let c = ref 0 in
    for i = 0 to bf.m - 1 do
      if get_bit bf.bits i then incr c
    done;
    !c

  (** Saturation: fraction of bits that are set (0.0 to 1.0). *)
  let saturation bf =
    float_of_int (popcount bf) /. float_of_int bf.m

  (** Theoretical false-positive probability given current fill. *)
  let false_positive_rate bf =
    if bf.n = 0 then 0.0
    else
      let m_f = float_of_int bf.m in
      let k_f = float_of_int bf.k in
      let n_f = float_of_int bf.n in
      (1.0 -. exp (-. k_f *. n_f /. m_f)) ** k_f

  (** Is the filter empty (no elements added)? *)
  let is_empty bf = bf.n = 0

  (** Union of two filters (must have same m and k). *)
  let union bf1 bf2 =
    if bf1.m <> bf2.m || bf1.k <> bf2.k then
      invalid_arg "BloomFilter.union: incompatible filters"
    else begin
      let new_bits = Bytes.copy bf1.bits in
      let byte_count = (bf1.m + 7) / 8 in
      for i = 0 to byte_count - 1 do
        let b1 = Char.code (Bytes.get bf1.bits i) in
        let b2 = Char.code (Bytes.get bf2.bits i) in
        Bytes.set new_bits i (Char.chr (b1 lor b2))
      done;
      { bits = new_bits; m = bf1.m; k = bf1.k; n = bf1.n + bf2.n }
    end

  (** Create a filter from a list of elements. *)
  let of_list ?(m = 1024) ?(k = 7) lst =
    List.fold_left (fun bf x -> add x bf) (create ~m ~k ()) lst

  (** Test if all elements in a list might be present. *)
  let mem_all lst bf =
    List.for_all (fun x -> mem x bf) lst

  (** Test if any element in a list might be present. *)
  let mem_any lst bf =
    List.exists (fun x -> mem x bf) lst

  (** Create a cleared copy (same m and k, no elements). *)
  let clear bf = create ~m:bf.m ~k:bf.k ()

  (** Create a deep copy. *)
  let copy bf = { bf with bits = Bytes.copy bf.bits }

  (** Serialize to string (for debugging). *)
  let to_string bf =
    Printf.sprintf "BloomFilter(m=%d, k=%d, n=%d, saturation=%.2f%%)"
      bf.m bf.k bf.n (saturation bf *. 100.0)
end
