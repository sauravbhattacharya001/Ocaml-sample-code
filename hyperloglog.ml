(* HyperLogLog — Probabilistic Cardinality Estimator
 *
 * A space-efficient probabilistic data structure for estimating the number
 * of distinct elements (cardinality) in a multiset. Uses only O(m) space
 * where m is the number of registers, while providing estimates within
 * a few percent of the true cardinality.
 *
 * Key operations:
 * - add: O(1) — add an element
 * - cardinality: O(m) — estimate distinct count
 * - merge: O(m) — combine two sketches (union)
 *
 * Features:
 * - Configurable precision (4-16 bits → 16-65536 registers)
 * - Small/large range bias corrections
 * - Merge support for distributed counting
 * - Intersection estimation via inclusion-exclusion
 * - Jaccard similarity estimation
 * - Serialization/deserialization
 * - Memory usage reporting
 *
 * Usage:
 *   let hll = HyperLogLog.create ~precision:14 () in
 *   let hll = HyperLogLog.add hll "hello" in
 *   let hll = HyperLogLog.add hll "world" in
 *   let count = HyperLogLog.cardinality hll in
 *   Printf.printf "Estimated distinct elements: %.0f\n" count
 *)

module HyperLogLog : sig
  type t

  val create : ?precision:int -> unit -> t
  (** Create a new HyperLogLog with given precision (4-16, default 14).
      Higher precision = more accuracy but more memory. *)

  val add : t -> string -> t
  (** Add an element to the sketch. *)

  val add_hash : t -> int -> t
  (** Add a pre-hashed value directly. *)

  val cardinality : t -> float
  (** Estimate the number of distinct elements. *)

  val merge : t -> t -> t
  (** Merge two HyperLogLog sketches (union). Both must have same precision. *)

  val intersection_cardinality : t -> t -> float
  (** Estimate cardinality of the intersection using inclusion-exclusion. *)

  val jaccard : t -> t -> float
  (** Estimate Jaccard similarity |A∩B|/|A∪B|. *)

  val precision : t -> int
  (** Return the precision parameter. *)

  val num_registers : t -> int
  (** Return the number of registers. *)

  val memory_bytes : t -> int
  (** Approximate memory usage in bytes. *)

  val is_empty : t -> bool
  (** Check if no elements have been added. *)

  val serialize : t -> string
  (** Serialize to a string representation. *)

  val deserialize : string -> t
  (** Deserialize from a string representation. *)

  val relative_error : t -> float
  (** Theoretical relative standard error for this precision. *)

  val to_string : t -> string
  (** Human-readable summary. *)
end = struct
  type t = {
    precision : int;      (* p: number of bits for register index *)
    num_registers : int;  (* m = 2^p *)
    registers : int array; (* max leading zeros seen per bucket *)
    alpha : float;        (* bias correction constant *)
  }

  (* MurmurHash3-inspired hash for strings *)
  let hash_string s =
    let h = ref 0x811c9dc5 in
    String.iter (fun c ->
      h := !h lxor (Char.code c);
      h := !h * 0x01000193;
      h := !h land 0x3FFFFFFF  (* keep positive in OCaml *)
    ) s;
    (* avalanche *)
    h := !h lxor (!h lsr 16);
    h := !h * 0x45d9f3b;
    h := !h land 0x3FFFFFFF;
    h := !h lxor (!h lsr 13);
    h := !h * 0x45d9f3b;
    h := !h land 0x3FFFFFFF;
    h := !h lxor (!h lsr 16);
    !h land 0x3FFFFFFF

  (* secondary hash for more bits *)
  let hash_string2 s =
    let h = ref 0x5bd1e995 in
    String.iter (fun c ->
      h := !h lxor (Char.code c * 0x100);
      h := !h * 0x5bd1e995;
      h := !h land 0x3FFFFFFF
    ) s;
    h := !h lxor (!h lsr 13);
    h := !h * 0x5bd1e995;
    h := !h land 0x3FFFFFFF;
    h := !h lxor (!h lsr 15);
    !h land 0x3FFFFFFF

  (* Combine two hashes for 60 usable bits *)
  let full_hash s =
    let h1 = hash_string s in
    let h2 = hash_string2 s in
    (h1, h2)

  (* Compute alpha_m correction constant *)
  let compute_alpha m =
    match m with
    | 16 -> 0.673
    | 32 -> 0.697
    | 64 -> 0.709
    | _ -> 0.7213 /. (1.0 +. 1.079 /. float_of_int m)

  let create ?(precision=14) () =
    if precision < 4 || precision > 16 then
      failwith (Printf.sprintf "HyperLogLog: precision must be 4-16, got %d" precision);
    let num_registers = 1 lsl precision in
    {
      precision;
      num_registers;
      registers = Array.make num_registers 0;
      alpha = compute_alpha num_registers;
    }

  (* Count leading zeros in the remaining bits after extracting register index *)
  let count_leading_zeros ~bits_available value =
    let rec count v pos =
      if pos >= bits_available then bits_available
      else if v land (1 lsl (bits_available - 1 - pos)) <> 0 then pos + 1
      else count v (pos + 1)
    in
    count value 0

  let add_hash hll hash_val =
    let idx = hash_val land (hll.num_registers - 1) in
    let w = hash_val lsr hll.precision in
    let bits_remaining = 30 - hll.precision in
    let rho = count_leading_zeros ~bits_available:bits_remaining w in
    let new_registers = Array.copy hll.registers in
    if rho > new_registers.(idx) then
      new_registers.(idx) <- rho;
    { hll with registers = new_registers }

  let add hll element =
    let (h1, h2) = full_hash element in
    (* Use both hashes for better distribution *)
    let combined = h1 lxor (h2 lsl 3) in
    let combined = combined land 0x3FFFFFFF in
    add_hash hll combined

  let cardinality hll =
    let m = float_of_int hll.num_registers in
    (* Raw harmonic mean estimate *)
    let sum = Array.fold_left (fun acc r ->
      acc +. (2.0 ** (float_of_int (-r)))
    ) 0.0 hll.registers in
    let estimate = hll.alpha *. m *. m /. sum in

    (* Small range correction: use linear counting if estimate is small *)
    if estimate <= 2.5 *. m then begin
      let zeros = Array.fold_left (fun acc r ->
        if r = 0 then acc + 1 else acc
      ) 0 hll.registers in
      if zeros > 0 then
        m *. log (m /. float_of_int zeros)
      else
        estimate
    end
    (* Large range correction for 32-bit hash *)
    else if estimate > 1073741824.0 (* 2^30 *) then
      -1073741824.0 *. log (1.0 -. estimate /. 1073741824.0)
    else
      estimate

  let merge hll1 hll2 =
    if hll1.precision <> hll2.precision then
      failwith "HyperLogLog.merge: precision mismatch";
    let new_registers = Array.init hll1.num_registers (fun i ->
      max hll1.registers.(i) hll2.registers.(i)
    ) in
    { hll1 with registers = new_registers }

  let intersection_cardinality hll1 hll2 =
    let card_a = cardinality hll1 in
    let card_b = cardinality hll2 in
    let union = merge hll1 hll2 in
    let card_union = cardinality union in
    (* Inclusion-exclusion: |A∩B| = |A| + |B| - |A∪B| *)
    let result = card_a +. card_b -. card_union in
    max 0.0 result

  let jaccard hll1 hll2 =
    let union = merge hll1 hll2 in
    let card_union = cardinality union in
    if card_union = 0.0 then 0.0
    else
      let inter = intersection_cardinality hll1 hll2 in
      inter /. card_union

  let precision hll = hll.precision
  let num_registers hll = hll.num_registers
  let memory_bytes hll = hll.num_registers (* 1 byte per register in practice *)

  let is_empty hll =
    Array.for_all (fun r -> r = 0) hll.registers

  let serialize hll =
    let buf = Buffer.create (hll.num_registers + 10) in
    Buffer.add_string buf (Printf.sprintf "HLL:%d:" hll.precision);
    Array.iter (fun r ->
      Buffer.add_char buf (Char.chr (min r 255))
    ) hll.registers;
    Buffer.contents buf

  let deserialize s =
    if String.length s < 6 || String.sub s 0 4 <> "HLL:" then
      failwith "HyperLogLog.deserialize: invalid format";
    (* Find second colon *)
    let colon2 = String.index_from s 4 ':' in
    let precision = int_of_string (String.sub s 4 (colon2 - 4)) in
    let num_registers = 1 lsl precision in
    let data_start = colon2 + 1 in
    if String.length s - data_start <> num_registers then
      failwith "HyperLogLog.deserialize: size mismatch";
    let registers = Array.init num_registers (fun i ->
      Char.code s.[data_start + i]
    ) in
    {
      precision;
      num_registers;
      registers;
      alpha = compute_alpha num_registers;
    }

  let relative_error hll =
    1.04 /. sqrt (float_of_int hll.num_registers)

  let to_string hll =
    let card = cardinality hll in
    Printf.sprintf "HyperLogLog(p=%d, m=%d, est=%.0f, err=±%.2f%%)"
      hll.precision hll.num_registers card
      (relative_error hll *. 100.0)
end

(* ── Demo ───────────────────────────────────────────────────────────── *)

let () =
  Printf.printf "=== HyperLogLog — Probabilistic Cardinality Estimator ===\n\n";

  (* Basic usage *)
  Printf.printf "── Basic Cardinality Estimation ──\n";
  let hll = HyperLogLog.create ~precision:14 () in
  Printf.printf "Empty: %s\n" (HyperLogLog.to_string hll);

  (* Add known number of distinct elements *)
  let hll = ref hll in
  let n = 10000 in
  for i = 0 to n - 1 do
    hll := HyperLogLog.add !hll (string_of_int i)
  done;
  let est = HyperLogLog.cardinality !hll in
  Printf.printf "Added %d distinct elements\n" n;
  Printf.printf "Estimated: %.0f (error: %.2f%%)\n"
    est (abs_float (est -. float_of_int n) /. float_of_int n *. 100.0);
  Printf.printf "Theoretical relative error: ±%.2f%%\n"
    (HyperLogLog.relative_error !hll *. 100.0);
  Printf.printf "\n";

  (* Duplicates don't increase count *)
  Printf.printf "── Duplicate Handling ──\n";
  let hll_dup = HyperLogLog.create ~precision:10 () in
  let hll_dup = ref hll_dup in
  for _ = 1 to 1000 do
    hll_dup := HyperLogLog.add !hll_dup "same-element"
  done;
  Printf.printf "Added 'same-element' 1000 times\n";
  Printf.printf "Estimated distinct: %.0f (expected ~1)\n"
    (HyperLogLog.cardinality !hll_dup);
  Printf.printf "\n";

  (* Merge / Union *)
  Printf.printf "── Merge (Union) ──\n";
  let a = ref (HyperLogLog.create ~precision:12 ()) in
  let b = ref (HyperLogLog.create ~precision:12 ()) in
  (* A = {0..4999}, B = {2500..7499} → overlap of 2500 *)
  for i = 0 to 4999 do
    a := HyperLogLog.add !a (Printf.sprintf "item-%d" i)
  done;
  for i = 2500 to 7499 do
    b := HyperLogLog.add !b (Printf.sprintf "item-%d" i)
  done;
  let union = HyperLogLog.merge !a !b in
  Printf.printf "|A| ≈ %.0f (true: 5000)\n" (HyperLogLog.cardinality !a);
  Printf.printf "|B| ≈ %.0f (true: 5000)\n" (HyperLogLog.cardinality !b);
  Printf.printf "|A∪B| ≈ %.0f (true: 7500)\n" (HyperLogLog.cardinality union);
  Printf.printf "|A∩B| ≈ %.0f (true: 2500)\n"
    (HyperLogLog.intersection_cardinality !a !b);
  Printf.printf "Jaccard(A,B) ≈ %.3f (true: %.3f)\n"
    (HyperLogLog.jaccard !a !b) (2500.0 /. 7500.0);
  Printf.printf "\n";

  (* Precision comparison *)
  Printf.printf "── Precision Comparison ──\n";
  Printf.printf "%-12s %-12s %-12s %-12s %-12s\n"
    "Precision" "Registers" "Memory" "Error" "Estimate";
  Printf.printf "%s\n" (String.make 60 '-');
  let true_count = 50000 in
  List.iter (fun p ->
    let h = ref (HyperLogLog.create ~precision:p ()) in
    for i = 0 to true_count - 1 do
      h := HyperLogLog.add !h (string_of_int i)
    done;
    let est = HyperLogLog.cardinality !h in
    Printf.printf "p=%-10d %-12d %-12d ±%-11.2f%.0f\n"
      p (HyperLogLog.num_registers !h)
      (HyperLogLog.memory_bytes !h)
      (HyperLogLog.relative_error !h *. 100.0)
      est
  ) [4; 8; 10; 12; 14; 16];
  Printf.printf "(True count: %d)\n\n" true_count;

  (* Serialization round-trip *)
  Printf.printf "── Serialization ──\n";
  let h = ref (HyperLogLog.create ~precision:8 ()) in
  for i = 0 to 999 do
    h := HyperLogLog.add !h (string_of_int i)
  done;
  let before = HyperLogLog.cardinality !h in
  let serialized = HyperLogLog.serialize !h in
  let h2 = HyperLogLog.deserialize serialized in
  let after = HyperLogLog.cardinality h2 in
  Printf.printf "Before serialize: %.0f\n" before;
  Printf.printf "After deserialize: %.0f\n" after;
  Printf.printf "Serialized size: %d bytes\n" (String.length serialized);
  Printf.printf "Match: %b\n\n" (before = after);

  (* Scaling behavior *)
  Printf.printf "── Scaling (p=14, 16384 registers) ──\n";
  Printf.printf "%-15s %-15s %-15s\n" "True Count" "Estimate" "Error%";
  Printf.printf "%s\n" (String.make 45 '-');
  let h = ref (HyperLogLog.create ~precision:14 ()) in
  let checkpoints = [100; 1000; 5000; 10000; 50000; 100000] in
  let i = ref 0 in
  List.iter (fun cp ->
    while !i < cp do
      h := HyperLogLog.add !h (string_of_int !i);
      incr i
    done;
    let est = HyperLogLog.cardinality !h in
    let err = abs_float (est -. float_of_int cp) /. float_of_int cp *. 100.0 in
    Printf.printf "%-15d %-15.0f %-15.2f\n" cp est err
  ) checkpoints;
  Printf.printf "\n";

  Printf.printf "Memory: %d bytes for up to millions of distinct items\n"
    (HyperLogLog.memory_bytes !h);
  Printf.printf "Done!\n"
