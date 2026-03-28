(*
 *  succinct_bitvector.ml
 *  OCaml Sample Code
 *
 *  Succinct Bit Vector — space-efficient data structure supporting
 *  constant-time rank and select queries on a bit sequence.
 *
 *  rank(i)   = number of 1-bits in positions 0..i-1
 *  select(k) = position of the k-th 1-bit (1-indexed)
 *
 *  Uses a two-level block structure for O(1) rank queries
 *  and binary search over rank for select queries.
 *
 *  Applications: compressed suffix arrays, FM-index, wavelet trees,
 *  succinct trees, and any space-constrained indexing problem.
 *)

(* ── Bit Vector Construction ──────────────────────────────────── *)

let block_size = 64  (* bits per small block *)
let super_block_size = 256  (* bits per super block = 4 small blocks *)

type bitvector = {
  bits: int array;          (* raw bit storage, 64 bits per int *)
  length: int;              (* total number of bits *)
  super_ranks: int array;   (* cumulative popcount at each super block boundary *)
  block_ranks: int array;   (* cumulative popcount within super block *)
  ones_count: int;          (* total number of 1-bits *)
}

let popcount x =
  (* Kernighan's bit counting *)
  let x = ref x in
  let count = ref 0 in
  while !x <> 0 do
    x := !x land (!x - 1);
    incr count
  done;
  !count

let popcount_range bits lo hi =
  (* Count 1-bits in bit positions lo..hi-1 *)
  let count = ref 0 in
  for i = lo to hi - 1 do
    let word = i / 63 in  (* use 63 bits per int to avoid sign bit issues *)
    let bit = i mod 63 in
    if word < Array.length bits && (bits.(word) lsr bit) land 1 = 1 then
      incr count
  done;
  !count

let create_from_array arr =
  let n = Array.length arr in
  (* Pack bits into ints, 63 bits each to avoid sign issues *)
  let bits_per_word = 63 in
  let num_words = (n + bits_per_word - 1) / bits_per_word in
  let bits = Array.make num_words 0 in
  let total_ones = ref 0 in
  for i = 0 to n - 1 do
    if arr.(i) then begin
      let word = i / bits_per_word in
      let bit = i mod bits_per_word in
      bits.(word) <- bits.(word) lor (1 lsl bit);
      incr total_ones
    end
  done;
  (* Build rank index *)
  let num_super = (n + super_block_size - 1) / super_block_size + 1 in
  let num_blocks = (n + block_size - 1) / block_size + 1 in
  let super_ranks = Array.make num_super 0 in
  let block_ranks = Array.make num_blocks 0 in
  let cumulative = ref 0 in
  for i = 0 to n - 1 do
    if i mod super_block_size = 0 then
      super_ranks.(i / super_block_size) <- !cumulative;
    if i mod block_size = 0 then
      block_ranks.(i / block_size) <- !cumulative - super_ranks.(i / super_block_size);
    let word = i / bits_per_word in
    let bit = i mod bits_per_word in
    if (bits.(word) lsr bit) land 1 = 1 then
      incr cumulative
  done;
  (* Fill final entries *)
  let last_super = n / super_block_size in
  if last_super < num_super then
    super_ranks.(last_super) <- (if n mod super_block_size = 0 then !cumulative
                                  else super_ranks.(last_super));
  { bits; length = n; super_ranks; block_ranks; ones_count = !total_ones }

let create_from_list lst =
  create_from_array (Array.of_list lst)

let create_from_string s =
  let arr = Array.init (String.length s) (fun i -> s.[i] = '1') in
  create_from_array arr

(* ── Bit Access ───────────────────────────────────────────────── *)

let get bv i =
  if i < 0 || i >= bv.length then
    invalid_arg (Printf.sprintf "succinct_bitvector: index %d out of bounds [0, %d)" i bv.length);
  let bits_per_word = 63 in
  let word = i / bits_per_word in
  let bit = i mod bits_per_word in
  (bv.bits.(word) lsr bit) land 1 = 1

(* ── Rank ─────────────────────────────────────────────────────── *)

(* rank1(i) = number of 1-bits in positions 0..i-1 *)
let rank1 bv i =
  if i <= 0 then 0
  else if i >= bv.length then bv.ones_count
  else begin
    let si = i / super_block_size in
    let bi = i / block_size in
    let base = bv.super_ranks.(si) + bv.block_ranks.(bi) in
    let start = bi * block_size in
    (* Count remaining bits from block start to i *)
    let extra = ref 0 in
    let bits_per_word = 63 in
    for j = start to i - 1 do
      let word = j / bits_per_word in
      let bit = j mod bits_per_word in
      if (bv.bits.(word) lsr bit) land 1 = 1 then
        incr extra
    done;
    base + !extra
  end

(* rank0(i) = number of 0-bits in positions 0..i-1 *)
let rank0 bv i = i - rank1 bv i

(* ── Select ───────────────────────────────────────────────────── *)

(* select1(k) = position of the k-th 1-bit (1-indexed) *)
(* Uses binary search over rank *)
let select1 bv k =
  if k <= 0 || k > bv.ones_count then
    None
  else begin
    let lo = ref 0 in
    let hi = ref (bv.length) in
    while !lo < !hi do
      let mid = !lo + (!hi - !lo) / 2 in
      if rank1 bv (mid + 1) < k then
        lo := mid + 1
      else
        hi := mid
    done;
    if !lo < bv.length && get bv !lo && rank1 bv (!lo + 1) = k then
      Some !lo
    else
      None
  end

(* select0(k) = position of the k-th 0-bit (1-indexed) *)
let select0 bv k =
  let zeros = bv.length - bv.ones_count in
  if k <= 0 || k > zeros then
    None
  else begin
    let lo = ref 0 in
    let hi = ref (bv.length) in
    while !lo < !hi do
      let mid = !lo + (!hi - !lo) / 2 in
      if rank0 bv (mid + 1) < k then
        lo := mid + 1
      else
        hi := mid
    done;
    if !lo < bv.length && not (get bv !lo) && rank0 bv (!lo + 1) = k then
      Some !lo
    else
      None
  end

(* ── Utilities ────────────────────────────────────────────────── *)

let length bv = bv.length
let count_ones bv = bv.ones_count
let count_zeros bv = bv.length - bv.ones_count

let to_string bv =
  String.init bv.length (fun i -> if get bv i then '1' else '0')

let density bv =
  if bv.length = 0 then 0.0
  else float_of_int bv.ones_count /. float_of_int bv.length

(* ── Demo ─────────────────────────────────────────────────────── *)

let () =
  Printf.printf "=== Succinct Bit Vector Demo ===\n\n";

  (* Create from string *)
  let bv = create_from_string "1011010011101001" in
  Printf.printf "Bit vector: %s\n" (to_string bv);
  Printf.printf "Length: %d, Ones: %d, Zeros: %d\n" (length bv) (count_ones bv) (count_zeros bv);
  Printf.printf "Density: %.2f%%\n\n" (density bv *. 100.0);

  (* Rank queries *)
  Printf.printf "--- Rank Queries ---\n";
  for i = 0 to length bv do
    Printf.printf "  rank1(%2d) = %d    rank0(%2d) = %d\n" i (rank1 bv i) i (rank0 bv i)
  done;
  Printf.printf "\n";

  (* Select queries *)
  Printf.printf "--- Select Queries ---\n";
  let ones = count_ones bv in
  for k = 1 to ones do
    match select1 bv k with
    | Some pos -> Printf.printf "  select1(%d) = %d\n" k pos
    | None -> Printf.printf "  select1(%d) = not found\n" k
  done;
  Printf.printf "\n";

  let zeros = count_zeros bv in
  for k = 1 to zeros do
    match select0 bv k with
    | Some pos -> Printf.printf "  select0(%d) = %d\n" k pos
    | None -> Printf.printf "  select0(%d) = not found\n" k
  done;
  Printf.printf "\n";

  (* Larger example *)
  Printf.printf "--- Larger Example (100 bits) ---\n";
  let large = create_from_array (Array.init 100 (fun i -> i mod 3 = 0 || i mod 7 = 0)) in
  Printf.printf "Length: %d, Ones: %d, Density: %.1f%%\n"
    (length large) (count_ones large) (density large *. 100.0);
  Printf.printf "rank1(50) = %d\n" (rank1 large 50);
  Printf.printf "rank0(50) = %d\n" (rank0 large 50);
  (match select1 large 10 with
   | Some p -> Printf.printf "select1(10) = %d\n" p
   | None -> Printf.printf "select1(10) = not found\n");
  (match select0 large 10 with
   | Some p -> Printf.printf "select0(10) = %d\n" p
   | None -> Printf.printf "select0(10) = not found\n");

  Printf.printf "\n--- Access Pattern ---\n";
  let bv2 = create_from_string "11001010" in
  Printf.printf "Bits: %s\n" (to_string bv2);
  for i = 0 to length bv2 - 1 do
    Printf.printf "  bv[%d] = %b\n" i (get bv2 i)
  done;

  Printf.printf "\nDone.\n"
