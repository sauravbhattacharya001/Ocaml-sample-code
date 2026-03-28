(* Wavelet Tree - A data structure for efficient rank, select, and access queries
   on sequences over an alphabet.

   A wavelet tree recursively partitions the alphabet into halves,
   storing a bitvector at each node indicating which half each element
   belongs to. This enables O(log σ) rank, select, and access queries
   where σ is the alphabet size.

   Applications:
   - Substring search and counting
   - Document retrieval
   - Compressed text indexing
   - Range quantile queries

   Time complexities (σ = alphabet size):
   - Build:    O(n log σ)
   - Access:   O(log σ)
   - Rank:     O(log σ)
   - Select:   O(log σ)
   - Quantile: O(log σ)
*)

(* Simple bitvector with rank/select support *)
module Bitvector = struct
  type t = {
    bits: bool array;
    rank_cache: int array;  (* prefix sum of 1s *)
  }

  let create bits =
    let n = Array.length bits in
    let rank_cache = Array.make (n + 1) 0 in
    for i = 0 to n - 1 do
      rank_cache.(i + 1) <- rank_cache.(i) + (if bits.(i) then 1 else 0)
    done;
    { bits; rank_cache }

  let length bv = Array.length bv.bits

  let access bv i = bv.bits.(i)

  (* rank1(i) = number of 1s in bits[0..i-1] *)
  let rank1 bv i = bv.rank_cache.(i)

  (* rank0(i) = number of 0s in bits[0..i-1] *)
  let rank0 bv i = i - rank1 bv i

  (* select1(j) = position of the j-th 1 (1-indexed), returns -1 if not found *)
  let select1 bv j =
    if j < 1 then -1
    else
      let n = length bv in
      let rec search i count =
        if i >= n then -1
        else if bv.bits.(i) then
          let count' = count + 1 in
          if count' = j then i else search (i + 1) count'
        else search (i + 1) count
      in
      search 0 0

  (* select0(j) = position of the j-th 0 (1-indexed), returns -1 if not found *)
  let select0 bv j =
    if j < 1 then -1
    else
      let n = length bv in
      let rec search i count =
        if i >= n then -1
        else if not bv.bits.(i) then
          let count' = count + 1 in
          if count' = j then i else search (i + 1) count'
        else search (i + 1) count
      in
      search 0 0
end

(* Wavelet tree node *)
type 'a node =
  | Leaf of { symbol: 'a }
  | Internal of {
      bv: Bitvector.t;
      left: 'a node;
      right: 'a node;
      lo: int;  (* alphabet range [lo, hi) mapped to indices *)
      hi: int;
    }

type 'a t = {
  root: 'a node;
  alphabet: 'a array;  (* sorted unique symbols *)
  symbol_to_idx: 'a -> int;
  n: int;  (* sequence length *)
}

(* Build a wavelet tree from a sequence *)
let build ~compare seq =
  let n = Array.length seq in
  (* Extract sorted unique alphabet *)
  let sorted = Array.copy seq in
  Array.sort compare sorted;
  let alphabet =
    if Array.length sorted = 0 then [||]
    else begin
      let uniq = Array.make (Array.length sorted) sorted.(0) in
      let k = ref 1 in
      for i = 1 to Array.length sorted - 1 do
        if compare sorted.(i) sorted.(i - 1) <> 0 then begin
          uniq.(!k) <- sorted.(i);
          incr k
        end
      done;
      Array.sub uniq 0 !k
    end
  in
  let sigma = Array.length alphabet in

  (* Map symbol to index in alphabet *)
  let symbol_to_idx sym =
    (* Binary search *)
    let lo = ref 0 and hi = ref (sigma - 1) in
    while !lo < !hi do
      let mid = (!lo + !hi) / 2 in
      if compare alphabet.(mid) sym < 0 then lo := mid + 1
      else hi := mid
    done;
    !lo
  in

  (* Recursive build: takes subsequence indices and alphabet range [lo, hi) *)
  let rec build_node indices lo hi =
    if hi - lo <= 1 then
      Leaf { symbol = alphabet.(lo) }
    else begin
      let mid = (lo + hi) / 2 in
      let len = Array.length indices in
      let bits = Array.init len (fun i ->
        symbol_to_idx indices.(i) >= mid
      ) in
      let bv = Bitvector.create bits in
      (* Partition indices into left (< mid) and right (>= mid) *)
      let left_indices = Array.of_list (
        Array.to_list indices |> List.filter (fun s -> symbol_to_idx s < mid)
      ) in
      let right_indices = Array.of_list (
        Array.to_list indices |> List.filter (fun s -> symbol_to_idx s >= mid)
      ) in
      let left = build_node left_indices lo mid in
      let right = build_node right_indices mid hi in
      Internal { bv; left; right; lo; hi }
    end
  in

  let root =
    if sigma = 0 then Leaf { symbol = seq.(0) }  (* degenerate *)
    else build_node seq 0 sigma
  in
  { root; alphabet; symbol_to_idx; n }

(* Access: retrieve the i-th element (0-indexed) *)
let access wt i =
  let rec go node i =
    match node with
    | Leaf { symbol; _ } -> symbol
    | Internal { bv; left; right; _ } ->
      if Bitvector.access bv i then
        (* Go right *)
        let i' = Bitvector.rank1 bv i in
        go right i'
      else
        (* Go left *)
        let i' = Bitvector.rank0 bv i in
        go left i'
  in
  go wt.root i

(* Rank: count occurrences of symbol in seq[0..i-1] *)
let rank wt symbol i =
  let idx = wt.symbol_to_idx symbol in
  let rec go node i lo hi =
    match node with
    | Leaf _ -> i
    | Internal { bv; left; right; _ } ->
      let mid = (lo + hi) / 2 in
      if idx < mid then
        let i' = Bitvector.rank0 bv i in
        go left i' lo mid
      else
        let i' = Bitvector.rank1 bv i in
        go right i' mid hi
  in
  go wt.root i 0 (Array.length wt.alphabet)

(* Select: find position of j-th occurrence of symbol (1-indexed) *)
let select wt symbol j =
  let idx = wt.symbol_to_idx symbol in
  (* We need to traverse down to the leaf, then back up *)
  (* First, collect the path *)
  let rec collect_path node lo hi =
    match node with
    | Leaf _ -> []
    | Internal { bv; left; right; _ } ->
      let mid = (lo + hi) / 2 in
      if idx < mid then
        (bv, false) :: collect_path left lo mid
      else
        (bv, true) :: collect_path right mid hi
  in
  let path = collect_path wt.root 0 (Array.length wt.alphabet) in
  (* Walk back up *)
  let rec walk_up path j =
    match path with
    | [] -> j  (* position in original sequence *)
    | (bv, went_right) :: rest ->
      let pos =
        if went_right then Bitvector.select1 bv j
        else Bitvector.select0 bv j
      in
      if pos = -1 then -1
      else walk_up rest (pos + 1)  (* select is 1-indexed for parent *)
  in
  let result = walk_up (List.rev path) j in
  if result < 1 then -1 else result - 1  (* convert to 0-indexed *)

(* Quantile: find the k-th smallest element in seq[lo..hi-1] (1-indexed k) *)
let quantile wt seq_lo seq_hi k =
  let rec go node lo hi mapped_lo mapped_hi k =
    match node with
    | Leaf { symbol; _ } -> symbol
    | Internal { bv; left; right; _ } ->
      let zeros_before = Bitvector.rank0 bv mapped_lo in
      let zeros_in_range = Bitvector.rank0 bv mapped_hi - zeros_before in
      if k <= zeros_in_range then
        (* k-th smallest is in the left subtree *)
        let new_lo = zeros_before in
        let new_hi = zeros_before + zeros_in_range in
        let mid = (lo + hi) / 2 in
        go left lo mid new_lo new_hi k
      else
        (* k-th smallest is in the right subtree *)
        let ones_before = Bitvector.rank1 bv mapped_lo in
        let ones_in_range = Bitvector.rank1 bv mapped_hi - ones_before in
        let _ = ones_in_range in
        let new_lo = ones_before in
        let new_hi = Bitvector.rank1 bv mapped_hi in
        let mid = (lo + hi) / 2 in
        go right mid hi new_lo new_hi (k - zeros_in_range)
  in
  go wt.root 0 (Array.length wt.alphabet) seq_lo seq_hi k

(* Range frequency: count occurrences of symbol in seq[lo..hi-1] *)
let range_count wt symbol lo hi =
  rank wt symbol hi - rank wt symbol lo

(* ============================================================ *)
(* Demo / Tests                                                  *)
(* ============================================================ *)

let () =
  Printf.printf "=== Wavelet Tree Demo ===\n\n";

  (* Example sequence *)
  let seq = [| 3; 1; 4; 1; 5; 9; 2; 6; 5; 3; 5; 8; 9; 7 |] in
  let n = Array.length seq in

  Printf.printf "Sequence: ";
  Array.iter (fun x -> Printf.printf "%d " x) seq;
  Printf.printf "\n\n";

  (* Build wavelet tree *)
  let wt = build ~compare:Int.compare seq in

  Printf.printf "Alphabet: ";
  Array.iter (fun x -> Printf.printf "%d " x) wt.alphabet;
  Printf.printf "\n";
  Printf.printf "Sequence length: %d\n\n" wt.n;

  (* Test access *)
  Printf.printf "--- Access queries ---\n";
  for i = 0 to n - 1 do
    let v = access wt i in
    let expected = seq.(i) in
    let ok = if v = expected then "OK" else "FAIL" in
    Printf.printf "  access(%d) = %d  [%s]\n" i v ok
  done;
  Printf.printf "\n";

  (* Test rank *)
  Printf.printf "--- Rank queries ---\n";
  let test_rank sym pos expected =
    let r = rank wt sym pos in
    let ok = if r = expected then "OK" else Printf.sprintf "FAIL (got %d)" r in
    Printf.printf "  rank(%d, %d) = %d  [%s]\n" sym pos expected ok
  in
  (* seq = [3;1;4;1;5;9;2;6;5;3;5;8;9;7] *)
  test_rank 1 0 0;   (* no 1s before position 0 *)
  test_rank 1 2 1;   (* one 1 in [0,2) *)
  test_rank 1 4 2;   (* two 1s in [0,4) *)
  test_rank 5 14 3;  (* three 5s total *)
  test_rank 9 14 2;  (* two 9s total *)
  test_rank 7 14 1;  (* one 7 total *)
  Printf.printf "\n";

  (* Test select *)
  Printf.printf "--- Select queries ---\n";
  let test_select sym j expected =
    let s = select wt sym j in
    let ok = if s = expected then "OK" else Printf.sprintf "FAIL (got %d)" s in
    Printf.printf "  select(%d, %d) = %d  [%s]\n" sym j expected ok
  in
  test_select 1 1 1;   (* first 1 is at position 1 *)
  test_select 1 2 3;   (* second 1 is at position 3 *)
  test_select 5 1 4;   (* first 5 is at position 4 *)
  test_select 5 2 8;   (* second 5 is at position 8 *)
  test_select 5 3 10;  (* third 5 is at position 10 *)
  test_select 9 1 5;   (* first 9 is at position 5 *)
  Printf.printf "\n";

  (* Test quantile *)
  Printf.printf "--- Quantile queries ---\n";
  Printf.printf "  (k-th smallest in range)\n";
  let test_quantile lo hi k expected =
    let q = quantile wt lo hi k in
    let ok = if q = expected then "OK" else Printf.sprintf "FAIL (got %d)" q in
    Printf.printf "  quantile([%d,%d), k=%d) = %d  [%s]\n" lo hi k expected ok
  in
  (* seq[0..4] = [3;1;4;1;5], sorted = [1;1;3;4;5] *)
  test_quantile 0 5 1 1;  (* smallest *)
  test_quantile 0 5 2 1;  (* 2nd smallest *)
  test_quantile 0 5 3 3;  (* 3rd smallest = median *)
  test_quantile 0 5 5 5;  (* largest *)
  Printf.printf "\n";

  (* Test range count *)
  Printf.printf "--- Range count queries ---\n";
  let test_range sym lo hi expected =
    let c = range_count wt sym lo hi in
    let ok = if c = expected then "OK" else Printf.sprintf "FAIL (got %d)" c in
    Printf.printf "  count(%d in [%d,%d)) = %d  [%s]\n" sym lo hi expected ok
  in
  test_range 5 0 14 3;   (* three 5s total *)
  test_range 5 0 5 1;    (* one 5 in first half *)
  test_range 1 0 4 2;    (* two 1s in [0,4) *)
  test_range 9 0 6 1;    (* one 9 in [0,6) *)
  Printf.printf "\n";

  (* String example *)
  Printf.printf "=== String Wavelet Tree ===\n\n";
  let str = "abracadabra" in
  let char_seq = Array.init (String.length str) (fun i -> Char.code str.[i]) in
  let cwt = build ~compare:Int.compare char_seq in

  Printf.printf "String: %s\n" str;
  Printf.printf "Alphabet: ";
  Array.iter (fun x -> Printf.printf "%c " (Char.chr x)) cwt.alphabet;
  Printf.printf "\n\n";

  let a = Char.code 'a' in
  let b = Char.code 'b' in
  let r = Char.code 'r' in

  Printf.printf "rank('a', 11) = %d  (expected 5)\n" (rank cwt a 11);
  Printf.printf "rank('b', 11) = %d  (expected 2)\n" (rank cwt b 11);
  Printf.printf "rank('r', 11) = %d  (expected 2)\n" (rank cwt r 11);
  Printf.printf "select('a', 3) = %d  (expected 4)\n" (select cwt a 3);
  Printf.printf "access(4) = '%c'  (expected 'c')\n" (Char.chr (access cwt 4));

  Printf.printf "\nAll tests complete!\n"
