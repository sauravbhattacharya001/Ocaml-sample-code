(* Fenwick Tree (Binary Indexed Tree) — efficient prefix sums  *)
(* and point updates in O(log n) time with O(n) space.        *)
(* Supports: prefix sum, range sum, point update, point query, *)
(* order statistics (k-th smallest), lower/upper bound search. *)
(* Demonstrates: imperative arrays, bit manipulation, functors *)

(* ── Module signature for additive groups ─────────────────── *)

module type GROUP = sig
  type t
  val zero : t
  val add : t -> t -> t
  val sub : t -> t -> t
  val compare : t -> t -> int
  val to_string : t -> string
end

(* ── Integer group ────────────────────────────────────────── *)

module IntGroup : GROUP with type t = int = struct
  type t = int
  let zero = 0
  let add = ( + )
  let sub = ( - )
  let compare = Int.compare
  let to_string = string_of_int
end

(* ── Float group ──────────────────────────────────────────── *)

module FloatGroup : GROUP with type t = float = struct
  type t = float
  let zero = 0.0
  let add = ( +. )
  let sub = ( -. )
  let compare = Float.compare
  let to_string = string_of_float
end

(* ── Fenwick Tree functor ─────────────────────────────────── *)

module Make (G : GROUP) = struct

  type t = {
    tree : G.t array;   (* 1-indexed BIT *)
    n : int;
  }

  (* ── Bit manipulation helpers ───────────────────────────── *)

  (* Lowest set bit: isolates rightmost 1-bit *)
  let lowbit i = i land (-i)

  (* ── Construction ───────────────────────────────────────── *)

  (* Create an empty Fenwick tree of size n *)
  let create n =
    { tree = Array.make (n + 1) G.zero; n }

  (* Build from a list in O(n) time using the "running update" trick *)
  let of_list lst =
    let arr = Array.of_list lst in
    let n = Array.length arr in
    let tree = Array.make (n + 1) G.zero in
    (* Copy values to 1-indexed positions *)
    for i = 0 to n - 1 do
      tree.(i + 1) <- arr.(i)
    done;
    (* Propagate contributions upward *)
    for i = 1 to n do
      let parent = i + lowbit i in
      if parent <= n then
        tree.(parent) <- G.add tree.(parent) tree.(i)
    done;
    { tree; n }

  (* ── Point update ───────────────────────────────────────── *)

  (* Add delta to position i (0-indexed) *)
  let update ft i delta =
    let j = ref (i + 1) in
    while !j <= ft.n do
      ft.tree.(!j) <- G.add ft.tree.(!j) delta;
      j := !j + lowbit !j
    done

  (* ── Prefix sum query ───────────────────────────────────── *)

  (* Sum of elements in [0, i] (0-indexed, inclusive) *)
  let prefix_sum ft i =
    let s = ref G.zero in
    let j = ref (i + 1) in  (* convert to 1-indexed *)
    while !j > 0 do
      s := G.add !s ft.tree.(!j);
      j := !j - lowbit !j
    done;
    !s

  (* ── Range sum query ────────────────────────────────────── *)

  (* Sum of elements in [l, r] (0-indexed, inclusive) *)
  let range_sum ft l r =
    if l > r then G.zero
    else if l = 0 then prefix_sum ft r
    else G.sub (prefix_sum ft r) (prefix_sum ft (l - 1))

  (* ── Point query ────────────────────────────────────────── *)

  (* Get the value at position i (0-indexed) *)
  let query_point ft i =
    if i = 0 then prefix_sum ft 0
    else G.sub (prefix_sum ft i) (prefix_sum ft (i - 1))

  (* ── Set value at position ──────────────────────────────── *)

  let set ft i v =
    let old = query_point ft i in
    let diff = G.sub v old in
    update ft i diff

  (* ── Find k-th smallest (order statistic) ───────────────── *)
  (* Requires all values to be non-negative frequencies.       *)
  (* Returns 0-indexed position where cumulative freq >= k.    *)

  let find_kth ft k =
    let pos = ref 0 in
    let remaining = ref k in
    (* Find highest power of 2 <= n *)
    let bit_mask = ref 1 in
    while !bit_mask <= ft.n do
      bit_mask := !bit_mask lsl 1
    done;
    bit_mask := !bit_mask lsr 1;
    while !bit_mask > 0 do
      let next = !pos + !bit_mask in
      if next <= ft.n && G.compare ft.tree.(next) !remaining < 0 then begin
        pos := next;
        remaining := G.sub !remaining ft.tree.(next)
      end;
      bit_mask := !bit_mask lsr 1
    done;
    !pos  (* 0-indexed result *)

  (* ── Utility ────────────────────────────────────────────── *)

  let size ft = ft.n

  (* Convert to list of prefix sums *)
  let to_prefix_sums ft =
    List.init ft.n (fun i -> prefix_sum ft i)

  (* Convert back to original values *)
  let to_list ft =
    List.init ft.n (fun i -> query_point ft i)

  (* Pretty-print *)
  let to_string ft =
    let vals = to_list ft in
    let strs = List.map G.to_string vals in
    "[" ^ String.concat "; " strs ^ "]"

end

(* ══════════════════════════════════════════════════════════ *)
(*  Concrete instances                                       *)
(* ══════════════════════════════════════════════════════════ *)

module IntFenwick = Make(IntGroup)
module FloatFenwick = Make(FloatGroup)

(* ══════════════════════════════════════════════════════════ *)
(*  Tests                                                    *)
(* ══════════════════════════════════════════════════════════ *)

let () =
  let passed = ref 0 in
  let failed = ref 0 in
  let assert_eq name expected actual =
    if expected = actual then (
      incr passed;
      Printf.printf "  ✓ %s\n" name
    ) else (
      incr failed;
      Printf.printf "  ✗ %s (expected %s, got %s)\n" name expected actual
    )
  in
  let assert_int name expected actual =
    assert_eq name (string_of_int expected) (string_of_int actual)
  in
  let assert_float_close name expected actual eps =
    if Float.abs (expected -. actual) < eps then (
      incr passed;
      Printf.printf "  ✓ %s\n" name
    ) else (
      incr failed;
      Printf.printf "  ✗ %s (expected %f, got %f)\n" name expected actual
    )
  in

  Printf.printf "\n══════ Fenwick Tree (Binary Indexed Tree) Tests ══════\n\n";

  (* ── Basic construction and prefix sums ─────────────────── *)
  Printf.printf "── Construction & Prefix Sums ──\n";
  let ft = IntFenwick.of_list [1; 3; 5; 7; 9; 11] in
  assert_int "size" 6 (IntFenwick.size ft);
  assert_int "prefix_sum(0)" 1 (IntFenwick.prefix_sum ft 0);
  assert_int "prefix_sum(1)" 4 (IntFenwick.prefix_sum ft 1);
  assert_int "prefix_sum(2)" 9 (IntFenwick.prefix_sum ft 2);
  assert_int "prefix_sum(3)" 16 (IntFenwick.prefix_sum ft 3);
  assert_int "prefix_sum(4)" 25 (IntFenwick.prefix_sum ft 4);
  assert_int "prefix_sum(5)" 36 (IntFenwick.prefix_sum ft 5);

  (* ── Range sum queries ──────────────────────────────────── *)
  Printf.printf "── Range Sum Queries ──\n";
  assert_int "range_sum(0,5)" 36 (IntFenwick.range_sum ft 0 5);
  assert_int "range_sum(1,3)" 15 (IntFenwick.range_sum ft 1 3);
  assert_int "range_sum(2,4)" 21 (IntFenwick.range_sum ft 2 4);
  assert_int "range_sum(0,0)" 1 (IntFenwick.range_sum ft 0 0);
  assert_int "range_sum(5,5)" 11 (IntFenwick.range_sum ft 5 5);
  assert_int "range_sum(3,1) empty" 0 (IntFenwick.range_sum ft 3 1);

  (* ── Point queries ──────────────────────────────────────── *)
  Printf.printf "── Point Queries ──\n";
  assert_int "query_point(0)" 1 (IntFenwick.query_point ft 0);
  assert_int "query_point(1)" 3 (IntFenwick.query_point ft 1);
  assert_int "query_point(3)" 7 (IntFenwick.query_point ft 3);
  assert_int "query_point(5)" 11 (IntFenwick.query_point ft 5);

  (* ── Point updates ──────────────────────────────────────── *)
  Printf.printf "── Point Updates ──\n";
  IntFenwick.update ft 2 10;  (* 5 -> 15 *)
  assert_int "after update: query_point(2)" 15 (IntFenwick.query_point ft 2);
  assert_int "after update: prefix_sum(2)" 19 (IntFenwick.prefix_sum ft 2);
  assert_int "after update: range_sum(0,5)" 46 (IntFenwick.range_sum ft 0 5);
  (* Other values unchanged *)
  assert_int "after update: query_point(0)" 1 (IntFenwick.query_point ft 0);
  assert_int "after update: query_point(1)" 3 (IntFenwick.query_point ft 1);

  (* ── Set value ──────────────────────────────────────────── *)
  Printf.printf "── Set Value ──\n";
  IntFenwick.set ft 2 5;  (* back to 5 *)
  assert_int "after set: query_point(2)" 5 (IntFenwick.query_point ft 2);
  assert_int "after set: prefix_sum(5)" 36 (IntFenwick.prefix_sum ft 5);

  (* ── Empty tree ─────────────────────────────────────────── *)
  Printf.printf "── Empty Tree ──\n";
  let empty = IntFenwick.create 0 in
  assert_int "empty size" 0 (IntFenwick.size empty);

  (* ── Single element ─────────────────────────────────────── *)
  Printf.printf "── Single Element ──\n";
  let single = IntFenwick.of_list [42] in
  assert_int "single prefix_sum(0)" 42 (IntFenwick.prefix_sum single 0);
  assert_int "single query_point(0)" 42 (IntFenwick.query_point single 0);
  IntFenwick.update single 0 8;
  assert_int "single after update" 50 (IntFenwick.query_point single 0);

  (* ── Large array ────────────────────────────────────────── *)
  Printf.printf "── Large Array ──\n";
  let big = IntFenwick.of_list (List.init 1000 (fun i -> i + 1)) in
  assert_int "big prefix_sum(999)" 500500 (IntFenwick.prefix_sum big 999);
  assert_int "big range_sum(0,99)" 5050 (IntFenwick.range_sum big 0 99);
  assert_int "big range_sum(100,199)" 15050 (IntFenwick.range_sum big 100 199);

  (* ── to_list roundtrip ──────────────────────────────────── *)
  Printf.printf "── Roundtrip ──\n";
  let original = [3; 1; 4; 1; 5; 9; 2; 6] in
  let ft2 = IntFenwick.of_list original in
  let recovered = IntFenwick.to_list ft2 in
  assert_eq "to_list roundtrip" "[3; 1; 4; 1; 5; 9; 2; 6]" (IntFenwick.to_string ft2);
  assert_int "roundtrip length" (List.length original) (List.length recovered);

  (* ── Float Fenwick ──────────────────────────────────────── *)
  Printf.printf "── Float Fenwick ──\n";
  let fft = FloatFenwick.of_list [1.5; 2.5; 3.5; 4.5] in
  assert_float_close "float prefix_sum(3)" 12.0 (FloatFenwick.prefix_sum fft 3) 1e-9;
  assert_float_close "float range_sum(1,2)" 6.0 (FloatFenwick.range_sum fft 1 2) 1e-9;
  FloatFenwick.update fft 0 0.5;
  assert_float_close "float after update" 2.0 (FloatFenwick.query_point fft 0) 1e-9;

  (* ── Find k-th (order statistics) ───────────────────────── *)
  Printf.printf "── Order Statistics (find_kth) ──\n";
  (* Frequency array: positions represent values 0-4, frequencies how many of each *)
  let freq = IntFenwick.of_list [2; 3; 0; 1; 4] in
  (* Cumulative: [2; 5; 5; 6; 10] *)
  (* 1st smallest is at position 0, 2nd at 0, 3rd at 1, etc. *)
  assert_int "kth(1)" 0 (IntFenwick.find_kth freq 1);
  assert_int "kth(2)" 0 (IntFenwick.find_kth freq 2);
  assert_int "kth(3)" 1 (IntFenwick.find_kth freq 3);
  assert_int "kth(5)" 1 (IntFenwick.find_kth freq 5);
  assert_int "kth(6)" 3 (IntFenwick.find_kth freq 6);
  assert_int "kth(7)" 4 (IntFenwick.find_kth freq 7);

  (* ── Summary ────────────────────────────────────────────── *)
  Printf.printf "\n══════ Results: %d passed, %d failed ══════\n\n" !passed !failed;
  if !failed > 0 then exit 1
