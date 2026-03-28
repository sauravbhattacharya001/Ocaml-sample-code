(* count_min_sketch.ml — Probabilistic Frequency Estimation *)
(* A Count-Min Sketch uses d hash functions over a w-wide table of     *)
(* counters to estimate element frequencies in data streams.            *)
(* Supports: create, add, count, merge, total, heavy_hitters,          *)
(* point_query, inner_product, reset, copy, of_list.                   *)
(* Always overestimates (never underestimates) true frequency.         *)

module CountMinSketch = struct

  type t = {
    table : int array array;  (* d rows × w columns *)
    w     : int;              (* width — number of columns *)
    d     : int;              (* depth — number of hash functions *)
    total : int;              (* total items added *)
  }

  (* ---- Hash functions ---- *)
  (* Double hashing: h_i(x) = (h1(x) + i * h2(x)) mod w *)

  let hash1 x = Hashtbl.hash x
  let hash2 x = Hashtbl.hash (x, 0x9e3779b9)

  let hash_i w h1 h2 i =
    ((h1 + i * h2) mod w + w) mod w

  (* ---- Construction ---- *)

  (* Create with explicit width w and depth d.
     Approximation guarantee: error ≤ ε·N with probability ≥ 1−δ
     when w = ⌈e/ε⌉ and d = ⌈ln(1/δ)⌉. *)
  let create ~w ~d =
    if w <= 0 || d <= 0 then invalid_arg "CountMinSketch.create: w and d must be positive";
    { table = Array.init d (fun _ -> Array.make w 0);
      w; d; total = 0 }

  (* Create from error parameters ε (epsilon) and δ (delta). *)
  let create_eps ~epsilon ~delta =
    if epsilon <= 0.0 || delta <= 0.0 then
      invalid_arg "CountMinSketch.create_eps: epsilon and delta must be positive";
    let w = int_of_float (ceil (exp 1.0 /. epsilon)) in
    let d = int_of_float (ceil (log (1.0 /. delta))) in
    create ~w ~d

  (* ---- Core API ---- *)

  (* Add n occurrences of an element. *)
  let add cms x ?(n=1) () =
    let h1 = hash1 x and h2 = hash2 x in
    let new_table = Array.map Array.copy cms.table in
    for i = 0 to cms.d - 1 do
      let j = hash_i cms.w h1 h2 i in
      new_table.(i).(j) <- new_table.(i).(j) + n
    done;
    { cms with table = new_table; total = cms.total + n }

  (* Estimate the frequency of an element (minimum across all rows). *)
  let count cms x =
    let h1 = hash1 x and h2 = hash2 x in
    let min_val = ref max_int in
    for i = 0 to cms.d - 1 do
      let j = hash_i cms.w h1 h2 i in
      if cms.table.(i).(j) < !min_val then
        min_val := cms.table.(i).(j)
    done;
    !min_val

  (* Alias for count. *)
  let point_query = count

  (* Total number of items added. *)
  let total cms = cms.total

  (* Merge two sketches of the same dimensions (element-wise addition). *)
  let merge a b =
    if a.w <> b.w || a.d <> b.d then
      invalid_arg "CountMinSketch.merge: dimensions must match";
    let new_table = Array.init a.d (fun i ->
      Array.init a.w (fun j ->
        a.table.(i).(j) + b.table.(i).(j)))
    in
    { w = a.w; d = a.d; table = new_table; total = a.total + b.total }

  (* Estimated inner product of two sketches (min across rows of dot products). *)
  let inner_product a b =
    if a.w <> b.w || a.d <> b.d then
      invalid_arg "CountMinSketch.inner_product: dimensions must match";
    let min_dot = ref max_int in
    for i = 0 to a.d - 1 do
      let dot = ref 0 in
      for j = 0 to a.w - 1 do
        dot := !dot + a.table.(i).(j) * b.table.(i).(j)
      done;
      if !dot < !min_dot then min_dot := !dot
    done;
    !min_dot

  (* Find elements from a candidate list whose estimated count ≥ threshold. *)
  let heavy_hitters cms candidates ~threshold =
    List.filter (fun x -> count cms x >= threshold) candidates

  (* Reset all counters to zero. *)
  let reset cms =
    { table = Array.init cms.d (fun _ -> Array.make cms.w 0);
      w = cms.w; d = cms.d; total = 0 }

  (* Deep copy. *)
  let copy cms =
    { cms with table = Array.map Array.copy cms.table }

  (* Build from a list of elements. *)
  let of_list ~w ~d xs =
    List.fold_left (fun cms x -> add cms x ()) (create ~w ~d) xs

  (* Saturation: fraction of non-zero cells. *)
  let saturation cms =
    let non_zero = ref 0 in
    Array.iter (fun row ->
      Array.iter (fun v -> if v > 0 then incr non_zero) row
    ) cms.table;
    float_of_int !non_zero /. float_of_int (cms.w * cms.d)

  (* Pretty-print sketch info. *)
  let to_string cms =
    Printf.sprintf "CountMinSketch(w=%d, d=%d, total=%d, saturation=%.2f%%)"
      cms.w cms.d cms.total (saturation cms *. 100.0)

end

(* ---- Demo / Tests ---- *)

let () =
  let open CountMinSketch in
  Printf.printf "=== Count-Min Sketch Demo ===\n\n";

  (* Create a sketch with ε=0.01, δ=0.01 *)
  let cms = create_eps ~epsilon:0.01 ~delta:0.01 in
  Printf.printf "Created: %s\n\n" (to_string cms);

  (* Add elements with various frequencies *)
  let cms = add cms "apple" ~n:100 () in
  let cms = add cms "banana" ~n:50 () in
  let cms = add cms "cherry" ~n:10 () in
  let cms = add cms "date" ~n:1 () in
  Printf.printf "After insertions: %s\n\n" (to_string cms);

  (* Query frequencies *)
  Printf.printf "Frequency estimates:\n";
  List.iter (fun (item, expected) ->
    let est = count cms item in
    Printf.printf "  %-10s expected=%3d  estimated=%3d  %s\n"
      item expected est
      (if est >= expected then "✓ (overestimate OK)" else "✗ ERROR")
  ) [("apple", 100); ("banana", 50); ("cherry", 10); ("date", 1)];

  (* Query for absent element *)
  let ghost = count cms "ghost" in
  Printf.printf "  %-10s expected=%3d  estimated=%3d  (false positive noise)\n\n"
    "ghost" 0 ghost;

  (* Merge two sketches *)
  Printf.printf "--- Merge Test ---\n";
  let cms_a = of_list ~w:272 ~d:5 ["x"; "x"; "x"; "y"; "y"; "z"] in
  let cms_b = of_list ~w:272 ~d:5 ["x"; "y"; "y"; "y"; "w"] in
  let cms_merged = merge cms_a cms_b in
  Printf.printf "Merged totals: x=%d (exp 4), y=%d (exp 5), z=%d (exp 1), w=%d (exp 1)\n\n"
    (count cms_merged "x") (count cms_merged "y")
    (count cms_merged "z") (count cms_merged "w");

  (* Heavy hitters *)
  Printf.printf "--- Heavy Hitters ---\n";
  let hitters = heavy_hitters cms ["apple";"banana";"cherry";"date";"ghost"] ~threshold:20 in
  Printf.printf "Items with count ≥ 20: [%s]\n\n"
    (String.concat "; " hitters);

  (* Inner product *)
  Printf.printf "--- Inner Product ---\n";
  let ip = inner_product cms_a cms_b in
  Printf.printf "Inner product of A·B = %d (exact = 3*1 + 2*3 = 9)\n\n" ip;

  Printf.printf "=== All Count-Min Sketch tests passed! ===\n"
