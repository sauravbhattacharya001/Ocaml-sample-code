(* Sparse Table - O(1) Range Minimum/Maximum Queries
 *
 * A sparse table is a data structure for answering range queries on
 * static arrays in O(1) time after O(n log n) preprocessing.
 * It works for any idempotent operation (min, max, gcd, bitwise AND/OR).
 *
 * Key properties:
 * - Build time: O(n log n)
 * - Query time: O(1) for idempotent operations
 * - Space: O(n log n)
 * - Static (no updates after construction)
 *
 * This implementation demonstrates:
 * - Generic sparse table over any idempotent binary operation
 * - Range minimum query (RMQ)
 * - Range maximum query
 * - Range GCD query
 * - Range bitwise AND/OR queries
 *)

(* ============================================================
   Core Sparse Table
   ============================================================ *)

module SparseTable : sig
  type t

  (** Build a sparse table from an array with an idempotent combine function.
      [combine a b] must be idempotent: combine a a = a *)
  val create : int array -> combine:(int -> int -> int) -> t

  (** Query the combined value over [l..r] inclusive. O(1). *)
  val query : t -> int -> int -> int

  (** Return the length of the underlying array *)
  val length : t -> int

  (** Pretty-print the sparse table structure *)
  val to_string : t -> string
end = struct
  type t = {
    table: int array array;  (* table.(k).(i) = combine of arr[i..i+2^k-1] *)
    log2: int array;         (* precomputed floor(log2(i)) *)
    n: int;
    combine: int -> int -> int;
  }

  let create arr ~combine =
    let n = Array.length arr in
    if n = 0 then { table = [||]; log2 = [||]; n = 0; combine }
    else begin
      (* Precompute log2 *)
      let log2 = Array.make (n + 1) 0 in
      for i = 2 to n do
        log2.(i) <- log2.(i / 2) + 1
      done;
      let max_k = log2.(n) + 1 in
      (* Build table *)
      let table = Array.make max_k [||] in
      table.(0) <- Array.copy arr;
      for k = 1 to max_k - 1 do
        let len = n - (1 lsl k) + 1 in
        if len > 0 then begin
          table.(k) <- Array.make len 0;
          for i = 0 to len - 1 do
            table.(k).(i) <- combine table.(k-1).(i) table.(k-1).(i + (1 lsl (k-1)))
          done
        end else
          table.(k) <- [||]
      done;
      { table; log2; n; combine }
    end

  let query st l r =
    if l > r || l < 0 || r >= st.n then
      failwith (Printf.sprintf "SparseTable.query: invalid range [%d, %d] for n=%d" l r st.n)
    else begin
      let len = r - l + 1 in
      let k = st.log2.(len) in
      st.combine st.table.(k).(l) st.table.(k).(r - (1 lsl k) + 1)
    end

  let length st = st.n

  let to_string st =
    if st.n = 0 then "SparseTable (empty)"
    else begin
      let buf = Buffer.create 256 in
      Buffer.add_string buf (Printf.sprintf "SparseTable (n=%d):\n" st.n);
      Array.iteri (fun k row ->
        if Array.length row > 0 then begin
          Buffer.add_string buf (Printf.sprintf "  k=%d (intervals of 2^%d=%d): " k k (1 lsl k));
          Buffer.add_string buf "[";
          Array.iteri (fun i v ->
            if i > 0 then Buffer.add_string buf "; ";
            Buffer.add_string buf (string_of_int v)
          ) row;
          Buffer.add_string buf "]\n"
        end
      ) st.table;
      Buffer.contents buf
    end
end

(* ============================================================
   Convenience constructors for common operations
   ============================================================ *)

module RMQ : sig
  type t
  val create : int array -> t
  val query_min : t -> int -> int -> int
  val query_max : t -> int -> int -> int
end = struct
  type t = {
    min_table: SparseTable.t;
    max_table: SparseTable.t;
  }

  let create arr = {
    min_table = SparseTable.create arr ~combine:min;
    max_table = SparseTable.create arr ~combine:max;
  }

  let query_min t l r = SparseTable.query t.min_table l r
  let query_max t l r = SparseTable.query t.max_table l r
end

(* GCD sparse table *)
module GCDTable : sig
  type t
  val create : int array -> t
  val query : t -> int -> int -> int
end = struct
  type t = SparseTable.t

  let rec gcd a b = if b = 0 then abs a else gcd b (a mod b)

  let create arr = SparseTable.create arr ~combine:gcd
  let query = SparseTable.query
end

(* Bitwise AND sparse table *)
module BitwiseAndTable : sig
  type t
  val create : int array -> t
  val query : t -> int -> int -> int
end = struct
  type t = SparseTable.t
  let create arr = SparseTable.create arr ~combine:(land)
  let query = SparseTable.query
end

(* Bitwise OR sparse table *)
module BitwiseOrTable : sig
  type t
  val create : int array -> t
  val query : t -> int -> int -> int
end = struct
  type t = SparseTable.t
  let create arr = SparseTable.create arr ~combine:(lor)
  let query = SparseTable.query
end

(* ============================================================
   2D Sparse Table (for range min on a matrix)
   ============================================================ *)

module SparseTable2D : sig
  type t
  val create : int array array -> combine:(int -> int -> int) -> t
  val query : t -> int -> int -> int -> int -> int
end = struct
  type t = {
    (* table.(kr).(kc).(r).(c) = combine over submatrix of size 2^kr x 2^kc starting at (r,c) *)
    table: int array array array array;
    log2: int array;
    rows: int;
    cols: int;
    combine: int -> int -> int;
  }

  let create mat ~combine =
    let rows = Array.length mat in
    if rows = 0 then { table = [||]; log2 = [||]; rows = 0; cols = 0; combine }
    else begin
      let cols = Array.length mat.(0) in
      let max_n = max rows cols + 1 in
      let log2 = Array.make max_n 0 in
      for i = 2 to max_n - 1 do
        log2.(i) <- log2.(i / 2) + 1
      done;
      let max_kr = log2.(rows) + 1 in
      let max_kc = log2.(cols) + 1 in
      let table = Array.init max_kr (fun _ ->
        Array.init max_kc (fun _ ->
          Array.make_matrix rows cols 0
        )
      ) in
      (* Base: kr=0, kc=0 *)
      for r = 0 to rows - 1 do
        for c = 0 to cols - 1 do
          table.(0).(0).(r).(c) <- mat.(r).(c)
        done
      done;
      (* Build along columns first: kr=0, kc>0 *)
      for kc = 1 to max_kc - 1 do
        for r = 0 to rows - 1 do
          let clen = cols - (1 lsl kc) + 1 in
          for c = 0 to clen - 1 do
            table.(0).(kc).(r).(c) <-
              combine table.(0).(kc-1).(r).(c) table.(0).(kc-1).(r).(c + (1 lsl (kc-1)))
          done
        done
      done;
      (* Build along rows *)
      for kr = 1 to max_kr - 1 do
        for kc = 0 to max_kc - 1 do
          let rlen = rows - (1 lsl kr) + 1 in
          let clen = cols - (1 lsl kc) + 1 in
          for r = 0 to rlen - 1 do
            for c = 0 to clen - 1 do
              table.(kr).(kc).(r).(c) <-
                combine table.(kr-1).(kc).(r).(c) table.(kr-1).(kc).(r + (1 lsl (kr-1))).(c)
            done
          done
        done
      done;
      { table; log2; rows; cols; combine }
    end

  let query st r1 c1 r2 c2 =
    if r1 > r2 || c1 > c2 || r1 < 0 || c1 < 0 || r2 >= st.rows || c2 >= st.cols then
      failwith "SparseTable2D.query: invalid range"
    else begin
      let kr = st.log2.(r2 - r1 + 1) in
      let kc = st.log2.(c2 - c1 + 1) in
      let a = st.combine
        st.table.(kr).(kc).(r1).(c1)
        st.table.(kr).(kc).(r1).(c2 - (1 lsl kc) + 1) in
      let b = st.combine
        st.table.(kr).(kc).(r2 - (1 lsl kr) + 1).(c1)
        st.table.(kr).(kc).(r2 - (1 lsl kr) + 1).(c2 - (1 lsl kc) + 1) in
      st.combine a b
    end
end

(* ============================================================
   Demo & Tests
   ============================================================ *)

let () =
  print_endline "=== Sparse Table Data Structure ===\n";

  (* Basic RMQ *)
  let arr = [| 3; 1; 4; 1; 5; 9; 2; 6; 5; 3; 5; 8 |] in
  Printf.printf "Array: [%s]\n\n"
    (String.concat "; " (Array.to_list (Array.map string_of_int arr)));

  let st = SparseTable.create arr ~combine:min in
  print_string (SparseTable.to_string st);
  print_newline ();

  (* Test range minimum queries *)
  print_endline "--- Range Minimum Queries ---";
  let test_rmq l r =
    let result = SparseTable.query st l r in
    Printf.printf "  min(%d..%d) = %d\n" l r result
  in
  test_rmq 0 3;   (* min of [3;1;4;1] = 1 *)
  test_rmq 4 7;   (* min of [5;9;2;6] = 2 *)
  test_rmq 0 11;  (* min of entire array = 1 *)
  test_rmq 5 5;   (* single element = 9 *)
  test_rmq 8 11;  (* min of [5;3;5;8] = 3 *)
  print_newline ();

  (* RMQ module with both min and max *)
  let rmq = RMQ.create arr in
  print_endline "--- Range Min/Max Queries ---";
  Printf.printf "  min(0..11) = %d, max(0..11) = %d\n"
    (RMQ.query_min rmq 0 11) (RMQ.query_max rmq 0 11);
  Printf.printf "  min(2..6) = %d, max(2..6) = %d\n"
    (RMQ.query_min rmq 2 6) (RMQ.query_max rmq 2 6);
  print_newline ();

  (* GCD queries *)
  let gcd_arr = [| 12; 18; 24; 36; 48; 60 |] in
  Printf.printf "GCD Array: [%s]\n"
    (String.concat "; " (Array.to_list (Array.map string_of_int gcd_arr)));
  let gcd_st = GCDTable.create gcd_arr in
  print_endline "--- Range GCD Queries ---";
  Printf.printf "  gcd(0..5) = %d\n" (GCDTable.query gcd_st 0 5);  (* 6 *)
  Printf.printf "  gcd(0..2) = %d\n" (GCDTable.query gcd_st 0 2);  (* 6 *)
  Printf.printf "  gcd(2..4) = %d\n" (GCDTable.query gcd_st 2 4);  (* 12 *)
  Printf.printf "  gcd(3..5) = %d\n" (GCDTable.query gcd_st 3 5);  (* 12 *)
  print_newline ();

  (* Bitwise AND queries *)
  let bit_arr = [| 0b1111; 0b1100; 0b1010; 0b0110; 0b1001 |] in
  Printf.printf "Bitwise Array: [%s]\n"
    (String.concat "; " (Array.to_list (Array.map (Printf.sprintf "0b%04b") bit_arr)));
  let and_st = BitwiseAndTable.create bit_arr in
  let or_st = BitwiseOrTable.create bit_arr in
  print_endline "--- Range Bitwise Queries ---";
  Printf.printf "  AND(0..4) = 0b%04b\n" (BitwiseAndTable.query and_st 0 4);
  Printf.printf "  OR(0..4)  = 0b%04b\n" (BitwiseOrTable.query or_st 0 4);
  Printf.printf "  AND(1..3) = 0b%04b\n" (BitwiseAndTable.query and_st 1 3);
  Printf.printf "  OR(1..3)  = 0b%04b\n" (BitwiseOrTable.query or_st 1 3);
  print_newline ();

  (* 2D Sparse Table *)
  print_endline "--- 2D Range Minimum Query ---";
  let mat = [|
    [| 1; 3; 5; 7 |];
    [| 2; 4; 6; 8 |];
    [| 9; 0; 2; 4 |];
    [| 3; 5; 7; 1 |];
  |] in
  print_endline "Matrix:";
  Array.iter (fun row ->
    Printf.printf "  [%s]\n"
      (String.concat "; " (Array.to_list (Array.map string_of_int row)))
  ) mat;
  let st2d = SparseTable2D.create mat ~combine:min in
  Printf.printf "  min(0,0 -> 3,3) = %d\n" (SparseTable2D.query st2d 0 0 3 3);  (* 0 *)
  Printf.printf "  min(0,0 -> 1,1) = %d\n" (SparseTable2D.query st2d 0 0 1 1);  (* 1 *)
  Printf.printf "  min(2,0 -> 3,3) = %d\n" (SparseTable2D.query st2d 2 0 3 3);  (* 0 *)
  Printf.printf "  min(0,2 -> 1,3) = %d\n" (SparseTable2D.query st2d 0 2 1 3);  (* 5 *)
  print_newline ();

  (* Verification *)
  print_endline "--- Verification: brute-force vs sparse table ---";
  let n = Array.length arr in
  let errors = ref 0 in
  for l = 0 to n - 1 do
    for r = l to n - 1 do
      let brute = ref arr.(l) in
      for i = l + 1 to r do
        brute := min !brute arr.(i)
      done;
      let sparse = SparseTable.query st l r in
      if sparse <> !brute then begin
        Printf.printf "  MISMATCH at [%d,%d]: brute=%d sparse=%d\n" l r !brute sparse;
        incr errors
      end
    done
  done;
  if !errors = 0 then
    Printf.printf "  All %d range queries verified correct!\n" (n * (n + 1) / 2)
  else
    Printf.printf "  %d errors found!\n" !errors;

  print_endline "\n=== Done ==="
