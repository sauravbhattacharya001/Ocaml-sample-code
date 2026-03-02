(** Matrix — Linear algebra operations with OCaml modules and functors.

    Demonstrates:
    - Module signatures and functors for generic numeric types
    - 2D array manipulation with imperative style
    - Gaussian elimination, LU decomposition
    - Determinant, inverse, matrix power
    - Pretty printing with configurable precision

    Concepts: functors, module signatures, abstract types, imperative arrays,
    exception handling, higher-order functions, numerical algorithms.

    Usage:
      ocamlfind ocamlopt -package str -linkpkg matrix.ml -o matrix && ./matrix
    Or simply:
      ocaml matrix.ml
*)

(** {1 Module Signature for Numeric Types} *)

module type NUM = sig
  type t
  val zero : t
  val one : t
  val add : t -> t -> t
  val sub : t -> t -> t
  val mul : t -> t -> t
  val div : t -> t -> t
  val neg : t -> t
  val abs : t -> t
  val compare : t -> t -> int
  val equal : t -> t -> bool
  val of_int : int -> t
  val to_float : t -> float
  val to_string : t -> string
end

(** {1 Float Implementation} *)

module Float_Num : NUM with type t = float = struct
  type t = float
  let zero = 0.0
  let one = 1.0
  let add = ( +. )
  let sub = ( -. )
  let mul = ( *. )
  let div = ( /. )
  let neg x = -. x
  let abs = Float.abs
  let compare = Float.compare
  let equal a b = Float.abs (a -. b) < 1e-10
  let of_int = Float.of_int
  let to_float x = x
  let to_string x =
    let s = Printf.sprintf "%.4f" x in
    (* Trim trailing zeros for readability *)
    let len = String.length s in
    let rec trim i =
      if i <= 0 then s
      else if s.[i] = '0' then trim (i - 1)
      else if s.[i] = '.' then String.sub s 0 i
      else String.sub s 0 (i + 1)
    in
    trim (len - 1)
end

(** {1 Integer Implementation} *)

module Int_Num : NUM with type t = int = struct
  type t = int
  let zero = 0
  let one = 1
  let add = ( + )
  let sub = ( - )
  let mul = ( * )
  let div = ( / )
  let neg x = -x
  let abs = Int.abs
  let compare = Int.compare
  let equal = Int.equal
  let of_int x = x
  let to_float = Float.of_int
  let to_string = Int.to_string
end

(** {1 Matrix Functor} *)

module Make (N : NUM) = struct
  type elt = N.t

  type t = {
    rows : int;
    cols : int;
    data : elt array array;
  }

  exception Dimension_mismatch of string
  exception Singular_matrix
  exception Invalid_argument of string

  (** {2 Construction} *)

  let create rows cols init =
    if rows <= 0 || cols <= 0 then
      raise (Invalid_argument "Matrix dimensions must be positive");
    { rows; cols; data = Array.init rows (fun _ -> Array.make cols init) }

  let zeros rows cols = create rows cols N.zero

  let identity n =
    let m = zeros n n in
    for i = 0 to n - 1 do
      m.data.(i).(i) <- N.one
    done;
    m

  let of_list lst =
    match lst with
    | [] -> raise (Invalid_argument "Cannot create matrix from empty list")
    | row0 :: _ ->
      let rows = List.length lst in
      let cols = List.length row0 in
      if cols = 0 then
        raise (Invalid_argument "Cannot create matrix with zero columns");
      let data = Array.of_list (List.map Array.of_list lst) in
      (* Validate all rows have same length *)
      Array.iter (fun row ->
        if Array.length row <> cols then
          raise (Invalid_argument "All rows must have the same length")
      ) data;
      { rows; cols; data }

  let of_array arr =
    let rows = Array.length arr in
    if rows = 0 then
      raise (Invalid_argument "Cannot create matrix from empty array");
    let cols = Array.length arr.(0) in
    if cols = 0 then
      raise (Invalid_argument "Cannot create matrix with zero columns");
    Array.iter (fun row ->
      if Array.length row <> cols then
        raise (Invalid_argument "All rows must have the same length")
    ) arr;
    { rows; cols; data = Array.map Array.copy arr }

  let copy m =
    { rows = m.rows; cols = m.cols; data = Array.map Array.copy m.data }

  let row_vector lst =
    of_list [lst]

  let col_vector lst =
    of_list (List.map (fun x -> [x]) lst)

  let diagonal lst =
    let n = List.length lst in
    let m = zeros n n in
    List.iteri (fun i v -> m.data.(i).(i) <- v) lst;
    m

  (** {2 Access} *)

  let get m i j =
    if i < 0 || i >= m.rows || j < 0 || j >= m.cols then
      raise (Invalid_argument (Printf.sprintf "Index (%d,%d) out of bounds for %dx%d matrix" i j m.rows m.cols));
    m.data.(i).(j)

  let set m i j v =
    if i < 0 || i >= m.rows || j < 0 || j >= m.cols then
      raise (Invalid_argument (Printf.sprintf "Index (%d,%d) out of bounds for %dx%d matrix" i j m.rows m.cols));
    let m' = copy m in
    m'.data.(i).(j) <- v;
    m'

  let dims m = (m.rows, m.cols)
  let num_rows m = m.rows
  let num_cols m = m.cols

  let get_row m i =
    if i < 0 || i >= m.rows then
      raise (Invalid_argument "Row index out of bounds");
    Array.to_list m.data.(i)

  let get_col m j =
    if j < 0 || j >= m.cols then
      raise (Invalid_argument "Column index out of bounds");
    Array.to_list (Array.init m.rows (fun i -> m.data.(i).(j)))

  (** {2 Arithmetic} *)

  let map f m =
    { rows = m.rows; cols = m.cols;
      data = Array.map (fun row -> Array.map f row) m.data }

  let map2 f a b =
    if a.rows <> b.rows || a.cols <> b.cols then
      raise (Dimension_mismatch
        (Printf.sprintf "Cannot combine %dx%d and %dx%d matrices"
           a.rows a.cols b.rows b.cols));
    { rows = a.rows; cols = a.cols;
      data = Array.init a.rows (fun i ->
        Array.init a.cols (fun j ->
          f a.data.(i).(j) b.data.(i).(j))) }

  let add = map2 N.add
  let sub = map2 N.sub

  let scale s m = map (N.mul s) m

  let mul a b =
    if a.cols <> b.rows then
      raise (Dimension_mismatch
        (Printf.sprintf "Cannot multiply %dx%d by %dx%d matrix"
           a.rows a.cols b.rows b.cols));
    let result = zeros a.rows b.cols in
    for i = 0 to a.rows - 1 do
      for j = 0 to b.cols - 1 do
        let sum = ref N.zero in
        for k = 0 to a.cols - 1 do
          sum := N.add !sum (N.mul a.data.(i).(k) b.data.(k).(j))
        done;
        result.data.(i).(j) <- !sum
      done
    done;
    result

  let ( + ) = add
  let ( - ) = sub
  let ( * ) = mul

  let hadamard = map2 N.mul

  (** {2 Transpose & Reshape} *)

  let transpose m =
    { rows = m.cols; cols = m.rows;
      data = Array.init m.cols (fun j ->
        Array.init m.rows (fun i -> m.data.(i).(j))) }

  let is_square m = m.rows = m.cols

  let is_symmetric m =
    if not (is_square m) then false
    else
      let n = m.rows in
      let rec check i j =
        if i >= n then true
        else if j >= n then check (i + 1) (i + 2)
        else if not (N.equal m.data.(i).(j) m.data.(j).(i)) then false
        else check i (j + 1)
      in
      check 0 1

  (** {2 Row Operations (for Gaussian elimination)} *)

  let swap_rows m i j =
    let m' = copy m in
    let tmp = m'.data.(i) in
    m'.data.(i) <- m'.data.(j);
    m'.data.(j) <- tmp;
    m'

  (** {2 Determinant via LU Decomposition} *)

  let det m =
    if not (is_square m) then
      raise (Dimension_mismatch "Determinant requires a square matrix");
    let n = m.rows in
    if n = 1 then m.data.(0).(0)
    else if n = 2 then
      N.sub (N.mul m.data.(0).(0) m.data.(1).(1))
            (N.mul m.data.(0).(1) m.data.(1).(0))
    else begin
      (* Gaussian elimination with partial pivoting *)
      let a = Array.map Array.copy m.data in
      let sign = ref N.one in
      for col = 0 to n - 1 do
        (* Find pivot *)
        let max_row = ref col in
        let max_val = ref (N.abs a.(col).(col)) in
        for row = col + 1 to n - 1 do
          let v = N.abs a.(row).(col) in
          if N.compare v !max_val > 0 then begin
            max_row := row;
            max_val := v
          end
        done;
        if N.equal !max_val N.zero then begin
          sign := N.zero;  (* Singular — det is 0 *)
        end else begin
          if !max_row <> col then begin
            let tmp = a.(col) in
            a.(col) <- a.(!max_row);
            a.(!max_row) <- tmp;
            sign := N.neg !sign
          end;
          let pivot = a.(col).(col) in
          for row = col + 1 to n - 1 do
            let factor = N.div a.(row).(col) pivot in
            for j = col to n - 1 do
              a.(row).(j) <- N.sub a.(row).(j) (N.mul factor a.(col).(j))
            done
          done
        end
      done;
      if N.equal !sign N.zero then N.zero
      else begin
        let result = ref !sign in
        for i = 0 to n - 1 do
          result := N.mul !result a.(i).(i)
        done;
        !result
      end
    end

  (** {2 Inverse via Gauss-Jordan Elimination} *)

  let inverse m =
    if not (is_square m) then
      raise (Dimension_mismatch "Inverse requires a square matrix");
    let n = m.rows in
    (* Augment [A | I] *)
    let aug = Array.init n (fun i ->
      Array.init (2 * n) (fun j ->
        if j < n then m.data.(i).(j)
        else if j - n = i then N.one
        else N.zero)
    ) in
    (* Forward elimination *)
    for col = 0 to n - 1 do
      (* Partial pivoting *)
      let max_row = ref col in
      let max_val = ref (N.abs aug.(col).(col)) in
      for row = col + 1 to n - 1 do
        let v = N.abs aug.(row).(col) in
        if N.compare v !max_val > 0 then begin
          max_row := row;
          max_val := v
        end
      done;
      if N.equal !max_val N.zero then raise Singular_matrix;
      if !max_row <> col then begin
        let tmp = aug.(col) in
        aug.(col) <- aug.(!max_row);
        aug.(!max_row) <- tmp
      end;
      let pivot = aug.(col).(col) in
      for j = 0 to 2 * n - 1 do
        aug.(col).(j) <- N.div aug.(col).(j) pivot
      done;
      for row = 0 to n - 1 do
        if row <> col then begin
          let factor = aug.(row).(col) in
          for j = 0 to 2 * n - 1 do
            aug.(row).(j) <- N.sub aug.(row).(j) (N.mul factor aug.(col).(j))
          done
        end
      done
    done;
    (* Extract right half *)
    { rows = n; cols = n;
      data = Array.init n (fun i ->
        Array.init n (fun j -> aug.(i).(j + n))) }

  (** {2 Trace} *)

  let trace m =
    if not (is_square m) then
      raise (Dimension_mismatch "Trace requires a square matrix");
    let sum = ref N.zero in
    for i = 0 to m.rows - 1 do
      sum := N.add !sum m.data.(i).(i)
    done;
    !sum

  (** {2 Matrix Power} *)

  let rec power m n =
    if not (is_square m) then
      raise (Dimension_mismatch "Power requires a square matrix");
    if n < 0 then
      raise (Invalid_argument "Negative exponent not supported (use inverse first)");
    if n = 0 then identity m.rows
    else if n = 1 then copy m
    else
      let half = power m (n / 2) in
      let sq = mul half half in
      if n mod 2 = 0 then sq
      else mul sq m

  (** {2 Norms} *)

  let frobenius_norm m =
    let sum = ref N.zero in
    Array.iter (fun row ->
      Array.iter (fun v ->
        sum := N.add !sum (N.mul v v)
      ) row
    ) m.data;
    sqrt (N.to_float !sum)

  let max_norm m =
    let mx = ref N.zero in
    Array.iter (fun row ->
      Array.iter (fun v ->
        let av = N.abs v in
        if N.compare av !mx > 0 then mx := av
      ) row
    ) m.data;
    !mx

  (** {2 Predicates} *)

  let equal a b =
    if a.rows <> b.rows || a.cols <> b.cols then false
    else
      let ok = ref true in
      for i = 0 to a.rows - 1 do
        for j = 0 to a.cols - 1 do
          if not (N.equal a.data.(i).(j) b.data.(i).(j)) then
            ok := false
        done
      done;
      !ok

  let is_identity m =
    if not (is_square m) then false
    else equal m (identity m.rows)

  let is_zero m =
    equal m (zeros m.rows m.cols)

  let is_diagonal m =
    if not (is_square m) then false
    else begin
      let ok = ref true in
      for i = 0 to m.rows - 1 do
        for j = 0 to m.cols - 1 do
          if i <> j && not (N.equal m.data.(i).(j) N.zero) then
            ok := false
        done
      done;
      !ok
    end

  let is_upper_triangular m =
    if not (is_square m) then false
    else begin
      let ok = ref true in
      for i = 1 to m.rows - 1 do
        for j = 0 to i - 1 do
          if not (N.equal m.data.(i).(j) N.zero) then
            ok := false
        done
      done;
      !ok
    end

  let is_lower_triangular m =
    if not (is_square m) then false
    else begin
      let ok = ref true in
      for i = 0 to m.rows - 2 do
        for j = i + 1 to m.cols - 1 do
          if not (N.equal m.data.(i).(j) N.zero) then
            ok := false
        done
      done;
      !ok
    end

  (** {2 Fold & Iteration} *)

  let fold f init m =
    let acc = ref init in
    Array.iter (fun row ->
      Array.iter (fun v -> acc := f !acc v) row
    ) m.data;
    !acc

  let iter f m =
    for i = 0 to m.rows - 1 do
      for j = 0 to m.cols - 1 do
        f i j m.data.(i).(j)
      done
    done

  let to_list m =
    Array.to_list (Array.map Array.to_list m.data)

  let to_array m =
    Array.map Array.copy m.data

  (** {2 Pretty Printing} *)

  let to_string m =
    let widths = Array.make m.cols 0 in
    (* Measure column widths *)
    for j = 0 to m.cols - 1 do
      for i = 0 to m.rows - 1 do
        let w = String.length (N.to_string m.data.(i).(j)) in
        if w > widths.(j) then widths.(j) <- w
      done
    done;
    let buf = Buffer.create (m.rows * m.cols * 8) in
    Buffer.add_string buf (Printf.sprintf "[%dx%d matrix]\n" m.rows m.cols);
    for i = 0 to m.rows - 1 do
      Buffer.add_string buf "│ ";
      for j = 0 to m.cols - 1 do
        let s = N.to_string m.data.(i).(j) in
        let pad = widths.(j) - String.length s in
        for _ = 1 to pad do Buffer.add_char buf ' ' done;
        Buffer.add_string buf s;
        if j < m.cols - 1 then Buffer.add_string buf "  "
      done;
      Buffer.add_string buf " │\n"
    done;
    Buffer.contents buf

  let print m = print_string (to_string m)
end

(* ─── Instantiate Float and Int matrices ─────────────────── *)

module FloatMatrix = Make(Float_Num)
module IntMatrix   = Make(Int_Num)

(* ═══════════════════════════════════════════════════════════
   Demo / Tests
   ═══════════════════════════════════════════════════════════ *)

let () =
  print_endline "╔══════════════════════════════════════╗";
  print_endline "║       Matrix — Linear Algebra        ║";
  print_endline "╚══════════════════════════════════════╝\n";

  let module M = FloatMatrix in

  (* --- Construction --- *)
  print_endline "▸ Creating matrices";
  let a = M.of_list [
    [1.0; 2.0; 3.0];
    [4.0; 5.0; 6.0];
    [7.0; 8.0; 10.0]  (* not 9, so it's invertible *)
  ] in
  M.print a;

  let id = M.identity 3 in
  Printf.printf "\nIdentity 3×3:\n";
  M.print id;

  (* --- Arithmetic --- *)
  print_endline "\n▸ Matrix multiplication A × I = A";
  let prod = M.mul a id in
  M.print prod;
  assert (M.equal prod a);

  print_endline "\n▸ A + A:";
  let doubled = M.add a a in
  M.print doubled;

  print_endline "\n▸ Scalar multiply 0.5 × (A + A) = A:";
  let halved = M.scale 0.5 doubled in
  M.print halved;
  assert (M.equal halved a);

  (* --- Transpose --- *)
  print_endline "\n▸ Transpose of A:";
  let at = M.transpose a in
  M.print at;
  assert (M.equal (M.transpose at) a);

  (* --- Determinant --- *)
  print_endline "\n▸ Determinant calculations";
  let d = M.det a in
  Printf.printf "  det(A) = %s\n" (Float_Num.to_string d);
  Printf.printf "  det(I) = %s\n" (Float_Num.to_string (M.det id));
  assert (Float_Num.equal (M.det id) 1.0);

  (* --- Inverse --- *)
  print_endline "\n▸ Inverse of A:";
  let a_inv = M.inverse a in
  M.print a_inv;

  print_endline "  Verifying A × A⁻¹ ≈ I:";
  let should_be_id = M.mul a a_inv in
  M.print should_be_id;

  (* --- Trace --- *)
  let t = M.trace a in
  Printf.printf "\n▸ Trace(A) = %s (sum of diagonal)\n" (Float_Num.to_string t);
  assert (Float_Num.equal t 16.0);  (* 1 + 5 + 10 *)

  (* --- Matrix Power --- *)
  print_endline "\n▸ A² (matrix squared):";
  let a2 = M.power a 2 in
  M.print a2;
  assert (M.equal a2 (M.mul a a));

  print_endline "  A⁰ = I:";
  let a0 = M.power a 0 in
  assert (M.equal a0 id);
  Printf.printf "  ✓ A⁰ = I verified\n";

  (* --- Norms --- *)
  Printf.printf "\n▸ Frobenius norm = %.4f\n" (M.frobenius_norm a);
  Printf.printf "  Max norm = %s\n" (Float_Num.to_string (M.max_norm a));

  (* --- Predicates --- *)
  print_endline "\n▸ Predicates:";
  Printf.printf "  is_square(A) = %b\n" (M.is_square a);
  Printf.printf "  is_symmetric(A) = %b\n" (M.is_symmetric a);
  Printf.printf "  is_diagonal(I) = %b\n" (M.is_diagonal id);
  Printf.printf "  is_identity(I) = %b\n" (M.is_identity id);

  let sym = M.of_list [
    [1.0; 2.0; 3.0];
    [2.0; 5.0; 6.0];
    [3.0; 6.0; 9.0]
  ] in
  Printf.printf "  is_symmetric([[1,2,3],[2,5,6],[3,6,9]]) = %b\n" (M.is_symmetric sym);

  let upper = M.of_list [
    [1.0; 2.0; 3.0];
    [0.0; 4.0; 5.0];
    [0.0; 0.0; 6.0]
  ] in
  Printf.printf "  is_upper_triangular = %b\n" (M.is_upper_triangular upper);
  Printf.printf "  is_lower_triangular = %b\n" (M.is_lower_triangular upper);

  (* --- Hadamard (element-wise) product --- *)
  print_endline "\n▸ Hadamard (element-wise) product A ⊙ A:";
  let h = M.hadamard a a in
  M.print h;

  (* --- Row/column access --- *)
  let r1 = M.get_row a 1 in
  Printf.printf "\n▸ Row 1 of A: [%s]\n"
    (String.concat "; " (List.map Float_Num.to_string r1));

  let c2 = M.get_col a 2 in
  Printf.printf "  Col 2 of A: [%s]\n"
    (String.concat "; " (List.map Float_Num.to_string c2));

  (* --- Fold --- *)
  let sum = M.fold Float_Num.add 0.0 a in
  Printf.printf "\n▸ Sum of all elements = %s\n" (Float_Num.to_string sum);

  (* --- Vectors --- *)
  print_endline "\n▸ Row and column vectors:";
  let rv = M.row_vector [1.0; 2.0; 3.0] in
  Printf.printf "  Row vector: "; M.print rv;
  let cv = M.col_vector [4.0; 5.0; 6.0] in
  Printf.printf "  Col vector: "; M.print cv;

  (* Dot product via matrix multiplication *)
  let dot = M.mul rv cv in
  Printf.printf "  Dot product [1,2,3]·[4,5,6] = %s\n"
    (Float_Num.to_string (M.get dot 0 0));
  assert (Float_Num.equal (M.get dot 0 0) 32.0);

  (* --- Diagonal matrix --- *)
  print_endline "\n▸ Diagonal matrix:";
  let diag = M.diagonal [2.0; 3.0; 5.0] in
  M.print diag;
  assert (M.is_diagonal diag);

  (* --- Integer matrix --- *)
  print_endline "\n▸ Integer matrix demo:";
  let module IM = IntMatrix in
  let im = IM.of_list [[1;2];[3;4]] in
  IM.print im;
  Printf.printf "  det = %s\n" (Int_Num.to_string (IM.det im));
  assert (Int_Num.equal (IM.det im) (-2));

  (* --- Error handling --- *)
  print_endline "\n▸ Error handling:";
  (try
    let _ = M.mul (M.zeros 2 3) (M.zeros 4 2) in
    assert false
  with M.Dimension_mismatch msg ->
    Printf.printf "  Dimension mismatch caught: %s\n" msg);

  (try
    let singular = M.of_list [[1.0;2.0];[2.0;4.0]] in
    let _ = M.inverse singular in
    assert false
  with M.Singular_matrix ->
    Printf.printf "  Singular matrix caught ✓\n");

  (try
    let _ = M.get a 5 0 in
    assert false
  with M.Invalid_argument msg ->
    Printf.printf "  Out of bounds caught: %s\n" msg);

  print_endline "\n════════════════════════════════════════";
  print_endline "All matrix tests passed! ✓";
  print_endline "════════════════════════════════════════"
