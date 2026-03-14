(* ============================================================================
   tensor.ml - N-Dimensional Tensor Library

   A pure OCaml implementation of N-dimensional arrays (tensors) with:
   - Arbitrary-rank tensor creation (scalars, vectors, matrices, 3D+)
   - Shape validation and reshaping
   - Element-wise arithmetic with NumPy-style broadcasting
   - Slicing and indexing (single element, sub-tensor, range)
   - Reduction operations (sum, product, min, max, mean along axes)
   - Linear algebra basics (matmul, transpose, dot product)
   - Mapping, folding, and zipping over elements
   - Pretty-printing with shape-aware formatting
   - Stack, concatenate, split operations
   - Comparison and logical operations

   Concepts demonstrated:
   - Flat storage with stride-based indexing (row-major)
   - Broadcasting rules (NumPy semantics)
   - Recursive pretty-printing for arbitrary dimensions
   - Functional array programming in OCaml

   Usage:
     ocamlfind ocamlopt -package alcotest -linkpkg tensor.ml -o tensor && ./tensor
   Or:
     ocaml tensor.ml
   ============================================================================ *)

(* ========== Core Types ========== *)

type shape = int array
(** Shape of a tensor: [|2; 3; 4|] means 2x3x4 *)

type t = {
  data : float array;   (** Flat row-major storage *)
  shape : shape;        (** Dimensions *)
  strides : int array;  (** Strides for index computation *)
}
(** An N-dimensional tensor with flat storage and stride-based indexing. *)

exception Shape_mismatch of string
exception Index_out_of_bounds of string
exception Invalid_axis of string

(* ========== Internal Helpers ========== *)

let compute_strides (sh : shape) : int array =
  let n = Array.length sh in
  if n = 0 then [||]
  else begin
    let st = Array.make n 1 in
    for i = n - 2 downto 0 do
      st.(i) <- st.(i + 1) * sh.(i + 1)
    done;
    st
  end

let numel (sh : shape) : int =
  Array.fold_left ( * ) 1 sh

let flat_index (strides : int array) (indices : int array) : int =
  let n = Array.length strides in
  let idx = ref 0 in
  for i = 0 to n - 1 do
    idx := !idx + indices.(i) * strides.(i)
  done;
  !idx

let multi_index (sh : shape) (flat : int) : int array =
  let n = Array.length sh in
  let indices = Array.make n 0 in
  let rem = ref flat in
  for i = 0 to n - 1 do
    let stride = Array.fold_left ( * ) 1 (Array.sub sh (i + 1) (n - i - 1)) in
    if stride > 0 then begin
      indices.(i) <- !rem / stride;
      rem := !rem mod stride
    end
  done;
  indices

let validate_indices (sh : shape) (indices : int array) : unit =
  if Array.length indices <> Array.length sh then
    raise (Index_out_of_bounds
      (Printf.sprintf "Expected %d indices, got %d"
        (Array.length sh) (Array.length indices)));
  Array.iteri (fun i idx ->
    if idx < 0 || idx >= sh.(i) then
      raise (Index_out_of_bounds
        (Printf.sprintf "Index %d out of bounds for axis %d (size %d)"
          idx i sh.(i)))
  ) indices

let validate_axis (ndim : int) (axis : int) : unit =
  if axis < 0 || axis >= ndim then
    raise (Invalid_axis
      (Printf.sprintf "Axis %d out of range for %d-dimensional tensor"
        axis ndim))

(* ========== Creation ========== *)

let create (sh : shape) (init : float) : t =
  let n = numel sh in
  { data = Array.make n init;
    shape = Array.copy sh;
    strides = compute_strides sh }

let zeros (sh : shape) : t = create sh 0.0

let ones (sh : shape) : t = create sh 1.0

let full (sh : shape) (v : float) : t = create sh v

let scalar (v : float) : t =
  { data = [|v|]; shape = [||]; strides = [||] }

let of_array (sh : shape) (data : float array) : t =
  let expected = numel sh in
  if Array.length data <> expected then
    raise (Shape_mismatch
      (Printf.sprintf "Data has %d elements but shape requires %d"
        (Array.length data) expected));
  { data = Array.copy data;
    shape = Array.copy sh;
    strides = compute_strides sh }

let of_list (sh : shape) (data : float list) : t =
  of_array sh (Array.of_list data)

let init (sh : shape) (f : int array -> float) : t =
  let n = numel sh in
  let data = Array.make n 0.0 in
  for i = 0 to n - 1 do
    let idx = multi_index sh i in
    data.(i) <- f idx
  done;
  { data; shape = Array.copy sh; strides = compute_strides sh }

let linspace (start : float) (stop : float) (n : int) : t =
  if n < 1 then raise (Shape_mismatch "linspace requires n >= 1");
  let step = if n = 1 then 0.0 else (stop -. start) /. float_of_int (n - 1) in
  let data = Array.init n (fun i -> start +. float_of_int i *. step) in
  { data; shape = [|n|]; strides = [|1|] }

let arange (start : float) (stop : float) (step : float) : t =
  if step = 0.0 then raise (Shape_mismatch "arange step cannot be zero");
  let n = max 0 (int_of_float (Float.round ((stop -. start) /. step))) in
  let data = Array.init n (fun i -> start +. float_of_int i *. step) in
  { data; shape = [|n|]; strides = [|1|] }

let eye (n : int) : t =
  let data = Array.make (n * n) 0.0 in
  for i = 0 to n - 1 do
    data.(i * n + i) <- 1.0
  done;
  { data; shape = [|n; n|]; strides = compute_strides [|n; n|] }

let diag (v : t) : t =
  if Array.length v.shape <> 1 then
    raise (Shape_mismatch "diag expects a 1-D tensor");
  let n = v.shape.(0) in
  let data = Array.make (n * n) 0.0 in
  for i = 0 to n - 1 do
    data.(i * n + i) <- v.data.(i)
  done;
  { data; shape = [|n; n|]; strides = compute_strides [|n; n|] }

let rand (sh : shape) : t =
  let n = numel sh in
  let data = Array.init n (fun _ -> Random.float 1.0) in
  { data; shape = Array.copy sh; strides = compute_strides sh }

(* ========== Properties ========== *)

let shape (t : t) : shape = Array.copy t.shape

let ndim (t : t) : int = Array.length t.shape

let size (t : t) : int = Array.length t.data

let is_scalar (t : t) : bool = Array.length t.shape = 0

let is_vector (t : t) : bool = Array.length t.shape = 1

let is_matrix (t : t) : bool = Array.length t.shape = 2

(* ========== Indexing ========== *)

let get (t : t) (indices : int array) : float =
  validate_indices t.shape indices;
  t.data.(flat_index t.strides indices)

let set (t : t) (indices : int array) (v : float) : t =
  validate_indices t.shape indices;
  let data = Array.copy t.data in
  data.(flat_index t.strides indices) <- v;
  { t with data }

let get_flat (t : t) (i : int) : float =
  if i < 0 || i >= Array.length t.data then
    raise (Index_out_of_bounds (Printf.sprintf "Flat index %d out of bounds" i));
  t.data.(i)

(* ========== Slicing ========== *)

(** Extract a sub-tensor along the first axis *)
let slice_axis0 (t : t) (start : int) (stop : int) : t =
  if Array.length t.shape = 0 then
    raise (Shape_mismatch "Cannot slice a scalar");
  let dim0 = t.shape.(0) in
  let start = max 0 (min start dim0) in
  let stop = max start (min stop dim0) in
  let len = stop - start in
  let new_shape = Array.copy t.shape in
  new_shape.(0) <- len;
  let stride0 = t.strides.(0) in
  let n = numel new_shape in
  let data = Array.make n 0.0 in
  for i = 0 to n - 1 do
    data.(i) <- t.data.(start * stride0 + i)
  done;
  { data; shape = new_shape; strides = compute_strides new_shape }

(** Select a single index along a given axis, reducing rank by 1 *)
let select (t : t) (axis : int) (index : int) : t =
  let nd = Array.length t.shape in
  validate_axis nd axis;
  if index < 0 || index >= t.shape.(axis) then
    raise (Index_out_of_bounds
      (Printf.sprintf "Index %d out of bounds for axis %d (size %d)"
        index axis t.shape.(axis)));
  let new_shape = Array.init (nd - 1) (fun i ->
    if i < axis then t.shape.(i) else t.shape.(i + 1)
  ) in
  let n = numel new_shape in
  let data = Array.make n 0.0 in
  for i = 0 to n - 1 do
    let idx = multi_index new_shape i in
    let full_idx = Array.init nd (fun j ->
      if j < axis then idx.(j)
      else if j = axis then index
      else idx.(j - 1)
    ) in
    data.(i) <- t.data.(flat_index t.strides full_idx)
  done;
  { data; shape = new_shape; strides = compute_strides new_shape }

(* ========== Reshaping ========== *)

let reshape (t : t) (new_shape : shape) : t =
  let n1 = numel t.shape in
  let n2 = numel new_shape in
  if n1 <> n2 then
    raise (Shape_mismatch
      (Printf.sprintf "Cannot reshape: %d elements vs %d elements" n1 n2));
  { data = Array.copy t.data;
    shape = Array.copy new_shape;
    strides = compute_strides new_shape }

let flatten (t : t) : t =
  let n = Array.length t.data in
  { data = Array.copy t.data;
    shape = [|n|];
    strides = [|1|] }

let squeeze (t : t) : t =
  let new_shape = Array.of_list
    (Array.to_list t.shape |> List.filter (fun d -> d > 1)) in
  if Array.length new_shape = 0 && Array.length t.data = 1 then
    scalar t.data.(0)
  else
    { data = Array.copy t.data;
      shape = new_shape;
      strides = compute_strides new_shape }

let unsqueeze (t : t) (axis : int) : t =
  let nd = Array.length t.shape in
  if axis < 0 || axis > nd then
    raise (Invalid_axis
      (Printf.sprintf "Axis %d out of range for unsqueeze (ndim=%d)" axis nd));
  let new_shape = Array.init (nd + 1) (fun i ->
    if i < axis then t.shape.(i)
    else if i = axis then 1
    else t.shape.(i - 1)
  ) in
  { data = Array.copy t.data;
    shape = new_shape;
    strides = compute_strides new_shape }

(* ========== Broadcasting ========== *)

(** Compute the broadcast shape of two shapes (NumPy rules) *)
let broadcast_shape (s1 : shape) (s2 : shape) : shape =
  let n1 = Array.length s1 and n2 = Array.length s2 in
  let nd = max n1 n2 in
  Array.init nd (fun i ->
    let d1 = if i < nd - n1 then 1 else s1.(i - (nd - n1)) in
    let d2 = if i < nd - n2 then 1 else s2.(i - (nd - n2)) in
    if d1 = d2 then d1
    else if d1 = 1 then d2
    else if d2 = 1 then d1
    else raise (Shape_mismatch
      (Printf.sprintf "Cannot broadcast shapes: dimension %d has sizes %d and %d"
        i d1 d2))
  )

(** Map element index in broadcast result to source tensor index *)
let broadcast_index (src_shape : shape) (out_shape : shape) (out_idx : int array) : int array =
  let nd_src = Array.length src_shape in
  let nd_out = Array.length out_shape in
  let offset = nd_out - nd_src in
  Array.init nd_src (fun i ->
    if src_shape.(i) = 1 then 0
    else out_idx.(i + offset)
  )

(** Apply a binary operation with broadcasting *)
let broadcast_op (op : float -> float -> float) (a : t) (b : t) : t =
  let out_shape = broadcast_shape a.shape b.shape in
  let n = numel out_shape in
  let data = Array.make n 0.0 in
  for i = 0 to n - 1 do
    let idx = multi_index out_shape i in
    let ai = broadcast_index a.shape out_shape idx in
    let bi = broadcast_index b.shape out_shape idx in
    let va = a.data.(flat_index a.strides ai) in
    let vb = b.data.(flat_index b.strides bi) in
    data.(i) <- op va vb
  done;
  { data; shape = out_shape; strides = compute_strides out_shape }

(* ========== Element-wise Arithmetic ========== *)

let add = broadcast_op ( +. )
let sub = broadcast_op ( -. )
let mul = broadcast_op ( *. )
let div = broadcast_op ( /. )

let add_scalar (t : t) (s : float) : t =
  { t with data = Array.map (fun x -> x +. s) t.data }

let mul_scalar (t : t) (s : float) : t =
  { t with data = Array.map (fun x -> x *. s) t.data }

let neg (t : t) : t =
  { t with data = Array.map (fun x -> -. x) t.data }

let abs_t (t : t) : t =
  { t with data = Array.map Float.abs t.data }

let pow_scalar (t : t) (p : float) : t =
  { t with data = Array.map (fun x -> x ** p) t.data }

(* ========== Element-wise Math Functions ========== *)

let map (f : float -> float) (t : t) : t =
  { t with data = Array.map f t.data }

let map2 (f : float -> float -> float) (a : t) (b : t) : t =
  broadcast_op f a b

let exp_t (t : t) : t = map Stdlib.exp t
let log_t (t : t) : t = map Stdlib.log t
let sqrt_t (t : t) : t = map Stdlib.sqrt t
let sin_t (t : t) : t = map Stdlib.sin t
let cos_t (t : t) : t = map Stdlib.cos t
let tanh_t (t : t) : t = map Stdlib.tanh t

let relu (t : t) : t = map (fun x -> if x > 0.0 then x else 0.0) t

let sigmoid (t : t) : t =
  map (fun x -> 1.0 /. (1.0 +. Stdlib.exp (-. x))) t

let clip (t : t) (lo : float) (hi : float) : t =
  map (fun x -> max lo (min hi x)) t

(* ========== Reduction Operations ========== *)

(** Reduce along a single axis using an accumulator function *)
let reduce_axis (f : float -> float -> float) (init_val : float) (t : t) (axis : int) : t =
  let nd = Array.length t.shape in
  validate_axis nd axis;
  let new_shape = Array.init (nd - 1) (fun i ->
    if i < axis then t.shape.(i) else t.shape.(i + 1)
  ) in
  let n = numel new_shape in
  let data = Array.make (max 1 n) init_val in
  let new_strides = compute_strides new_shape in
  let total = numel t.shape in
  for i = 0 to total - 1 do
    let idx = multi_index t.shape i in
    let out_idx = Array.init (nd - 1) (fun j ->
      if j < axis then idx.(j) else idx.(j + 1)
    ) in
    let oi = if nd - 1 = 0 then 0 else flat_index new_strides out_idx in
    data.(oi) <- f data.(oi) t.data.(i)
  done;
  if Array.length new_shape = 0 then
    scalar data.(0)
  else
    { data; shape = new_shape; strides = compute_strides new_shape }

let sum_axis (t : t) (axis : int) : t =
  reduce_axis ( +. ) 0.0 t axis

let prod_axis (t : t) (axis : int) : t =
  reduce_axis ( *. ) 1.0 t axis

let max_axis (t : t) (axis : int) : t =
  reduce_axis max neg_infinity t axis

let min_axis (t : t) (axis : int) : t =
  reduce_axis min infinity t axis

(** Global reductions *)
let sum (t : t) : float =
  Array.fold_left ( +. ) 0.0 t.data

let prod (t : t) : float =
  Array.fold_left ( *. ) 1.0 t.data

let max_val (t : t) : float =
  Array.fold_left max neg_infinity t.data

let min_val (t : t) : float =
  Array.fold_left min infinity t.data

let mean (t : t) : float =
  sum t /. float_of_int (Array.length t.data)

let mean_axis (t : t) (axis : int) : t =
  let s = sum_axis t axis in
  let dim = float_of_int t.shape.(axis) in
  mul_scalar s (1.0 /. dim)

let variance (t : t) : float =
  let m = mean t in
  let n = float_of_int (Array.length t.data) in
  Array.fold_left (fun acc x -> acc +. (x -. m) ** 2.0) 0.0 t.data /. n

let std (t : t) : float =
  sqrt (variance t)

let argmax (t : t) : int =
  let best_i = ref 0 in
  let best_v = ref neg_infinity in
  Array.iteri (fun i v ->
    if v > !best_v then begin best_i := i; best_v := v end
  ) t.data;
  !best_i

let argmin (t : t) : int =
  let best_i = ref 0 in
  let best_v = ref infinity in
  Array.iteri (fun i v ->
    if v < !best_v then begin best_i := i; best_v := v end
  ) t.data;
  !best_i

(* ========== Comparison ========== *)

let equal (a : t) (b : t) : bool =
  a.shape = b.shape && a.data = b.data

let allclose ?(atol=1e-8) ?(rtol=1e-5) (a : t) (b : t) : bool =
  if a.shape <> b.shape then false
  else
    let n = Array.length a.data in
    let ok = ref true in
    let i = ref 0 in
    while !ok && !i < n do
      let diff = Float.abs (a.data.(!i) -. b.data.(!i)) in
      if diff > atol +. rtol *. Float.abs b.data.(!i) then
        ok := false;
      incr i
    done;
    !ok

(* ========== Matrix Operations ========== *)

(** Transpose a 2-D tensor *)
let transpose (t : t) : t =
  if Array.length t.shape <> 2 then
    raise (Shape_mismatch "transpose requires a 2-D tensor");
  let rows = t.shape.(0) and cols = t.shape.(1) in
  let data = Array.make (rows * cols) 0.0 in
  for i = 0 to rows - 1 do
    for j = 0 to cols - 1 do
      data.(j * rows + i) <- t.data.(i * cols + j)
    done
  done;
  { data; shape = [|cols; rows|]; strides = compute_strides [|cols; rows|] }

(** Matrix multiplication (2-D x 2-D) *)
let matmul (a : t) (b : t) : t =
  if Array.length a.shape <> 2 || Array.length b.shape <> 2 then
    raise (Shape_mismatch "matmul requires two 2-D tensors");
  let m = a.shape.(0) and k1 = a.shape.(1) in
  let k2 = b.shape.(0) and n = b.shape.(1) in
  if k1 <> k2 then
    raise (Shape_mismatch
      (Printf.sprintf "matmul inner dimensions mismatch: %d vs %d" k1 k2));
  let data = Array.make (m * n) 0.0 in
  for i = 0 to m - 1 do
    for j = 0 to n - 1 do
      let s = ref 0.0 in
      for p = 0 to k1 - 1 do
        s := !s +. a.data.(i * k1 + p) *. b.data.(p * n + j)
      done;
      data.(i * n + j) <- !s
    done
  done;
  { data; shape = [|m; n|]; strides = compute_strides [|m; n|] }

(** Dot product of two 1-D tensors *)
let dot (a : t) (b : t) : float =
  if Array.length a.shape <> 1 || Array.length b.shape <> 1 then
    raise (Shape_mismatch "dot requires two 1-D tensors");
  if a.shape.(0) <> b.shape.(0) then
    raise (Shape_mismatch "dot: vectors must have same length");
  let s = ref 0.0 in
  for i = 0 to a.shape.(0) - 1 do
    s := !s +. a.data.(i) *. b.data.(i)
  done;
  !s

(** Outer product of two 1-D tensors *)
let outer (a : t) (b : t) : t =
  if Array.length a.shape <> 1 || Array.length b.shape <> 1 then
    raise (Shape_mismatch "outer requires two 1-D tensors");
  let m = a.shape.(0) and n = b.shape.(0) in
  let data = Array.make (m * n) 0.0 in
  for i = 0 to m - 1 do
    for j = 0 to n - 1 do
      data.(i * n + j) <- a.data.(i) *. b.data.(j)
    done
  done;
  { data; shape = [|m; n|]; strides = compute_strides [|m; n|] }

(** Frobenius norm *)
let norm (t : t) : float =
  sqrt (Array.fold_left (fun acc x -> acc +. x *. x) 0.0 t.data)

(* ========== Stacking and Concatenation ========== *)

let concatenate (tensors : t list) (axis : int) : t =
  match tensors with
  | [] -> raise (Shape_mismatch "concatenate requires at least one tensor")
  | first :: _ ->
    let nd = Array.length first.shape in
    validate_axis nd axis;
    List.iter (fun other ->
      if Array.length other.shape <> nd then
        raise (Shape_mismatch "All tensors must have same number of dimensions");
      Array.iteri (fun i d ->
        if i <> axis && d <> first.shape.(i) then
          raise (Shape_mismatch
            (Printf.sprintf "Shape mismatch at axis %d: %d vs %d" i d first.shape.(i)))
      ) other.shape
    ) tensors;
    let total_axis = List.fold_left (fun acc t -> acc + t.shape.(axis)) 0 tensors in
    let new_shape = Array.copy first.shape in
    new_shape.(axis) <- total_axis;
    let n = numel new_shape in
    let data = Array.make n 0.0 in
    let new_strides = compute_strides new_shape in
    let axis_offset = ref 0 in
    List.iter (fun t ->
      let total_t = numel t.shape in
      for i = 0 to total_t - 1 do
        let idx = multi_index t.shape i in
        let out_idx = Array.copy idx in
        out_idx.(axis) <- idx.(axis) + !axis_offset;
        data.(flat_index new_strides out_idx) <- t.data.(i)
      done;
      axis_offset := !axis_offset + t.shape.(axis)
    ) tensors;
    { data; shape = new_shape; strides = new_strides }

let stack (tensors : t list) (axis : int) : t =
  let expanded = List.map (fun t -> unsqueeze t axis) tensors in
  concatenate expanded axis

let split (t : t) (n : int) (axis : int) : t list =
  let nd = Array.length t.shape in
  validate_axis nd axis;
  let dim = t.shape.(axis) in
  if dim mod n <> 0 then
    raise (Shape_mismatch
      (Printf.sprintf "Cannot split dimension %d into %d equal parts" dim n));
  let chunk_size = dim / n in
  List.init n (fun c ->
    let new_shape = Array.copy t.shape in
    new_shape.(axis) <- chunk_size;
    let chunk_n = numel new_shape in
    let data = Array.make chunk_n 0.0 in
    let new_strides = compute_strides new_shape in
    for i = 0 to chunk_n - 1 do
      let idx = multi_index new_shape i in
      let src_idx = Array.copy idx in
      src_idx.(axis) <- idx.(axis) + c * chunk_size;
      data.(flat_index new_strides idx) <- t.data.(flat_index t.strides src_idx)
    done;
    { data; shape = new_shape; strides = new_strides }
  )

(* ========== Folding ========== *)

let fold_left (f : 'a -> float -> 'a) (init : 'a) (t : t) : 'a =
  Array.fold_left f init t.data

let iter (f : float -> unit) (t : t) : unit =
  Array.iter f t.data

let iteri (f : int array -> float -> unit) (t : t) : unit =
  Array.iteri (fun i v ->
    let idx = multi_index t.shape i in
    f idx v
  ) t.data

(* ========== Copying ========== *)

let copy (t : t) : t =
  { data = Array.copy t.data;
    shape = Array.copy t.shape;
    strides = Array.copy t.strides }

let to_array (t : t) : float array =
  Array.copy t.data

let to_list (t : t) : float list =
  Array.to_list t.data

(* ========== Pretty Printing ========== *)

let format_float (v : float) : string =
  if Float.is_integer v && Float.abs v < 1e15 then
    Printf.sprintf "%.0f" v
  else
    Printf.sprintf "%.4g" v

let rec pp_recursive (data : float array) (sh : shape) (offset : int)
    (dim : int) : string =
  let nd = Array.length sh in
  if dim = nd then
    format_float data.(offset)
  else if dim = nd - 1 then begin
    let n = sh.(dim) in
    let parts = Array.init n (fun i -> format_float data.(offset + i)) in
    "[" ^ String.concat ", " (Array.to_list parts) ^ "]"
  end else begin
    let n = sh.(dim) in
    let stride = Array.fold_left ( * ) 1
      (Array.sub sh (dim + 1) (nd - dim - 1)) in
    let parts = Array.init n (fun i ->
      pp_recursive data sh (offset + i * stride) (dim + 1)
    ) in
    let inner = String.concat ",\n " (Array.to_list parts) in
    "[" ^ inner ^ "]"
  end

let to_string (t : t) : string =
  let shape_str =
    "[" ^ String.concat ", " (Array.to_list (Array.map string_of_int t.shape)) ^ "]"
  in
  if Array.length t.shape = 0 then
    Printf.sprintf "tensor(%s)" (format_float t.data.(0))
  else
    Printf.sprintf "tensor(%s, shape=%s)"
      (pp_recursive t.data t.shape 0 0)
      shape_str

let print (t : t) : unit =
  print_endline (to_string t)


(* ============================================================================
   TESTS
   ============================================================================ *)

let () =
  let open Alcotest in

  let float_eps = 1e-10 in

  let check_shape msg expected (t : t) =
    check (array int) msg expected t.shape
  in

  let check_data msg expected (t : t) =
    let n = Array.length expected in
    if Array.length t.data <> n then
      fail (Printf.sprintf "%s: expected %d elements, got %d" msg n (Array.length t.data));
    Array.iteri (fun i e ->
      let a = t.data.(i) in
      if Float.abs (a -. e) > float_eps then
        fail (Printf.sprintf "%s[%d]: expected %g, got %g" msg i e a)
    ) expected
  in

  let test_zeros () =
    let t = zeros [|2; 3|] in
    check_shape "shape" [|2; 3|] t;
    check_data "data" (Array.make 6 0.0) t
  in

  let test_ones () =
    let t = ones [|3|] in
    check_shape "shape" [|3|] t;
    check_data "data" [|1.0; 1.0; 1.0|] t
  in

  let test_full () =
    let t = full [|2; 2|] 5.0 in
    check_data "data" [|5.0; 5.0; 5.0; 5.0|] t
  in

  let test_scalar () =
    let t = scalar 42.0 in
    check int "ndim" 0 (ndim t);
    check_data "data" [|42.0|] t;
    check bool "is_scalar" true (is_scalar t)
  in

  let test_of_array () =
    let t = of_array [|2; 3|] [|1.;2.;3.;4.;5.;6.|] in
    check_shape "shape" [|2; 3|] t;
    check (float float_eps) "get" 5.0 (get t [|1; 1|])
  in

  let test_of_list () =
    let t = of_list [|3|] [1.0; 2.0; 3.0] in
    check_data "data" [|1.0; 2.0; 3.0|] t
  in

  let test_init () =
    let t = init [|2; 2|] (fun idx ->
      float_of_int (idx.(0) * 10 + idx.(1))
    ) in
    check_data "data" [|0.; 1.; 10.; 11.|] t
  in

  let test_linspace () =
    let t = linspace 0.0 1.0 5 in
    check_shape "shape" [|5|] t;
    check (float float_eps) "first" 0.0 t.data.(0);
    check (float float_eps) "last" 1.0 t.data.(4);
    check (float float_eps) "mid" 0.5 t.data.(2)
  in

  let test_arange () =
    let t = arange 0.0 5.0 1.0 in
    check_shape "shape" [|5|] t;
    check_data "data" [|0.;1.;2.;3.;4.|] t
  in

  let test_eye () =
    let t = eye 3 in
    check_shape "shape" [|3;3|] t;
    check_data "data" [|1.;0.;0.; 0.;1.;0.; 0.;0.;1.|] t
  in

  let test_diag () =
    let v = of_array [|3|] [|2.;3.;4.|] in
    let d = diag v in
    check_shape "shape" [|3;3|] d;
    check_data "data" [|2.;0.;0.; 0.;3.;0.; 0.;0.;4.|] d
  in

  let test_properties () =
    let t = zeros [|2; 3; 4|] in
    check int "ndim" 3 (ndim t);
    check int "size" 24 (size t);
    check bool "is_scalar" false (is_scalar t);
    check bool "is_vector" false (is_vector t);
    check bool "is_matrix" false (is_matrix t)
  in

  let test_get_set () =
    let t = zeros [|2; 3|] in
    let t2 = set t [|1; 2|] 7.0 in
    check (float float_eps) "get" 7.0 (get t2 [|1; 2|]);
    check (float float_eps) "original" 0.0 (get t [|1; 2|])
  in

  let test_index_bounds () =
    let t = zeros [|2; 3|] in
    check_raises "oob" (Index_out_of_bounds "Index 5 out of bounds for axis 1 (size 3)")
      (fun () -> ignore (get t [|0; 5|]))
  in

  let test_slice_axis0 () =
    let t = of_array [|4; 2|] [|1.;2.;3.;4.;5.;6.;7.;8.|] in
    let s = slice_axis0 t 1 3 in
    check_shape "shape" [|2; 2|] s;
    check_data "data" [|3.;4.;5.;6.|] s
  in

  let test_select () =
    let t = of_array [|2; 3|] [|1.;2.;3.;4.;5.;6.|] in
    let row = select t 0 1 in
    check_shape "shape" [|3|] row;
    check_data "data" [|4.;5.;6.|] row;
    let col = select t 1 0 in
    check_shape "col shape" [|2|] col;
    check_data "col data" [|1.;4.|] col
  in

  let test_reshape () =
    let t = of_array [|2; 3|] [|1.;2.;3.;4.;5.;6.|] in
    let r = reshape t [|3; 2|] in
    check_shape "shape" [|3; 2|] r;
    check (float float_eps) "data preserved" 4.0 (get r [|1; 1|])
  in

  let test_reshape_mismatch () =
    let t = zeros [|2; 3|] in
    check_raises "mismatch" (Shape_mismatch "Cannot reshape: 6 elements vs 8 elements")
      (fun () -> ignore (reshape t [|2; 4|]))
  in

  let test_flatten () =
    let t = of_array [|2; 3|] [|1.;2.;3.;4.;5.;6.|] in
    let f = flatten t in
    check_shape "shape" [|6|] f;
    check_data "data" [|1.;2.;3.;4.;5.;6.|] f
  in

  let test_squeeze () =
    let t = of_array [|1; 3; 1|] [|1.;2.;3.|] in
    let s = squeeze t in
    check_shape "shape" [|3|] s
  in

  let test_unsqueeze () =
    let t = of_array [|3|] [|1.;2.;3.|] in
    let u = unsqueeze t 0 in
    check_shape "shape" [|1; 3|] u;
    let u2 = unsqueeze t 1 in
    check_shape "shape2" [|3; 1|] u2
  in

  let test_broadcast_add () =
    let a = of_array [|2; 3|] [|1.;2.;3.;4.;5.;6.|] in
    let b = of_array [|3|] [|10.;20.;30.|] in
    let c = add a b in
    check_shape "shape" [|2; 3|] c;
    check_data "data" [|11.;22.;33.;14.;25.;36.|] c
  in

  let test_broadcast_scalar () =
    let a = of_array [|2; 2|] [|1.;2.;3.;4.|] in
    let b = scalar 10.0 in
    let c = mul a b in
    check_shape "shape" [|2; 2|] c;
    check_data "data" [|10.;20.;30.;40.|] c
  in

  let test_broadcast_column_row () =
    let col = of_array [|3; 1|] [|1.;2.;3.|] in
    let row = of_array [|1; 3|] [|10.;20.;30.|] in
    let c = add col row in
    check_shape "shape" [|3; 3|] c;
    check_data "data" [|11.;21.;31.;12.;22.;32.;13.;23.;33.|] c
  in

  let test_broadcast_mismatch () =
    let a = of_array [|2; 3|] [|1.;2.;3.;4.;5.;6.|] in
    let b = of_array [|2|] [|1.;2.|] in
    check_raises "mismatch"
      (Shape_mismatch "Cannot broadcast shapes: dimension 1 has sizes 3 and 2")
      (fun () -> ignore (add a b))
  in

  let test_sub () =
    let a = of_array [|3|] [|5.;8.;3.|] in
    let b = of_array [|3|] [|1.;2.;3.|] in
    let c = sub a b in
    check_data "data" [|4.;6.;0.|] c
  in

  let test_div () =
    let a = of_array [|3|] [|10.;20.;30.|] in
    let b = of_array [|3|] [|2.;5.;10.|] in
    let c = div a b in
    check_data "data" [|5.;4.;3.|] c
  in

  let test_neg () =
    let t = of_array [|3|] [|1.;-2.;3.|] in
    let n = neg t in
    check_data "data" [|-1.;2.;-3.|] n
  in

  let test_abs () =
    let t = of_array [|3|] [|-1.;2.;-3.|] in
    check_data "data" [|1.;2.;3.|] (abs_t t)
  in

  let test_pow_scalar () =
    let t = of_array [|3|] [|2.;3.;4.|] in
    let p = pow_scalar t 2.0 in
    check_data "data" [|4.;9.;16.|] p
  in

  let test_add_scalar () =
    let t = of_array [|3|] [|1.;2.;3.|] in
    check_data "data" [|11.;12.;13.|] (add_scalar t 10.0)
  in

  let test_mul_scalar () =
    let t = of_array [|3|] [|1.;2.;3.|] in
    check_data "data" [|3.;6.;9.|] (mul_scalar t 3.0)
  in

  let test_relu () =
    let t = of_array [|5|] [|-2.;-1.;0.;1.;2.|] in
    check_data "data" [|0.;0.;0.;1.;2.|] (relu t)
  in

  let test_sigmoid () =
    let t = scalar 0.0 in
    let s = sigmoid t in
    check (float 1e-6) "sigmoid(0)" 0.5 s.data.(0)
  in

  let test_clip () =
    let t = of_array [|5|] [|-2.;0.;3.;5.;10.|] in
    check_data "data" [|0.;0.;3.;5.;5.|] (clip t 0.0 5.0)
  in

  let test_sum () =
    let t = of_array [|3|] [|1.;2.;3.|] in
    check (float float_eps) "sum" 6.0 (sum t)
  in

  let test_prod () =
    let t = of_array [|3|] [|2.;3.;4.|] in
    check (float float_eps) "prod" 24.0 (prod t)
  in

  let test_max_min () =
    let t = of_array [|5|] [|3.;1.;4.;1.;5.|] in
    check (float float_eps) "max" 5.0 (max_val t);
    check (float float_eps) "min" 1.0 (min_val t)
  in

  let test_mean () =
    let t = of_array [|4|] [|2.;4.;6.;8.|] in
    check (float float_eps) "mean" 5.0 (mean t)
  in

  let test_variance () =
    let t = of_array [|4|] [|2.;4.;6.;8.|] in
    check (float float_eps) "var" 5.0 (variance t)
  in

  let test_std () =
    let t = of_array [|4|] [|2.;4.;6.;8.|] in
    check (float 1e-6) "std" (sqrt 5.0) (std t)
  in

  let test_argmax_argmin () =
    let t = of_array [|5|] [|3.;1.;4.;1.;5.|] in
    check int "argmax" 4 (argmax t);
    check int "argmin" 1 (argmin t)
  in

  let test_sum_axis () =
    let t = of_array [|2; 3|] [|1.;2.;3.;4.;5.;6.|] in
    let s0 = sum_axis t 0 in
    check_shape "shape" [|3|] s0;
    check_data "data" [|5.;7.;9.|] s0;
    let s1 = sum_axis t 1 in
    check_shape "shape" [|2|] s1;
    check_data "data" [|6.;15.|] s1
  in

  let test_max_axis () =
    let t = of_array [|2; 3|] [|1.;5.;3.;4.;2.;6.|] in
    let m = max_axis t 0 in
    check_data "data" [|4.;5.;6.|] m
  in

  let test_mean_axis () =
    let t = of_array [|2; 3|] [|1.;2.;3.;4.;5.;6.|] in
    let m = mean_axis t 0 in
    check_data "data" [|2.5;3.5;4.5|] m
  in

  let test_equal () =
    let a = of_array [|2|] [|1.;2.|] in
    let b = of_array [|2|] [|1.;2.|] in
    check bool "equal" true (equal a b);
    let c = of_array [|2|] [|1.;3.|] in
    check bool "not equal" false (equal a c)
  in

  let test_allclose () =
    let a = of_array [|2|] [|1.0; 2.0|] in
    let b = of_array [|2|] [|1.0 +. 1e-10; 2.0 -. 1e-10|] in
    check bool "close" true (allclose a b);
    let c = of_array [|2|] [|1.0; 3.0|] in
    check bool "not close" false (allclose a c)
  in

  let test_transpose () =
    let t = of_array [|2; 3|] [|1.;2.;3.;4.;5.;6.|] in
    let tr = transpose t in
    check_shape "shape" [|3; 2|] tr;
    check_data "data" [|1.;4.;2.;5.;3.;6.|] tr
  in

  let test_matmul () =
    let a = of_array [|2; 3|] [|1.;2.;3.;4.;5.;6.|] in
    let b = of_array [|3; 2|] [|7.;8.;9.;10.;11.;12.|] in
    let c = matmul a b in
    check_shape "shape" [|2; 2|] c;
    check_data "data" [|58.;64.;139.;154.|] c
  in

  let test_matmul_identity () =
    let a = of_array [|2; 2|] [|1.;2.;3.;4.|] in
    let id = eye 2 in
    check bool "A*I=A" true (equal (matmul a id) a)
  in

  let test_dot () =
    let a = of_array [|3|] [|1.;2.;3.|] in
    let b = of_array [|3|] [|4.;5.;6.|] in
    check (float float_eps) "dot" 32.0 (dot a b)
  in

  let test_outer () =
    let a = of_array [|2|] [|1.;2.|] in
    let b = of_array [|3|] [|3.;4.;5.|] in
    let o = outer a b in
    check_shape "shape" [|2; 3|] o;
    check_data "data" [|3.;4.;5.;6.;8.;10.|] o
  in

  let test_norm () =
    let t = of_array [|3|] [|3.;4.;0.|] in
    check (float float_eps) "norm" 5.0 (norm t)
  in

  let test_concatenate () =
    let a = of_array [|2; 2|] [|1.;2.;3.;4.|] in
    let b = of_array [|1; 2|] [|5.;6.|] in
    let c = concatenate [a; b] 0 in
    check_shape "shape" [|3; 2|] c;
    check_data "data" [|1.;2.;3.;4.;5.;6.|] c
  in

  let test_concatenate_axis1 () =
    let a = of_array [|2; 2|] [|1.;2.;3.;4.|] in
    let b = of_array [|2; 1|] [|5.;6.|] in
    let c = concatenate [a; b] 1 in
    check_shape "shape" [|2; 3|] c;
    check_data "data" [|1.;2.;5.;3.;4.;6.|] c
  in

  let test_stack () =
    let a = of_array [|3|] [|1.;2.;3.|] in
    let b = of_array [|3|] [|4.;5.;6.|] in
    let s = stack [a; b] 0 in
    check_shape "shape" [|2; 3|] s;
    check_data "data" [|1.;2.;3.;4.;5.;6.|] s
  in

  let test_split () =
    let t = of_array [|4; 2|] [|1.;2.;3.;4.;5.;6.;7.;8.|] in
    let parts = split t 2 0 in
    check int "count" 2 (List.length parts);
    check_shape "part0 shape" [|2; 2|] (List.nth parts 0);
    check_data "part0 data" [|1.;2.;3.;4.|] (List.nth parts 0);
    check_data "part1 data" [|5.;6.;7.;8.|] (List.nth parts 1)
  in

  let test_3d_create () =
    let t = init [|2; 3; 4|] (fun idx ->
      float_of_int (idx.(0) * 100 + idx.(1) * 10 + idx.(2))
    ) in
    check int "size" 24 (size t);
    check (float float_eps) "get" 123.0 (get t [|1; 2; 3|]);
    check (float float_eps) "get2" 10.0 (get t [|0; 1; 0|])
  in

  let test_3d_sum_axis () =
    let t = ones [|2; 3; 4|] in
    let s = sum_axis t 0 in
    check_shape "shape" [|3; 4|] s;
    check (float float_eps) "all twos" 2.0 s.data.(0);
    let s1 = sum_axis t 1 in
    check_shape "shape1" [|2; 4|] s1;
    check (float float_eps) "all threes" 3.0 s1.data.(0);
    let s2 = sum_axis t 2 in
    check_shape "shape2" [|2; 3|] s2;
    check (float float_eps) "all fours" 4.0 s2.data.(0)
  in

  let test_3d_broadcasting () =
    let a = ones [|2; 3; 4|] in
    let b = of_array [|4|] [|1.;2.;3.;4.|] in
    let c = add a b in
    check_shape "shape" [|2; 3; 4|] c;
    check (float float_eps) "first" 2.0 (get c [|0; 0; 0|]);
    check (float float_eps) "last" 5.0 (get c [|0; 0; 3|])
  in

  let test_copy () =
    let t = of_array [|3|] [|1.;2.;3.|] in
    let c = copy t in
    check bool "equal" true (equal t c);
    let _ = set c [|0|] 99.0 in
    check (float float_eps) "original" 1.0 (get t [|0|])
  in

  let test_to_array_list () =
    let t = of_array [|3|] [|1.;2.;3.|] in
    check (array (float float_eps)) "to_array" [|1.;2.;3.|] (to_array t);
    check (list (float float_eps)) "to_list" [1.;2.;3.] (to_list t)
  in

  let test_to_string () =
    let t = of_array [|2; 2|] [|1.;2.;3.;4.|] in
    let s = to_string t in
    check bool "has tensor" true (String.length s > 0);
    check bool "has shape" true
      (try ignore (String.sub s 0 1); true with _ -> false)
  in

  let test_to_string_scalar () =
    let t = scalar 3.14 in
    check string "scalar" "tensor(3.14)" (to_string t)
  in

  run "Tensor" [
    "creation", [
      test_case "zeros" `Quick test_zeros;
      test_case "ones" `Quick test_ones;
      test_case "full" `Quick test_full;
      test_case "scalar" `Quick test_scalar;
      test_case "of_array" `Quick test_of_array;
      test_case "of_list" `Quick test_of_list;
      test_case "init" `Quick test_init;
      test_case "linspace" `Quick test_linspace;
      test_case "arange" `Quick test_arange;
      test_case "eye" `Quick test_eye;
      test_case "diag" `Quick test_diag;
    ];
    "properties", [
      test_case "ndim/size/is_*" `Quick test_properties;
    ];
    "indexing", [
      test_case "get/set" `Quick test_get_set;
      test_case "index bounds" `Quick test_index_bounds;
    ];
    "slicing", [
      test_case "slice_axis0" `Quick test_slice_axis0;
      test_case "select" `Quick test_select;
    ];
    "reshape", [
      test_case "reshape" `Quick test_reshape;
      test_case "reshape mismatch" `Quick test_reshape_mismatch;
      test_case "flatten" `Quick test_flatten;
      test_case "squeeze" `Quick test_squeeze;
      test_case "unsqueeze" `Quick test_unsqueeze;
    ];
    "broadcast", [
      test_case "add 2d+1d" `Quick test_broadcast_add;
      test_case "mul scalar" `Quick test_broadcast_scalar;
      test_case "column+row" `Quick test_broadcast_column_row;
      test_case "mismatch" `Quick test_broadcast_mismatch;
    ];
    "arithmetic", [
      test_case "sub" `Quick test_sub;
      test_case "div" `Quick test_div;
      test_case "neg" `Quick test_neg;
      test_case "abs" `Quick test_abs;
      test_case "pow_scalar" `Quick test_pow_scalar;
      test_case "add_scalar" `Quick test_add_scalar;
      test_case "mul_scalar" `Quick test_mul_scalar;
    ];
    "math", [
      test_case "relu" `Quick test_relu;
      test_case "sigmoid" `Quick test_sigmoid;
      test_case "clip" `Quick test_clip;
    ];
    "reductions", [
      test_case "sum" `Quick test_sum;
      test_case "prod" `Quick test_prod;
      test_case "max/min" `Quick test_max_min;
      test_case "mean" `Quick test_mean;
      test_case "variance" `Quick test_variance;
      test_case "std" `Quick test_std;
      test_case "argmax/argmin" `Quick test_argmax_argmin;
      test_case "sum_axis" `Quick test_sum_axis;
      test_case "max_axis" `Quick test_max_axis;
      test_case "mean_axis" `Quick test_mean_axis;
    ];
    "comparison", [
      test_case "equal" `Quick test_equal;
      test_case "allclose" `Quick test_allclose;
    ];
    "matrix", [
      test_case "transpose" `Quick test_transpose;
      test_case "matmul" `Quick test_matmul;
      test_case "matmul identity" `Quick test_matmul_identity;
      test_case "dot" `Quick test_dot;
      test_case "outer" `Quick test_outer;
      test_case "norm" `Quick test_norm;
    ];
    "stack_concat", [
      test_case "concatenate axis0" `Quick test_concatenate;
      test_case "concatenate axis1" `Quick test_concatenate_axis1;
      test_case "stack" `Quick test_stack;
      test_case "split" `Quick test_split;
    ];
    "nd", [
      test_case "3d create+get" `Quick test_3d_create;
      test_case "3d sum_axis" `Quick test_3d_sum_axis;
      test_case "3d broadcast" `Quick test_3d_broadcasting;
    ];
    "copy_convert", [
      test_case "copy" `Quick test_copy;
      test_case "to_array/list" `Quick test_to_array_list;
    ];
    "printing", [
      test_case "to_string matrix" `Quick test_to_string;
      test_case "to_string scalar" `Quick test_to_string_scalar;
    ];
  ]
