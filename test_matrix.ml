(* test_matrix.ml — Tests for Matrix module *)
(* Run: ocaml test_matrix.ml *)

#use "test_framework.ml";;
#use "matrix.ml";;

let () =
  Printf.printf "=== Matrix Tests ===\n\n";

  let module M = FloatMatrix in

  (* --- Construction --- *)
  Printf.printf "  Construction:\n";

  let a = M.of_list [[1.0;2.0;3.0]; [4.0;5.0;6.0]; [7.0;8.0;10.0]] in
  let (r, c) = M.dims a in
  assert_equal ~msg:"dims rows" "3" (string_of_int r);
  assert_equal ~msg:"dims cols" "3" (string_of_int c);

  let z = M.zeros 2 3 in
  assert_true ~msg:"zeros is zero" (M.is_zero z);

  let id = M.identity 3 in
  assert_true ~msg:"identity is identity" (M.is_identity id);

  let diag = M.diagonal [2.0; 3.0; 5.0] in
  assert_true ~msg:"diagonal is diagonal" (M.is_diagonal diag);

  let rv = M.row_vector [1.0; 2.0; 3.0] in
  assert_equal ~msg:"row_vector rows" "1" (string_of_int (M.num_rows rv));
  assert_equal ~msg:"row_vector cols" "3" (string_of_int (M.num_cols rv));

  let cv = M.col_vector [4.0; 5.0] in
  assert_equal ~msg:"col_vector rows" "2" (string_of_int (M.num_rows cv));
  assert_equal ~msg:"col_vector cols" "1" (string_of_int (M.num_cols cv));

  assert_raises ~msg:"empty list" (fun () -> M.of_list []);
  assert_raises ~msg:"ragged rows" (fun () -> M.of_list [[1.0;2.0]; [3.0]]);

  (* --- Access --- *)
  Printf.printf "  Access:\n";

  assert_equal ~msg:"get (0,0)" "1" (Float_Num.to_string (M.get a 0 0));
  assert_equal ~msg:"get (1,2)" "6" (Float_Num.to_string (M.get a 1 2));
  assert_equal ~msg:"get (2,2)" "10" (Float_Num.to_string (M.get a 2 2));

  let a' = M.set a 0 0 99.0 in
  assert_equal ~msg:"set creates new matrix" "99" (Float_Num.to_string (M.get a' 0 0));
  assert_equal ~msg:"original unchanged" "1" (Float_Num.to_string (M.get a 0 0));

  assert_raises ~msg:"get out of bounds" (fun () -> M.get a 5 0);
  assert_raises ~msg:"set out of bounds" (fun () -> M.set a 0 5 0.0);

  let row1 = M.get_row a 1 in
  assert_equal ~msg:"get_row length" "3" (string_of_int (List.length row1));

  let col0 = M.get_col a 0 in
  assert_equal ~msg:"get_col length" "3" (string_of_int (List.length col0));

  (* --- Arithmetic --- *)
  Printf.printf "  Arithmetic:\n";

  let sum = M.add a a in
  assert_equal ~msg:"add (0,0)" "2" (Float_Num.to_string (M.get sum 0 0));

  let diff = M.sub sum a in
  assert_true ~msg:"sub reverses add" (M.equal diff a);

  let scaled = M.scale 2.0 a in
  assert_true ~msg:"scale 2x = add" (M.equal scaled sum);

  let halved = M.scale 0.5 scaled in
  assert_true ~msg:"scale 0.5 reverses 2x" (M.equal halved a);

  (* Multiplication *)
  let prod = M.mul a id in
  assert_true ~msg:"A * I = A" (M.equal prod a);

  let prod2 = M.mul id a in
  assert_true ~msg:"I * A = A" (M.equal prod2 a);

  (* Dot product via vectors *)
  let dot = M.mul (M.row_vector [1.0;2.0;3.0]) (M.col_vector [4.0;5.0;6.0]) in
  assert_equal ~msg:"dot product" "32" (Float_Num.to_string (M.get dot 0 0));

  (* Dimension mismatch *)
  assert_raises ~msg:"mul dim mismatch" (fun () -> M.mul (M.zeros 2 3) (M.zeros 4 2));
  assert_raises ~msg:"add dim mismatch" (fun () -> M.add (M.zeros 2 3) (M.zeros 3 2));

  (* Hadamard product *)
  let h = M.hadamard a a in
  assert_equal ~msg:"hadamard (0,0)" "1" (Float_Num.to_string (M.get h 0 0));
  assert_equal ~msg:"hadamard (1,1)" "25" (Float_Num.to_string (M.get h 1 1));

  (* --- Transpose --- *)
  Printf.printf "  Transpose:\n";

  let at = M.transpose a in
  assert_equal ~msg:"transpose dims" "3" (string_of_int (M.num_rows at));
  assert_equal ~msg:"transpose (0,1)=(1,0)" "2"
    (Float_Num.to_string (M.get (M.transpose a) 1 0));
  assert_true ~msg:"double transpose" (M.equal (M.transpose at) a);

  (* --- Determinant --- *)
  Printf.printf "  Determinant:\n";

  assert_equal ~msg:"det(I)" "1" (Float_Num.to_string (M.det id));

  let d = M.det a in
  assert_equal ~msg:"det(A)" "-3" (Float_Num.to_string d);

  let m2 = M.of_list [[3.0;7.0];[1.0;-4.0]] in
  assert_equal ~msg:"det 2x2" "-19" (Float_Num.to_string (M.det m2));

  let singular = M.of_list [[1.0;2.0];[2.0;4.0]] in
  assert_equal ~msg:"det singular" "0" (Float_Num.to_string (M.det singular));

  let m1x1 = M.of_list [[5.0]] in
  assert_equal ~msg:"det 1x1" "5" (Float_Num.to_string (M.det m1x1));

  (* --- Inverse --- *)
  Printf.printf "  Inverse:\n";

  let inv_id = M.inverse id in
  assert_true ~msg:"inverse(I) = I" (M.is_identity inv_id);

  let a_inv = M.inverse a in
  (* A * A^-1 should be approximately I *)
  let should_be_id = M.mul a a_inv in
  (* Check diagonal is ~1 and off-diagonal is ~0 *)
  for i = 0 to 2 do
    for j = 0 to 2 do
      let v = M.get should_be_id i j in
      let expected = if i = j then 1.0 else 0.0 in
      assert_true ~msg:(Printf.sprintf "A*A^-1 [%d,%d]" i j)
        (Float.abs (v -. expected) < 1e-8)
    done
  done;

  assert_raises ~msg:"inverse singular" (fun () -> M.inverse singular);

  (* --- Trace --- *)
  Printf.printf "  Trace:\n";

  let tr = M.trace a in
  assert_equal ~msg:"trace(A)" "16" (Float_Num.to_string tr);
  assert_equal ~msg:"trace(I)" "3" (Float_Num.to_string (M.trace id));

  (* --- Power --- *)
  Printf.printf "  Power:\n";

  let a0 = M.power a 0 in
  assert_true ~msg:"A^0 = I" (M.equal a0 id);

  let a1 = M.power a 1 in
  assert_true ~msg:"A^1 = A" (M.equal a1 a);

  let a2 = M.power a 2 in
  assert_true ~msg:"A^2 = A*A" (M.equal a2 (M.mul a a));

  let a3 = M.power a 3 in
  assert_true ~msg:"A^3 = A*A*A" (M.equal a3 (M.mul (M.mul a a) a));

  assert_raises ~msg:"negative power" (fun () -> M.power a (-1));

  (* --- Norms --- *)
  Printf.printf "  Norms:\n";

  let fn = M.frobenius_norm a in
  assert_true ~msg:"frobenius > 0" (fn > 0.0);

  let mn = M.max_norm a in
  assert_equal ~msg:"max norm" "10" (Float_Num.to_string mn);

  assert_true ~msg:"frobenius(zero) = 0" (M.frobenius_norm (M.zeros 3 3) = 0.0);

  (* --- Predicates --- *)
  Printf.printf "  Predicates:\n";

  assert_true ~msg:"is_square A" (M.is_square a);
  assert_true ~msg:"not square 2x3" (not (M.is_square (M.zeros 2 3)));

  let sym = M.of_list [[1.0;2.0;3.0]; [2.0;5.0;6.0]; [3.0;6.0;9.0]] in
  assert_true ~msg:"symmetric" (M.is_symmetric sym);
  assert_true ~msg:"not symmetric A" (not (M.is_symmetric a));

  let upper = M.of_list [[1.0;2.0;3.0]; [0.0;4.0;5.0]; [0.0;0.0;6.0]] in
  assert_true ~msg:"upper triangular" (M.is_upper_triangular upper);
  assert_true ~msg:"not lower" (not (M.is_lower_triangular upper));

  let lower = M.transpose upper in
  assert_true ~msg:"lower triangular" (M.is_lower_triangular lower);
  assert_true ~msg:"not upper" (not (M.is_upper_triangular lower));

  assert_true ~msg:"diagonal is upper" (M.is_upper_triangular diag);
  assert_true ~msg:"diagonal is lower" (M.is_lower_triangular diag);

  (* --- Fold & Map --- *)
  Printf.printf "  Fold & Map:\n";

  let total = M.fold Float_Num.add 0.0 a in
  assert_equal ~msg:"fold sum" "46" (Float_Num.to_string total);

  let negated = M.map Float_Num.neg a in
  assert_equal ~msg:"map neg (0,0)" "-1" (Float_Num.to_string (M.get negated 0 0));

  let added = M.map2 Float_Num.add a a in
  assert_true ~msg:"map2 = add" (M.equal added sum);

  (* --- Copy immutability --- *)
  Printf.printf "  Copy & immutability:\n";

  let original = M.of_list [[1.0;2.0];[3.0;4.0]] in
  let copied = M.copy original in
  assert_true ~msg:"copy equals original" (M.equal copied original);
  (* Modifying copy shouldn't affect original *)
  copied.data.(0).(0) <- 999.0;
  assert_equal ~msg:"original unchanged after copy mod" "1"
    (Float_Num.to_string (M.get original 0 0));

  (* --- Swap rows --- *)
  Printf.printf "  Swap rows:\n";

  let swapped = M.swap_rows a 0 2 in
  assert_equal ~msg:"swapped (0,0)" "7" (Float_Num.to_string (M.get swapped 0 0));
  assert_equal ~msg:"swapped (2,0)" "1" (Float_Num.to_string (M.get swapped 2 0));
  assert_equal ~msg:"original unchanged" "1" (Float_Num.to_string (M.get a 0 0));

  (* --- to_list / to_array roundtrip --- *)
  Printf.printf "  Serialization:\n";

  let lst = M.to_list a in
  assert_equal ~msg:"to_list length" "3" (string_of_int (List.length lst));
  let from_lst = M.of_list lst in
  assert_true ~msg:"list roundtrip" (M.equal from_lst a);

  let arr = M.to_array a in
  assert_equal ~msg:"to_array length" "3" (string_of_int (Array.length arr));
  let from_arr = M.of_array arr in
  assert_true ~msg:"array roundtrip" (M.equal from_arr a);

  (* --- Integer matrix --- *)
  Printf.printf "  Integer matrix:\n";

  let module IM = IntMatrix in

  let im = IM.of_list [[1;2];[3;4]] in
  assert_equal ~msg:"int det" "-2" (Int_Num.to_string (IM.det im));

  let im_id = IM.identity 2 in
  assert_true ~msg:"int identity" (IM.is_identity im_id);

  let im_prod = IM.mul im im_id in
  assert_true ~msg:"int A*I=A" (IM.equal im_prod im);

  let im_sum = IM.add im im in
  assert_equal ~msg:"int add (0,0)" "2" (Int_Num.to_string (IM.get im_sum 0 0));

  (* --- to_string --- *)
  Printf.printf "  Pretty printing:\n";

  let s = M.to_string id in
  assert_true ~msg:"to_string not empty" (String.length s > 0);
  assert_true ~msg:"to_string contains dimension" (String.length s > 10);

  test_summary ()
