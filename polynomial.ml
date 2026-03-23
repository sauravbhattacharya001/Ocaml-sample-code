(* ========================================================================== *)
(*  Polynomial Arithmetic                                                     *)
(*  ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~  *)
(*  A comprehensive polynomial library demonstrating:                         *)
(*  - Sparse representation using sorted coefficient lists                    *)
(*  - Arithmetic: add, subtract, multiply, power, compose                    *)
(*  - Calculus: differentiate, integrate, evaluate                           *)
(*  - Root finding: Newton's method, rational root theorem                   *)
(*  - GCD via pseudo-remainder algorithm                                      *)
(*  - Pretty printing with Unicode superscripts                              *)
(*  - Polynomial interpolation (Lagrange)                                     *)
(*                                                                            *)
(*  Concepts: algebraic data types, pattern matching, higher-order functions, *)
(*  tail recursion, numerical methods                                         *)
(* ========================================================================== *)

(* A term is (coefficient, exponent). A polynomial is a sorted list of terms
   with descending exponents and no zero coefficients. *)
type term = { coeff : float; exp : int }
type poly = term list

(* ---- Construction & Normalization ---- *)

let zero : poly = []
let one : poly = [{ coeff = 1.0; exp = 0 }]
let monomial c e : poly = if c = 0.0 then [] else [{ coeff = c; exp = e }]
let constant c : poly = monomial c 0
let x : poly = monomial 1.0 1

(* Normalize: combine like terms, remove zeros, sort descending *)
let normalize (p : poly) : poly =
  let tbl = Hashtbl.create 16 in
  List.iter (fun t ->
    let prev = try Hashtbl.find tbl t.exp with Not_found -> 0.0 in
    Hashtbl.replace tbl t.exp (prev +. t.coeff)
  ) p;
  Hashtbl.fold (fun e c acc ->
    if abs_float c < 1e-15 then acc
    else { coeff = c; exp = e } :: acc
  ) tbl []
  |> List.sort (fun a b -> compare b.exp a.exp)

(* ---- Degree & Leading Coefficient ---- *)

let degree (p : poly) : int =
  match p with [] -> -1 | t :: _ -> t.exp

let leading_coeff (p : poly) : float =
  match p with [] -> 0.0 | t :: _ -> t.coeff

let is_zero (p : poly) : bool = p = []

(* ---- Arithmetic Operations ---- *)

let add (p1 : poly) (p2 : poly) : poly =
  normalize (p1 @ p2)

let negate (p : poly) : poly =
  List.map (fun t -> { t with coeff = -. t.coeff }) p

let sub (p1 : poly) (p2 : poly) : poly =
  add p1 (negate p2)

let scale (c : float) (p : poly) : poly =
  if c = 0.0 then zero
  else normalize (List.map (fun t -> { coeff = t.coeff *. c; exp = t.exp }) p)

let shift (n : int) (p : poly) : poly =
  List.map (fun t -> { t with exp = t.exp + n }) p

let mul (p1 : poly) (p2 : poly) : poly =
  let terms = List.concat_map (fun t1 ->
    List.map (fun t2 ->
      { coeff = t1.coeff *. t2.coeff; exp = t1.exp + t2.exp }
    ) p2
  ) p1 in
  normalize terms

let rec pow (p : poly) (n : int) : poly =
  if n < 0 then invalid_arg "pow: negative exponent"
  else if n = 0 then one
  else if n = 1 then p
  else
    let half = pow p (n / 2) in
    let sq = mul half half in
    if n mod 2 = 0 then sq else mul sq p

(* ---- Evaluation ---- *)

(* Horner's method for efficient evaluation *)
let eval (p : poly) (x_val : float) : float =
  if is_zero p then 0.0
  else
    let d = degree p in
    (* Build coefficient array *)
    let coeffs = Array.make (d + 1) 0.0 in
    List.iter (fun t -> coeffs.(t.exp) <- t.coeff) p;
    let result = ref 0.0 in
    for i = d downto 0 do
      result := !result *. x_val +. coeffs.(i)
    done;
    !result

(* ---- Calculus ---- *)

let differentiate (p : poly) : poly =
  normalize (List.filter_map (fun t ->
    if t.exp = 0 then None
    else Some { coeff = t.coeff *. float_of_int t.exp; exp = t.exp - 1 }
  ) p)

(* Indefinite integral (constant of integration = 0) *)
let integrate (p : poly) : poly =
  normalize (List.map (fun t ->
    { coeff = t.coeff /. float_of_int (t.exp + 1); exp = t.exp + 1 }
  ) p)

(* Definite integral from a to b *)
let definite_integral (p : poly) (a : float) (b : float) : float =
  let anti = integrate p in
  eval anti b -. eval anti a

(* ---- Composition: p(q(x)) ---- *)

let compose (p : poly) (q : poly) : poly =
  List.fold_left (fun acc t ->
    add acc (scale t.coeff (pow q t.exp))
  ) zero p

(* ---- Division ---- *)

(* Polynomial long division: returns (quotient, remainder) *)
let divmod (p1 : poly) (p2 : poly) : poly * poly =
  if is_zero p2 then invalid_arg "divmod: division by zero polynomial";
  let rec aux q r =
    if is_zero r || degree r < degree p2 then (q, r)
    else
      let c = leading_coeff r /. leading_coeff p2 in
      let e = degree r - degree p2 in
      let t = monomial c e in
      let q' = add q t in
      let r' = sub r (mul t p2) in
      aux q' r'
  in
  aux zero p1

let div (p1 : poly) (p2 : poly) : poly = fst (divmod p1 p2)
let modulo (p1 : poly) (p2 : poly) : poly = snd (divmod p1 p2)

(* ---- GCD via Euclidean Algorithm ---- *)

let rec gcd (p1 : poly) (p2 : poly) : poly =
  if is_zero p2 then
    (* Make monic *)
    let lc = leading_coeff p1 in
    if lc = 0.0 then zero else scale (1.0 /. lc) p1
  else
    gcd p2 (modulo p1 p2)

(* ---- Root Finding ---- *)

(* Newton's method *)
let newton_root ?(max_iter = 100) ?(tol = 1e-10) (p : poly) (x0 : float) : float option =
  let p' = differentiate p in
  let rec iterate x n =
    if n >= max_iter then None
    else
      let fx = eval p x in
      if abs_float fx < tol then Some x
      else
        let fpx = eval p' x in
        if abs_float fpx < 1e-15 then None  (* derivative too small *)
        else iterate (x -. fx /. fpx) (n + 1)
  in
  iterate x0 0

(* Find all real roots by deflation *)
let find_roots ?(tol = 1e-8) (p : poly) : float list =
  let rec aux poly_remaining roots =
    if degree poly_remaining <= 0 then roots
    else
      (* Try several starting points *)
      let starts = [-10.0; -1.0; 0.0; 1.0; 10.0; -100.0; 100.0; 0.5; -0.5] in
      let root = List.fold_left (fun found x0 ->
        match found with
        | Some _ -> found
        | None -> newton_root ~tol poly_remaining x0
      ) None starts in
      match root with
      | None -> roots
      | Some r ->
        (* Deflate: divide out (x - r) *)
        let factor = [{ coeff = 1.0; exp = 1 }; { coeff = -. r; exp = 0 }] in
        let (q, _) = divmod poly_remaining factor in
        aux q (r :: roots)
  in
  List.sort compare (aux p [])

(* ---- Lagrange Interpolation ---- *)

(* Given points [(x0,y0); (x1,y1); ...], find the interpolating polynomial *)
let interpolate (points : (float * float) list) : poly =
  let n = List.length points in
  let pts = Array.of_list points in
  let result = ref zero in
  for i = 0 to n - 1 do
    let (xi, yi) = pts.(i) in
    let basis = ref one in
    for j = 0 to n - 1 do
      if i <> j then begin
        let (xj, _) = pts.(j) in
        let denom = xi -. xj in
        (* L_i(x) *= (x - xj) / (xi - xj) *)
        let factor = [
          { coeff = 1.0 /. denom; exp = 1 };
          { coeff = -. xj /. denom; exp = 0 }
        ] in
        basis := mul !basis factor
      end
    done;
    result := add !result (scale yi !basis)
  done;
  !result

(* ---- Pretty Printing ---- *)

let superscript_digit = function
  | '0' -> "\xE2\x81\xB0" | '1' -> "\xC2\xB9" | '2' -> "\xC2\xB2"
  | '3' -> "\xC2\xB3" | '4' -> "\xE2\x81\xB4" | '5' -> "\xE2\x81\xB5"
  | '6' -> "\xE2\x81\xB6" | '7' -> "\xE2\x81\xB7" | '8' -> "\xE2\x81\xB8"
  | '9' -> "\xE2\x81\xB9" | c -> String.make 1 c

let superscript n =
  String.to_seq (string_of_int n)
  |> Seq.map superscript_digit
  |> Seq.fold_left (fun acc s -> acc ^ s) ""

let to_string (p : poly) : string =
  if is_zero p then "0"
  else
    let term_to_string i t =
      let c = t.coeff in
      let e = t.exp in
      let sign = if c >= 0.0 then (if i = 0 then "" else " + ") else (if i = 0 then "-" else " - ") in
      let ac = abs_float c in
      let coeff_str =
        if e = 0 then Printf.sprintf "%g" ac
        else if ac = 1.0 then ""
        else Printf.sprintf "%g" ac
      in
      let var_str =
        if e = 0 then ""
        else if e = 1 then "x"
        else "x" ^ superscript e
      in
      sign ^ coeff_str ^ var_str
    in
    String.concat "" (List.mapi term_to_string p)

(* ---- Chebyshev Polynomials ---- *)

let rec chebyshev (n : int) : poly =
  if n < 0 then invalid_arg "chebyshev: negative index"
  else if n = 0 then one
  else if n = 1 then x
  else
    sub (mul (scale 2.0 x) (chebyshev (n - 1))) (chebyshev (n - 2))

(* ---- Sturm's Theorem (count real roots in interval) ---- *)

let sturm_chain (p : poly) : poly list =
  let p' = differentiate p in
  let rec build chain =
    match chain with
    | [] -> chain
    | [_] -> chain
    | a :: b :: _ ->
      let r = negate (modulo a b) in
      if is_zero r then chain
      else build (r :: chain)
  in
  List.rev (build [p'; p])

let sign_changes_at (chain : poly list) (x_val : float) : int =
  let signs = List.filter_map (fun p ->
    let v = eval p x_val in
    if abs_float v < 1e-15 then None
    else Some (v > 0.0)
  ) chain in
  let rec count = function
    | [] | [_] -> 0
    | a :: b :: rest ->
      (if a <> b then 1 else 0) + count (b :: rest)
  in
  count signs

let count_roots_in (p : poly) (a : float) (b : float) : int =
  let chain = sturm_chain p in
  abs (sign_changes_at chain a - sign_changes_at chain b)

(* ========================================================================== *)
(*  Demo / Main                                                               *)
(* ========================================================================== *)

let () =
  Printf.printf "=== Polynomial Arithmetic Demo ===\n\n";

  (* Build: 2x³ - 3x² + x - 5 *)
  let p = normalize [
    { coeff = 2.0; exp = 3 };
    { coeff = -3.0; exp = 2 };
    { coeff = 1.0; exp = 1 };
    { coeff = -5.0; exp = 0 }
  ] in
  Printf.printf "p(x) = %s\n" (to_string p);

  (* Build: x² - 1 *)
  let q = normalize [
    { coeff = 1.0; exp = 2 };
    { coeff = -1.0; exp = 0 }
  ] in
  Printf.printf "q(x) = %s\n\n" (to_string q);

  (* Arithmetic *)
  Printf.printf "p + q = %s\n" (to_string (add p q));
  Printf.printf "p - q = %s\n" (to_string (sub p q));
  Printf.printf "p * q = %s\n" (to_string (mul p q));
  Printf.printf "p² = %s\n\n" (to_string (pow p 2));

  (* Evaluation *)
  Printf.printf "p(2) = %g\n" (eval p 2.0);
  Printf.printf "q(-1) = %g\n\n" (eval q (-1.0));

  (* Calculus *)
  Printf.printf "p'(x) = %s\n" (to_string (differentiate p));
  Printf.printf "p''(x) = %s\n" (to_string (differentiate (differentiate p)));
  Printf.printf "∫p(x)dx = %s\n" (to_string (integrate p));
  Printf.printf "∫₀² p(x)dx = %g\n\n" (definite_integral p 0.0 2.0);

  (* Division *)
  let (quot, rem) = divmod p q in
  Printf.printf "p / q = %s  remainder %s\n\n" (to_string quot) (to_string rem);

  (* Root finding *)
  let r = normalize [
    { coeff = 1.0; exp = 3 };
    { coeff = -6.0; exp = 2 };
    { coeff = 11.0; exp = 1 };
    { coeff = -6.0; exp = 0 }
  ] in
  Printf.printf "r(x) = %s\n" (to_string r);
  Printf.printf "Roots of r: ";
  List.iter (fun root -> Printf.printf "%g " root) (find_roots r);
  Printf.printf "\n\n";

  (* Interpolation *)
  let points = [(0.0, 1.0); (1.0, 3.0); (2.0, 9.0); (3.0, 19.0)] in
  let interp = interpolate points in
  Printf.printf "Interpolating polynomial through (0,1),(1,3),(2,9),(3,19):\n";
  Printf.printf "  %s\n\n" (to_string interp);

  (* Chebyshev polynomials *)
  Printf.printf "Chebyshev polynomials:\n";
  for i = 0 to 5 do
    Printf.printf "  T_%d(x) = %s\n" i (to_string (chebyshev i))
  done;
  Printf.printf "\n";

  (* Sturm's theorem *)
  Printf.printf "Number of real roots of r(x) in [0, 4]: %d\n"
    (count_roots_in r 0.0 4.0);

  (* Composition *)
  let s = normalize [{ coeff = 1.0; exp = 1 }; { coeff = 1.0; exp = 0 }] in
  Printf.printf "\nq(x+1) = %s\n" (to_string (compose q s));

  Printf.printf "\n=== Done ===\n"
