(* Symbolic Differentiation — compute derivatives of mathematical expressions *)
(* Demonstrates the quintessential OCaml use case: algebraic data types     *)
(* representing abstract syntax, and pattern matching for transformations.  *)
(* Features: symbolic diff, algebraic simplification, evaluation, pretty    *)
(* printing, partial derivatives, higher-order derivatives, chain rule.     *)

(* ── Expression type ──────────────────────────────────────────────── *)

type expr =
  | Const of float                    (* numeric constant *)
  | Var   of string                   (* named variable *)
  | Add   of expr * expr              (* e1 + e2 *)
  | Sub   of expr * expr              (* e1 - e2 *)
  | Mul   of expr * expr              (* e1 * e2 *)
  | Div   of expr * expr              (* e1 / e2 *)
  | Pow   of expr * expr              (* e1 ^ e2 *)
  | Neg   of expr                     (* -e *)
  | Ln    of expr                     (* ln(e) *)
  | Exp   of expr                     (* e^x (natural exponential) *)
  | Sin   of expr                     (* sin(e) *)
  | Cos   of expr                     (* cos(e) *)
  | Tan   of expr                     (* tan(e) *)
  | Sqrt  of expr                     (* sqrt(e) *)
  | Abs   of expr                     (* |e| *)

(* ── Pretty printing ──────────────────────────────────────────────── *)

(* Precedence levels for minimal parenthesization *)
let prec = function
  | Const _ | Var _ | Ln _ | Exp _ | Sin _ | Cos _
  | Tan _ | Sqrt _ | Abs _ -> 100
  | Neg _ -> 90
  | Pow _ -> 80
  | Mul _ | Div _ -> 60
  | Add _ | Sub _ -> 50

let rec to_string e =
  let wrap parent child s =
    if prec child < prec parent then "(" ^ s ^ ")" else s
  in
  match e with
  | Const c ->
    if c = Float.round c && Float.is_finite c then
      string_of_int (int_of_float c)
    else string_of_float c
  | Var x -> x
  | Add (a, b) -> wrap e a (to_string a) ^ " + " ^ wrap e b (to_string b)
  | Sub (a, b) -> wrap e a (to_string a) ^ " - " ^ wrap e b (to_string b)
  | Mul (a, b) -> wrap e a (to_string a) ^ " * " ^ wrap e b (to_string b)
  | Div (a, b) -> wrap e a (to_string a) ^ " / " ^ wrap e b (to_string b)
  | Pow (a, b) -> wrap e a (to_string a) ^ "^" ^ wrap e b (to_string b)
  | Neg a -> "-" ^ wrap e a (to_string a)
  | Ln a -> "ln(" ^ to_string a ^ ")"
  | Exp a -> "exp(" ^ to_string a ^ ")"
  | Sin a -> "sin(" ^ to_string a ^ ")"
  | Cos a -> "cos(" ^ to_string a ^ ")"
  | Tan a -> "tan(" ^ to_string a ^ ")"
  | Sqrt a -> "sqrt(" ^ to_string a ^ ")"
  | Abs a -> "|" ^ to_string a ^ "|"

(* ── Algebraic simplification ─────────────────────────────────────── *)

(* Apply algebraic identities to reduce expression size.
   Runs recursively bottom-up until no more rules apply. *)
let rec simplify = function
  (* Constant folding *)
  | Add (Const a, Const b) -> Const (a +. b)
  | Sub (Const a, Const b) -> Const (a -. b)
  | Mul (Const a, Const b) -> Const (a *. b)
  | Div (Const a, Const b) when b <> 0.0 -> Const (a /. b)
  | Pow (Const a, Const b) -> Const (a ** b)
  | Neg (Const a) -> Const (-.a)

  (* Additive identity: x + 0 = 0 + x = x *)
  | Add (e, Const 0.0) | Add (Const 0.0, e) -> simplify e

  (* Subtractive identity: x - 0 = x *)
  | Sub (e, Const 0.0) -> simplify e
  (* x - x = 0 *)
  | Sub (a, b) when a = b -> Const 0.0

  (* Multiplicative identity: x * 1 = 1 * x = x *)
  | Mul (e, Const 1.0) | Mul (Const 1.0, e) -> simplify e
  (* Multiplicative zero: x * 0 = 0 * x = 0 *)
  | Mul (_, Const 0.0) | Mul (Const 0.0, _) -> Const 0.0

  (* Division identity: x / 1 = x *)
  | Div (e, Const 1.0) -> simplify e
  (* x / x = 1 *)
  | Div (a, b) when a = b -> Const 1.0

  (* Power rules *)
  | Pow (_, Const 0.0) -> Const 1.0      (* x^0 = 1 *)
  | Pow (e, Const 1.0) -> simplify e     (* x^1 = x *)
  | Pow (Const 1.0, _) -> Const 1.0      (* 1^x = 1 *)

  (* Double negation: --x = x *)
  | Neg (Neg e) -> simplify e
  (* Negation of zero *)
  | Neg (Const 0.0) -> Const 0.0

  (* ln(exp(x)) = x, exp(ln(x)) = x *)
  | Ln (Exp e) -> simplify e
  | Exp (Ln e) -> simplify e

  (* ln(1) = 0, exp(0) = 1 *)
  | Ln (Const 1.0) -> Const 0.0
  | Exp (Const 0.0) -> Const 1.0

  (* sqrt(x^2) = |x| *)
  | Sqrt (Pow (e, Const 2.0)) -> Abs (simplify e)

  (* Recursive simplification *)
  | Add (a, b) ->
    let a' = simplify a and b' = simplify b in
    if a' <> a || b' <> b then simplify (Add (a', b')) else Add (a', b')
  | Sub (a, b) ->
    let a' = simplify a and b' = simplify b in
    if a' <> a || b' <> b then simplify (Sub (a', b')) else Sub (a', b')
  | Mul (a, b) ->
    let a' = simplify a and b' = simplify b in
    if a' <> a || b' <> b then simplify (Mul (a', b')) else Mul (a', b')
  | Div (a, b) ->
    let a' = simplify a and b' = simplify b in
    if a' <> a || b' <> b then simplify (Div (a', b')) else Div (a', b')
  | Pow (a, b) ->
    let a' = simplify a and b' = simplify b in
    if a' <> a || b' <> b then simplify (Pow (a', b')) else Pow (a', b')
  | Neg a ->
    let a' = simplify a in
    if a' <> a then simplify (Neg a') else Neg a'
  | Ln a ->
    let a' = simplify a in
    if a' <> a then simplify (Ln a') else Ln a'
  | Exp a ->
    let a' = simplify a in
    if a' <> a then simplify (Exp a') else Exp a'
  | Sin a ->
    let a' = simplify a in
    if a' <> a then simplify (Sin a') else Sin a'
  | Cos a ->
    let a' = simplify a in
    if a' <> a then simplify (Cos a') else Cos a'
  | Tan a ->
    let a' = simplify a in
    if a' <> a then simplify (Tan a') else Tan a'
  | Sqrt a ->
    let a' = simplify a in
    if a' <> a then simplify (Sqrt a') else Sqrt a'
  | Abs a ->
    let a' = simplify a in
    if a' <> a then simplify (Abs a') else Abs a'
  | e -> e   (* Const, Var — already simplified *)

(* ── Differentiation ──────────────────────────────────────────────── *)

(* Compute the symbolic derivative d(expr)/d(var).
   Applies standard calculus rules: sum, product, quotient, chain, power. *)
let rec diff var = function
  (* Constants and variables *)
  | Const _ -> Const 0.0
  | Var x when x = var -> Const 1.0
  | Var _ -> Const 0.0

  (* Sum and difference rules *)
  | Add (a, b) -> Add (diff var a, diff var b)
  | Sub (a, b) -> Sub (diff var a, diff var b)

  (* Product rule: d(fg) = f'g + fg' *)
  | Mul (a, b) ->
    Add (Mul (diff var a, b), Mul (a, diff var b))

  (* Quotient rule: d(f/g) = (f'g - fg') / g^2 *)
  | Div (a, b) ->
    Div (Sub (Mul (diff var a, b), Mul (a, diff var b)),
         Pow (b, Const 2.0))

  (* Power rule with chain rule *)
  (* Case 1: x^n where n is constant → n * x^(n-1) * x' *)
  | Pow (base, Const n) ->
    Mul (Mul (Const n, Pow (base, Const (n -. 1.0))), diff var base)

  (* Case 2: a^b general → a^b * (b' * ln(a) + b * a'/a) *)
  | Pow (a, b) ->
    Mul (Pow (a, b),
         Add (Mul (diff var b, Ln a),
              Mul (b, Div (diff var a, a))))

  (* Negation *)
  | Neg a -> Neg (diff var a)

  (* ln(f) → f'/f *)
  | Ln a -> Div (diff var a, a)

  (* exp(f) → exp(f) * f' *)
  | Exp a -> Mul (Exp a, diff var a)

  (* sin(f) → cos(f) * f' *)
  | Sin a -> Mul (Cos a, diff var a)

  (* cos(f) → -sin(f) * f' *)
  | Cos a -> Neg (Mul (Sin a, diff var a))

  (* tan(f) → f' / cos(f)^2 *)
  | Tan a -> Div (diff var a, Pow (Cos a, Const 2.0))

  (* sqrt(f) → f' / (2 * sqrt(f)) *)
  | Sqrt a -> Div (diff var a, Mul (Const 2.0, Sqrt a))

  (* |f| → f * f' / |f| (where f ≠ 0) *)
  | Abs a -> Div (Mul (a, diff var a), Abs a)

(* Differentiate and simplify in one step *)
let differentiate var e = simplify (diff var e)

(* Higher-order derivative: d^n(expr)/d(var)^n *)
let rec nth_derivative var n e =
  if n <= 0 then simplify e
  else nth_derivative var (n - 1) (differentiate var e)

(* ── Evaluation ───────────────────────────────────────────────────── *)

(** Raised when evaluation encounters a mathematical domain error
    (division by zero, log of non-positive, sqrt of negative, etc.). *)
exception Domain_error of string

(* Evaluate an expression given variable bindings.
   Raises [Failure] if a variable is unbound.
   Raises [Domain_error] on mathematical domain violations. *)
let rec eval env = function
  | Const c -> c
  | Var x ->
    (match List.assoc_opt x env with
     | Some v -> v
     | None -> failwith ("unbound variable: " ^ x))
  | Add (a, b) -> eval env a +. eval env b
  | Sub (a, b) -> eval env a -. eval env b
  | Mul (a, b) -> eval env a *. eval env b
  | Div (a, b) ->
    let bv = eval env b in
    if bv = 0.0 then raise (Domain_error "division by zero")
    else eval env a /. bv
  | Pow (a, b) ->
    let av = eval env a and bv = eval env b in
    let result = av ** bv in
    if Float.is_nan result && not (Float.is_nan av) && not (Float.is_nan bv)
    then raise (Domain_error (Printf.sprintf "undefined power: %g ** %g" av bv))
    else if Float.is_infinite result && Float.is_finite av && Float.is_finite bv
    then raise (Domain_error (Printf.sprintf "infinite power: %g ** %g" av bv))
    else result
  | Neg a -> -.(eval env a)
  | Ln a ->
    let av = eval env a in
    if av <= 0.0 then raise (Domain_error (Printf.sprintf "log of non-positive value: %g" av))
    else log av
  | Exp a -> exp (eval env a)
  | Sin a -> sin (eval env a)
  | Cos a -> cos (eval env a)
  | Tan a ->
    let av = eval env a in
    let cv = cos av in
    if Float.abs cv < 1e-15
    then raise (Domain_error (Printf.sprintf "tan at singularity: %g" av))
    else sin av /. cv
  | Sqrt a ->
    let av = eval env a in
    if av < 0.0 then raise (Domain_error (Printf.sprintf "sqrt of negative value: %g" av))
    else sqrt av
  | Abs a -> Float.abs (eval env a)

(** [try_eval env expr] evaluates [expr] safely, returning [Some value]
    on success or [None] on domain errors. Useful in numerical methods
    where domain errors are expected and should be handled gracefully. *)
let try_eval env expr =
  try Some (eval env expr)
  with Domain_error _ -> None

(* ── Variable collection ──────────────────────────────────────────── *)

(* Collect all free variables in an expression *)
let variables expr =
  let rec collect acc = function
    | Const _ -> acc
    | Var x -> if List.mem x acc then acc else x :: acc
    | Add (a, b) | Sub (a, b) | Mul (a, b) | Div (a, b) | Pow (a, b) ->
      collect (collect acc a) b
    | Neg a | Ln a | Exp a | Sin a | Cos a | Tan a | Sqrt a | Abs a ->
      collect acc a
  in
  List.sort String.compare (collect [] expr)

(* ── Gradient (partial derivatives for all variables) ─────────────── *)

let gradient expr =
  let vars = variables expr in
  List.map (fun v -> (v, differentiate v expr)) vars

(* ── Expression substitution ──────────────────────────────────────── *)

(* Replace all occurrences of a variable with an expression *)
let rec substitute var replacement = function
  | Const c -> Const c
  | Var x when x = var -> replacement
  | Var x -> Var x
  | Add (a, b) -> Add (substitute var replacement a, substitute var replacement b)
  | Sub (a, b) -> Sub (substitute var replacement a, substitute var replacement b)
  | Mul (a, b) -> Mul (substitute var replacement a, substitute var replacement b)
  | Div (a, b) -> Div (substitute var replacement a, substitute var replacement b)
  | Pow (a, b) -> Pow (substitute var replacement a, substitute var replacement b)
  | Neg a -> Neg (substitute var replacement a)
  | Ln a -> Ln (substitute var replacement a)
  | Exp a -> Exp (substitute var replacement a)
  | Sin a -> Sin (substitute var replacement a)
  | Cos a -> Cos (substitute var replacement a)
  | Tan a -> Tan (substitute var replacement a)
  | Sqrt a -> Sqrt (substitute var replacement a)
  | Abs a -> Abs (substitute var replacement a)

(* ── Demo ─────────────────────────────────────────────────────────── *)

let () =
  Printf.printf "=== Symbolic Differentiation ===\n\n";

  let x = Var "x" in
  let y = Var "y" in

  (* Example 1: Polynomial — d/dx (x^3 + 2x^2 - 5x + 3) *)
  let poly = Add (Pow (x, Const 3.0),
                  Sub (Mul (Const 2.0, Pow (x, Const 2.0)),
                       Add (Mul (Const 5.0, x), Const (-.3.0)))) in
  let poly' = differentiate "x" poly in
  Printf.printf "f(x) = %s\n" (to_string poly);
  Printf.printf "f'(x) = %s\n" (to_string poly');
  Printf.printf "f'(2) = %.1f\n\n" (eval [("x", 2.0)] poly');

  (* Example 2: Product rule — d/dx (x * sin(x)) *)
  let prod = Mul (x, Sin x) in
  let prod' = differentiate "x" prod in
  Printf.printf "f(x) = %s\n" (to_string prod);
  Printf.printf "f'(x) = %s\n" (to_string prod');
  Printf.printf "f'(π/2) = %.4f\n\n" (eval [("x", Float.pi /. 2.0)] prod');

  (* Example 3: Chain rule — d/dx (exp(x^2)) *)
  let chain = Exp (Pow (x, Const 2.0)) in
  let chain' = differentiate "x" chain in
  Printf.printf "f(x) = %s\n" (to_string chain);
  Printf.printf "f'(x) = %s\n" (to_string chain');
  Printf.printf "f'(1) = %.4f\n\n" (eval [("x", 1.0)] chain');

  (* Example 4: Quotient rule — d/dx (x / (x + 1)) *)
  let quot = Div (x, Add (x, Const 1.0)) in
  let quot' = differentiate "x" quot in
  Printf.printf "f(x) = %s\n" (to_string quot);
  Printf.printf "f'(x) = %s\n" (to_string quot');
  Printf.printf "f'(1) = %.4f\n\n" (eval [("x", 1.0)] quot');

  (* Example 5: Second derivative — d²/dx² (sin(x)) = -sin(x) *)
  let sin_x = Sin x in
  let sin'' = nth_derivative "x" 2 sin_x in
  Printf.printf "f(x) = %s\n" (to_string sin_x);
  Printf.printf "f''(x) = %s\n" (to_string sin'');
  Printf.printf "f''(π) = %.4f\n\n" (eval [("x", Float.pi)] sin'');

  (* Example 6: Partial derivatives — d/dx and d/dy of x^2 * y + y^3 *)
  let multi = Add (Mul (Pow (x, Const 2.0), y), Pow (y, Const 3.0)) in
  let dx = differentiate "x" multi in
  let dy = differentiate "y" multi in
  Printf.printf "f(x,y) = %s\n" (to_string multi);
  Printf.printf "∂f/∂x = %s\n" (to_string dx);
  Printf.printf "∂f/∂y = %s\n" (to_string dy);
  Printf.printf "∂f/∂x at (2,3) = %.1f\n" (eval [("x", 2.0); ("y", 3.0)] dx);
  Printf.printf "∂f/∂y at (2,3) = %.1f\n\n" (eval [("x", 2.0); ("y", 3.0)] dy);

  (* Example 7: Gradient *)
  let grad = gradient multi in
  Printf.printf "Gradient of %s:\n" (to_string multi);
  List.iter (fun (v, de) ->
    Printf.printf "  ∂f/∂%s = %s\n" v (to_string de)
  ) grad;
  Printf.printf "\n";

  (* Example 8: Substitution *)
  let before = Mul (x, Add (x, Const 1.0)) in
  let after = substitute "x" (Const 3.0) before in
  Printf.printf "f(x) = %s\n" (to_string before);
  Printf.printf "f(3) = %s = %.0f\n\n" (to_string (simplify after)) (eval [] (simplify after));

  (* Example 9: Logarithmic differentiation — d/dx (ln(x^2 + 1)) *)
  let logfn = Ln (Add (Pow (x, Const 2.0), Const 1.0)) in
  let logfn' = differentiate "x" logfn in
  Printf.printf "f(x) = %s\n" (to_string logfn);
  Printf.printf "f'(x) = %s\n" (to_string logfn');
  Printf.printf "f'(1) = %.4f\n\n" (eval [("x", 1.0)] logfn');

  (* Example 10: Square root — d/dx (sqrt(x^2 + 1)) *)
  let sqrtfn = Sqrt (Add (Pow (x, Const 2.0), Const 1.0)) in
  let sqrtfn' = differentiate "x" sqrtfn in
  Printf.printf "f(x) = %s\n" (to_string sqrtfn);
  Printf.printf "f'(x) = %s\n" (to_string sqrtfn');
  Printf.printf "f'(3) = %.4f\n" (eval [("x", 3.0)] sqrtfn');

  Printf.printf "\n=== Done ===\n"
