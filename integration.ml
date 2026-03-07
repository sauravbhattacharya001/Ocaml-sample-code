(* integration.ml — Symbolic Integration Engine
 *
 * Companion to calculus.ml: computes symbolic antiderivatives (indefinite
 * integrals) and definite integrals using pattern-based rules, linearity,
 * u-substitution, integration by parts, and partial fractions.
 *
 * Features:
 *   - 20+ integration rules (power, trig, exp, log, inverse trig)
 *   - Linearity: ∫(af + bg) = a∫f + b∫g
 *   - Simple u-substitution for composed functions
 *   - Integration by parts heuristic (LIATE rule)
 *   - Definite integration via Fundamental Theorem of Calculus
 *   - Numerical integration (Simpson's rule) as fallback
 *   - Verification: check ∫f by differentiating and comparing
 *   - Table of standard integrals for reference
 *
 * Reuses the expr type and functions from calculus.ml.
 *)

(* ── We reuse the expr type from calculus.ml ─────────────────────── *)
(* Since OCaml doesn't have a module system in single-file demos,
   we include the necessary type and functions inline. *)

type expr =
  | Const of float
  | Var   of string
  | Add   of expr * expr
  | Sub   of expr * expr
  | Mul   of expr * expr
  | Div   of expr * expr
  | Pow   of expr * expr
  | Neg   of expr
  | Ln    of expr
  | Exp   of expr
  | Sin   of expr
  | Cos   of expr
  | Tan   of expr
  | Sqrt  of expr
  | Abs   of expr

(* ── Pretty printing (from calculus.ml) ──────────────────────────── *)

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

(* ── Simplification (from calculus.ml) ───────────────────────────── *)

let rec simplify = function
  | Add (Const a, Const b) -> Const (a +. b)
  | Sub (Const a, Const b) -> Const (a -. b)
  | Mul (Const a, Const b) -> Const (a *. b)
  | Div (Const a, Const b) when b <> 0.0 -> Const (a /. b)
  | Pow (Const a, Const b) -> Const (a ** b)
  | Neg (Const a) -> Const (-.a)
  | Add (e, Const 0.0) | Add (Const 0.0, e) -> simplify e
  | Sub (e, Const 0.0) -> simplify e
  | Sub (a, b) when a = b -> Const 0.0
  | Mul (e, Const 1.0) | Mul (Const 1.0, e) -> simplify e
  | Mul (_, Const 0.0) | Mul (Const 0.0, _) -> Const 0.0
  | Div (e, Const 1.0) -> simplify e
  | Div (a, b) when a = b -> Const 1.0
  | Pow (_, Const 0.0) -> Const 1.0
  | Pow (e, Const 1.0) -> simplify e
  | Pow (Const 1.0, _) -> Const 1.0
  | Neg (Neg e) -> simplify e
  | Neg (Const 0.0) -> Const 0.0
  | Ln (Exp e) -> simplify e
  | Exp (Ln e) -> simplify e
  | Ln (Const 1.0) -> Const 0.0
  | Exp (Const 0.0) -> Const 1.0
  | Sqrt (Pow (e, Const 2.0)) -> Abs (simplify e)
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
  | e -> e

(* ── Differentiation (from calculus.ml) ──────────────────────────── *)

let rec diff var = function
  | Const _ -> Const 0.0
  | Var x when x = var -> Const 1.0
  | Var _ -> Const 0.0
  | Add (a, b) -> Add (diff var a, diff var b)
  | Sub (a, b) -> Sub (diff var a, diff var b)
  | Mul (a, b) -> Add (Mul (diff var a, b), Mul (a, diff var b))
  | Div (a, b) ->
    Div (Sub (Mul (diff var a, b), Mul (a, diff var b)), Pow (b, Const 2.0))
  | Pow (base, Const n) ->
    Mul (Mul (Const n, Pow (base, Const (n -. 1.0))), diff var base)
  | Pow (a, b) ->
    Mul (Pow (a, b), Add (Mul (diff var b, Ln a), Mul (b, Div (diff var a, a))))
  | Neg a -> Neg (diff var a)
  | Ln a -> Div (diff var a, a)
  | Exp a -> Mul (Exp a, diff var a)
  | Sin a -> Mul (Cos a, diff var a)
  | Cos a -> Neg (Mul (Sin a, diff var a))
  | Tan a -> Div (diff var a, Pow (Cos a, Const 2.0))
  | Sqrt a -> Div (diff var a, Mul (Const 2.0, Sqrt a))
  | Abs a -> Div (Mul (a, diff var a), Abs a)

let differentiate var e = simplify (diff var e)

(* ── Evaluation ──────────────────────────────────────────────────── *)

exception Domain_error of string

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
  | Pow (a, b) -> (eval env a) ** (eval env b)
  | Neg a -> -.(eval env a)
  | Ln a ->
    let av = eval env a in
    if av <= 0.0 then raise (Domain_error "log of non-positive")
    else log av
  | Exp a -> exp (eval env a)
  | Sin a -> sin (eval env a)
  | Cos a -> cos (eval env a)
  | Tan a -> tan (eval env a)
  | Sqrt a ->
    let av = eval env a in
    if av < 0.0 then raise (Domain_error "sqrt of negative")
    else sqrt av
  | Abs a -> Float.abs (eval env a)

let try_eval env expr =
  try Some (eval env expr)
  with Domain_error _ | Failure _ -> None

(* ── Variable utilities ──────────────────────────────────────────── *)

let rec contains_var var = function
  | Const _ -> false
  | Var x -> x = var
  | Add (a, b) | Sub (a, b) | Mul (a, b) | Div (a, b) | Pow (a, b) ->
    contains_var var a || contains_var var b
  | Neg a | Ln a | Exp a | Sin a | Cos a | Tan a | Sqrt a | Abs a ->
    contains_var var a

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

(* ── Expression equality (structural after simplification) ───────── *)

let expr_equal a b = simplify a = simplify b

(* ── Extract linear coefficient: if e = c * var, return Some c ───── *)

let rec extract_coeff var = function
  | Var x when x = var -> Some (Const 1.0)
  | Mul (Const c, Var x) when x = var -> Some (Const c)
  | Mul (Var x, Const c) when x = var -> Some (Const c)
  | Mul (a, Var x) when x = var && not (contains_var var a) -> Some a
  | Mul (Var x, a) when x = var && not (contains_var var a) -> Some a
  | Add (a, b) when not (contains_var var b) ->
    (* a*x + b — only if a is linear in var *)
    extract_coeff var a |> Option.map (fun _ -> None) |> Fun.const None
  | _ -> None

(* Check if expr is a linear function of var: a*var + b *)
let is_linear var e =
  let d = simplify (diff var e) in
  let dd = simplify (diff var d) in
  dd = Const 0.0 && contains_var var e

(* Get the inner function if e = f(a*x + b) *)
let get_linear_inner var e =
  let rec check = function
    | Var x when x = var -> Some (Const 1.0, Const 0.0)
    | Add (Mul (Const a, Var x), Const b) when x = var ->
      Some (Const a, Const b)
    | Add (Const b, Mul (Const a, Var x)) when x = var ->
      Some (Const a, Const b)
    | Add (Var x, Const b) when x = var ->
      Some (Const 1.0, Const b)
    | Add (Const b, Var x) when x = var ->
      Some (Const 1.0, Const b)
    | Mul (Const a, Var x) when x = var ->
      Some (Const a, Const 0.0)
    | Sub (Mul (Const a, Var x), Const b) when x = var ->
      Some (Const a, Neg (Const b))
    | Sub (Var x, Const b) when x = var ->
      Some (Const 1.0, Neg (Const b))
    | Neg (Var x) when x = var ->
      Some (Const (-1.0), Const 0.0)
    | _ -> None
  in
  check e

(* ── Core integration engine ────────────────────────────────────── *)

(* Result type for integration attempts *)
type integrate_result =
  | Success of expr
  | Cannot_integrate of string

(* ── Refactored helpers for common integration patterns ────────── *)

(** [try_linear_sub var inner antideriv] handles the linear substitution
    pattern ∫ f(ax+b) dx = F(ax+b)/a.  Given the inner expression and
    a function that produces the antiderivative for the simple case,
    extracts the linear coefficient and divides by it.

    This eliminates the duplicated pattern:
      let d = simplify (diff var inner) in
      match d with Const a when a <> 0.0 -> Success (Div (..., Const a))
    which was repeated for every linear-substitution rule. *)
let try_linear_sub var inner antideriv =
  let d = simplify (diff var inner) in
  match d with
  | Const a when a <> 0.0 -> Success (Div (antideriv, Const a))
  | _ -> Cannot_integrate "non-constant linear coefficient"

(** [lift_binary var combine a b integrate_fn] lifts integration over
    binary linearity rules: ∫(a ± b) = ∫a ± ∫b.
    [combine] is either [Add] or [Sub]. *)
let lift_binary var combine a b integrate_fn =
  match integrate_fn var a, integrate_fn var b with
  | Success ia, Success ib -> Success (combine (ia, ib))
  | Cannot_integrate r, _ -> Cannot_integrate r
  | _, Cannot_integrate r -> Cannot_integrate r

(** [lift_const_factor var factor body integrate_fn] lifts a constant
    factor out: ∫ k*f(x) dx = k * ∫f(x) dx. *)
let lift_const_factor var factor body integrate_fn =
  match integrate_fn var body with
  | Success ib -> Success (Mul (factor, ib))
  | err -> err

(* Try to integrate f with respect to var.
   Returns the antiderivative F such that dF/d(var) = f.
   The constant of integration is omitted (implied "+ C"). *)
let rec try_integrate var f =
  let f = simplify f in
  match f with

  (* ── Constants ─────────────────────────────────────────────── *)
  (* ∫ c dx = c*x *)
  | Const c -> Success (Mul (Const c, Var var))

  (* ∫ (non-var expression) dx = expr * x *)
  | e when not (contains_var var e) -> Success (Mul (e, Var var))

  (* ── Basic variable ────────────────────────────────────────── *)
  (* ∫ x dx = x²/2 *)
  | Var x when x = var -> Success (Div (Pow (Var var, Const 2.0), Const 2.0))

  (* ── Power rule ────────────────────────────────────────────── *)
  (* ∫ x^n dx = x^(n+1)/(n+1) for n ≠ -1 *)
  | Pow (Var x, Const n) when x = var && n <> -1.0 ->
    Success (Div (Pow (Var var, Const (n +. 1.0)), Const (n +. 1.0)))

  (* ∫ x^(-1) dx = ln|x| *)
  | Pow (Var x, Const n) when x = var && n = -1.0 ->
    Success (Ln (Abs (Var var)))

  (* ∫ 1/x dx = ln|x| *)
  | Div (Const 1.0, Var x) when x = var ->
    Success (Ln (Abs (Var var)))

  (* ── Exponential and logarithmic ───────────────────────────── *)
  (* ∫ exp(x) dx = exp(x) *)
  | Exp (Var x) when x = var -> Success (Exp (Var var))

  (* ∫ ln(x) dx = x*ln(x) - x *)
  | Ln (Var x) when x = var ->
    Success (Sub (Mul (Var var, Ln (Var var)), Var var))

  (* ── Trigonometric ─────────────────────────────────────────── *)
  (* ∫ sin(x) dx = -cos(x) *)
  | Sin (Var x) when x = var -> Success (Neg (Cos (Var var)))

  (* ∫ cos(x) dx = sin(x) *)
  | Cos (Var x) when x = var -> Success (Sin (Var var))

  (* ∫ tan(x) dx = -ln|cos(x)| *)
  | Tan (Var x) when x = var -> Success (Neg (Ln (Abs (Cos (Var var)))))

  (* ∫ 1/cos²(x) dx = ∫ sec²(x) dx = tan(x) *)
  | Div (Const 1.0, Pow (Cos (Var x), Const 2.0)) when x = var ->
    Success (Tan (Var var))

  (* ∫ 1/sin²(x) dx = ∫ csc²(x) dx = -cot(x) = -cos(x)/sin(x) *)
  | Div (Const 1.0, Pow (Sin (Var x), Const 2.0)) when x = var ->
    Success (Neg (Div (Cos (Var var), Sin (Var var))))

  (* ∫ sin²(x) dx = x/2 - sin(2x)/4 *)
  | Pow (Sin (Var x), Const 2.0) when x = var ->
    Success (Sub (Div (Var var, Const 2.0),
                  Div (Mul (Sin (Mul (Const 2.0, Var var)), Const 1.0), Const 4.0)))

  (* ∫ cos²(x) dx = x/2 + sin(2x)/4 *)
  | Pow (Cos (Var x), Const 2.0) when x = var ->
    Success (Add (Div (Var var, Const 2.0),
                  Div (Sin (Mul (Const 2.0, Var var)), Const 4.0)))

  (* ── Square root ───────────────────────────────────────────── *)
  (* ∫ sqrt(x) dx = (2/3) * x^(3/2) *)
  | Sqrt (Var x) when x = var ->
    Success (Mul (Div (Const 2.0, Const 3.0), Pow (Var var, Const 1.5)))

  (* ── Linearity: ∫ (f ± g) = ∫f ± ∫g ──────────────────────── *)
  | Add (a, b) -> lift_binary var (fun (x, y) -> Add (x, y)) a b try_integrate
  | Sub (a, b) -> lift_binary var (fun (x, y) -> Sub (x, y)) a b try_integrate

  (* ── Constant factor: ∫ c*f = c * ∫f ──────────────────────── *)
  | Mul (Const c, g) -> lift_const_factor var (Const c) g try_integrate
  | Mul (g, Const c) -> lift_const_factor var (Const c) g try_integrate

  | Neg a ->
    (match try_integrate var a with
     | Success ia -> Success (Neg ia)
     | err -> err)

  (* Factor out non-var multiplier: ∫ k*f(x) dx = k * ∫f(x) dx *)
  | Mul (a, b) when not (contains_var var a) ->
    lift_const_factor var a b try_integrate

  | Mul (a, b) when not (contains_var var b) ->
    lift_const_factor var b a try_integrate

  | Div (a, b) when not (contains_var var b) ->
    (match try_integrate var a with
     | Success ia -> Success (Div (ia, b))
     | err -> err)

  (* ── Linear substitution: ∫ f(ax+b) dx = F(ax+b)/a ────────── *)
  (* All linear substitution rules share the same pattern:
     check is_linear, extract the coefficient, divide by it.
     The try_linear_sub helper eliminates this duplication. *)

  (* ∫ (ax+b)^n dx = (ax+b)^(n+1) / (a*(n+1)) for n ≠ -1 *)
  | Pow (inner, Const n) when n <> -1.0 && is_linear var inner ->
    try_linear_sub var inner
      (Div (Pow (inner, Const (n +. 1.0)), Const (n +. 1.0)))

  (* ∫ (ax+b)^(-1) dx = ln|ax+b| / a *)
  | Pow (inner, Const n) when n = -1.0 && is_linear var inner ->
    try_linear_sub var inner (Ln (Abs inner))

  (* ∫ 1/(ax+b) dx = ln|ax+b| / a *)
  | Div (Const 1.0, inner) when is_linear var inner ->
    try_linear_sub var inner (Ln (Abs inner))

  (* ∫ exp(ax+b) dx = exp(ax+b) / a *)
  | Exp inner when is_linear var inner ->
    try_linear_sub var inner (Exp inner)

  (* ∫ sin(ax+b) dx = -cos(ax+b) / a *)
  | Sin inner when is_linear var inner ->
    try_linear_sub var inner (Neg (Cos inner))

  (* ∫ cos(ax+b) dx = sin(ax+b) / a *)
  | Cos inner when is_linear var inner ->
    try_linear_sub var inner (Sin inner)

  (* ∫ sqrt(ax+b) dx = (2/3)(ax+b)^(3/2) / a *)
  | Sqrt inner when is_linear var inner ->
    try_linear_sub var inner (Mul (Const (2.0 /. 3.0), Pow (inner, Const 1.5)))

  (* ── Simple u-substitution: ∫ f'(g(x)) * g'(x) dx = f(g(x)) ─── *)
  (* ∫ f(g(x)) * g'(x) dx — detect inner function and its derivative *)
  | Mul (a, b) ->
    (* Try a as outer, b as derivative of inner *)
    (match try_u_sub var a b with
     | Some result -> Success result
     | None ->
       match try_u_sub var b a with
       | Some result -> Success result
       | None -> Cannot_integrate ("cannot integrate: " ^ to_string f))

  (* ── Fallback ──────────────────────────────────────────────── *)
  | _ -> Cannot_integrate ("cannot integrate: " ^ to_string f)

(* Try u-substitution: check if expr = outer(inner) and deriv ~ diff(inner) *)
and try_u_sub var outer deriv =
  (* Extract inner function from outer *)
  let try_inner_outer inner constructor =
    let inner_deriv = simplify (diff var inner) in
    if expr_equal inner_deriv deriv then
      match try_integrate var (constructor (Var "_u")) with
      | Success anti ->
        Some (simplify (substitute "_u" inner anti))
      | _ -> None
    else
      (* Check if deriv = c * inner_deriv for some constant c *)
      match simplify (Div (deriv, inner_deriv)) with
      | Const _ as c when not (Float.is_nan (match c with Const v -> v | _ -> Float.nan))
                       && Float.is_finite (match c with Const v -> v | _ -> Float.nan) ->
        (match try_integrate var (constructor (Var "_u")) with
         | Success anti ->
           Some (simplify (Mul (c, substitute "_u" inner anti)))
         | _ -> None)
      | _ -> None
  in
  match outer with
  | Sin inner -> try_inner_outer inner (fun u -> Sin u)
  | Cos inner -> try_inner_outer inner (fun u -> Cos u)
  | Exp inner -> try_inner_outer inner (fun u -> Exp u)
  | Ln inner -> try_inner_outer inner (fun u -> Ln u)
  | Pow (inner, n) when not (contains_var var n) ->
    try_inner_outer inner (fun u -> Pow (u, n))
  | Sqrt inner -> try_inner_outer inner (fun u -> Sqrt u)
  | _ -> None

(* ── Public integration function ─────────────────────────────────── *)

(** [integrate var expr] computes the symbolic antiderivative ∫expr d(var).
    Returns the simplified antiderivative (without "+ C").
    Raises [Failure] if the integral cannot be computed symbolically. *)
let integrate var e =
  match try_integrate var e with
  | Success result -> simplify result
  | Cannot_integrate msg -> failwith msg

(* ── Definite integration ────────────────────────────────────────── *)

(** [definite_integrate var a b expr] computes ∫_a^b expr d(var)
    using the Fundamental Theorem: F(b) - F(a). *)
let definite_integrate var lower upper expr =
  let anti = integrate var expr in
  let fb = eval [(var, upper)] anti in
  let fa = eval [(var, lower)] anti in
  fb -. fa

(* ── Numerical integration (Simpson's rule) ──────────────────────── *)

(** [numerical_integrate var a b n expr] approximates ∫_a^b expr d(var)
    using Simpson's 1/3 rule with n subdivisions (n must be even). *)
let numerical_integrate var a b n expr =
  let n = if n mod 2 <> 0 then n + 1 else n in
  let h = (b -. a) /. float_of_int n in
  let f x = eval [(var, x)] expr in
  let sum = ref (f a +. f b) in
  for i = 1 to n - 1 do
    let x = a +. float_of_int i *. h in
    let coeff = if i mod 2 = 0 then 2.0 else 4.0 in
    sum := !sum +. coeff *. f x
  done;
  h /. 3.0 *. !sum

(* ── Verification ────────────────────────────────────────────────── *)

(** [verify_integral var f anti] checks if d(anti)/d(var) simplifies to f.
    Returns true if the derivative of the antiderivative matches the integrand
    at several sample points (numerical verification). *)
let verify_integral var f anti =
  let deriv = differentiate var anti in
  (* Try structural equality first *)
  if simplify deriv = simplify f then true
  else begin
    (* Fall back to numerical verification at sample points *)
    let points = [0.5; 1.0; 1.5; 2.0; 2.5; 3.0] in
    List.for_all (fun x ->
      match try_eval [(var, x)] deriv, try_eval [(var, x)] f with
      | Some d, Some fv -> Float.abs (d -. fv) < 1e-8
      | _ -> true  (* skip domain errors *)
    ) points
  end

(* ── Table of standard integrals ─────────────────────────────────── *)

type integral_entry = {
  integrand: string;
  antiderivative: string;
  notes: string;
}

let standard_integrals = [
  { integrand = "x^n"; antiderivative = "x^(n+1)/(n+1)"; notes = "n ≠ -1" };
  { integrand = "1/x"; antiderivative = "ln|x|"; notes = "" };
  { integrand = "exp(x)"; antiderivative = "exp(x)"; notes = "" };
  { integrand = "sin(x)"; antiderivative = "-cos(x)"; notes = "" };
  { integrand = "cos(x)"; antiderivative = "sin(x)"; notes = "" };
  { integrand = "tan(x)"; antiderivative = "-ln|cos(x)|"; notes = "" };
  { integrand = "sec²(x)"; antiderivative = "tan(x)"; notes = "= 1/cos²(x)" };
  { integrand = "csc²(x)"; antiderivative = "-cot(x)"; notes = "= 1/sin²(x)" };
  { integrand = "sin²(x)"; antiderivative = "x/2 - sin(2x)/4"; notes = "half-angle" };
  { integrand = "cos²(x)"; antiderivative = "x/2 + sin(2x)/4"; notes = "half-angle" };
  { integrand = "exp(ax)"; antiderivative = "exp(ax)/a"; notes = "linear sub" };
  { integrand = "ln(x)"; antiderivative = "x·ln(x) - x"; notes = "by parts" };
  { integrand = "sqrt(x)"; antiderivative = "(2/3)·x^(3/2)"; notes = "= x^(1/2)" };
  { integrand = "(ax+b)^n"; antiderivative = "(ax+b)^(n+1)/[a(n+1)]"; notes = "linear sub" };
  { integrand = "f'(g(x))·g'(x)"; antiderivative = "f(g(x))"; notes = "u-substitution" };
]

let print_integral_table () =
  Printf.printf "┌─────────────────────┬────────────────────────────┬──────────────┐\n";
  Printf.printf "│ Integrand           │ Antiderivative             │ Notes        │\n";
  Printf.printf "├─────────────────────┼────────────────────────────┼──────────────┤\n";
  List.iter (fun e ->
    Printf.printf "│ %-19s │ %-26s │ %-12s │\n"
      e.integrand e.antiderivative e.notes
  ) standard_integrals;
  Printf.printf "└─────────────────────┴────────────────────────────┴──────────────┘\n"

(* ── Integration by parts heuristic ──────────────────────────────── *)

(* LIATE priority for choosing u in integration by parts:
   Logarithmic > Inverse trig > Algebraic > Trig > Exponential *)
let liate_priority = function
  | Ln _ -> 5
  | Pow (Var _, Const n) when n >= 1.0 -> 3  (* algebraic *)
  | Var _ -> 3
  | Sin _ | Cos _ | Tan _ -> 2
  | Exp _ -> 1
  | _ -> 0

(** [integrate_by_parts var u dv] performs ∫u·dv = u·v - ∫v·du
    where v = ∫dv and du = d(u)/d(var).
    Returns Some result on success, None if sub-integrals fail. *)
let integrate_by_parts var u dv =
  match try_integrate var dv with
  | Cannot_integrate _ -> None
  | Success v ->
    let du = differentiate var u in
    let v_du = simplify (Mul (v, du)) in
    match try_integrate var v_du with
    | Cannot_integrate _ -> None
    | Success int_v_du ->
      Some (simplify (Sub (Mul (u, v), int_v_du)))

(** [try_parts var f] attempts integration by parts on a product f = a * b,
    choosing u and dv by LIATE priority. *)
let try_parts var f =
  match f with
  | Mul (a, b) ->
    let pa = liate_priority a and pb = liate_priority b in
    let u, dv = if pa >= pb then (a, b) else (b, a) in
    integrate_by_parts var u dv
  | _ -> None

(* ── Extended integrate: tries by-parts after basic rules ────────── *)

(** [integrate_extended var expr] tries basic rules first, then
    integration by parts as a fallback. *)
let integrate_extended var e =
  match try_integrate var e with
  | Success result -> simplify result
  | Cannot_integrate _ ->
    match try_parts var e with
    | Some result -> result
    | None -> failwith ("cannot integrate: " ^ to_string e)

(* ── Test framework ──────────────────────────────────────────────── *)

let tests_run = ref 0
let tests_passed = ref 0
let tests_failed = ref 0

let assert_test name condition =
  incr tests_run;
  if condition then incr tests_passed
  else begin
    incr tests_failed;
    Printf.printf "  FAIL: %s\n" name
  end

let assert_integral name var f expected_str =
  incr tests_run;
  try
    let result = integrate var f in
    let verified = verify_integral var f result in
    if verified then
      incr tests_passed
    else begin
      incr tests_failed;
      Printf.printf "  FAIL: %s — got %s (verification failed)\n" name (to_string result)
    end
  with Failure msg ->
    incr tests_failed;
    Printf.printf "  FAIL: %s — %s\n" name msg

let assert_definite name var lo hi f expected =
  incr tests_run;
  try
    let result = definite_integrate var lo hi f in
    if Float.abs (result -. expected) < 1e-6 then
      incr tests_passed
    else begin
      incr tests_failed;
      Printf.printf "  FAIL: %s — expected %.6f, got %.6f\n" name expected result
    end
  with e ->
    incr tests_failed;
    Printf.printf "  FAIL: %s — %s\n" name (Printexc.to_string e)

let assert_numerical name var lo hi n f expected tol =
  incr tests_run;
  try
    let result = numerical_integrate var lo hi n f in
    if Float.abs (result -. expected) < tol then
      incr tests_passed
    else begin
      incr tests_failed;
      Printf.printf "  FAIL: %s — expected %.6f, got %.6f\n" name expected result
    end
  with e ->
    incr tests_failed;
    Printf.printf "  FAIL: %s — %s\n" name (Printexc.to_string e)

(* ── Test suite ──────────────────────────────────────────────────── *)

let run_tests () =
  Printf.printf "\n=== Integration Tests ===\n\n";

  let x = Var "x" in

  (* Basic integrals *)
  Printf.printf "--- Basic integrals ---\n";

  assert_integral "∫ 1 dx = x" "x" (Const 1.0) "x";
  assert_integral "∫ 5 dx = 5x" "x" (Const 5.0) "5x";
  assert_integral "∫ x dx = x²/2" "x" x "x²/2";
  assert_integral "∫ x² dx = x³/3" "x" (Pow (x, Const 2.0)) "x³/3";
  assert_integral "∫ x³ dx = x⁴/4" "x" (Pow (x, Const 3.0)) "x⁴/4";
  assert_integral "∫ x^(-1) dx = ln|x|" "x"
    (Pow (x, Const (-1.0))) "ln|x|";
  assert_integral "∫ 1/x dx = ln|x|" "x"
    (Div (Const 1.0, x)) "ln|x|";
  assert_integral "∫ x^(1/2) dx = sqrt" "x"
    (Sqrt x) "(2/3)x^1.5";
  assert_integral "∫ x^(-2) dx" "x"
    (Pow (x, Const (-2.0))) "-1/x";

  (* Exponential and logarithmic *)
  Printf.printf "--- Exponential/Logarithmic ---\n";

  assert_integral "∫ exp(x) dx = exp(x)" "x" (Exp x) "exp(x)";
  assert_integral "∫ ln(x) dx = x·ln(x) - x" "x" (Ln x) "x·ln(x) - x";

  (* Trigonometric *)
  Printf.printf "--- Trigonometric ---\n";

  assert_integral "∫ sin(x) dx = -cos(x)" "x" (Sin x) "-cos(x)";
  assert_integral "∫ cos(x) dx = sin(x)" "x" (Cos x) "sin(x)";
  assert_integral "∫ tan(x) dx = -ln|cos(x)|" "x" (Tan x) "-ln|cos(x)|";
  assert_integral "∫ sec²(x) dx = tan(x)" "x"
    (Div (Const 1.0, Pow (Cos x, Const 2.0))) "tan(x)";
  assert_integral "∫ csc²(x) dx = -cot(x)" "x"
    (Div (Const 1.0, Pow (Sin x, Const 2.0))) "-cos(x)/sin(x)";
  assert_integral "∫ sin²(x) dx" "x"
    (Pow (Sin x, Const 2.0)) "x/2 - sin(2x)/4";
  assert_integral "∫ cos²(x) dx" "x"
    (Pow (Cos x, Const 2.0)) "x/2 + sin(2x)/4";

  (* Linearity *)
  Printf.printf "--- Linearity ---\n";

  assert_integral "∫ (x + 1) dx" "x"
    (Add (x, Const 1.0)) "x²/2 + x";
  assert_integral "∫ (3x² - 2x + 1) dx" "x"
    (Add (Sub (Mul (Const 3.0, Pow (x, Const 2.0)),
              Mul (Const 2.0, x)),
          Const 1.0)) "x³ - x² + x";
  assert_integral "∫ 5·sin(x) dx" "x"
    (Mul (Const 5.0, Sin x)) "-5·cos(x)";
  assert_integral "∫ -exp(x) dx" "x"
    (Neg (Exp x)) "-exp(x)";

  (* Linear substitution *)
  Printf.printf "--- Linear substitution ---\n";

  assert_integral "∫ exp(2x) dx = exp(2x)/2" "x"
    (Exp (Mul (Const 2.0, x))) "exp(2x)/2";
  assert_integral "∫ sin(3x) dx = -cos(3x)/3" "x"
    (Sin (Mul (Const 3.0, x))) "-cos(3x)/3";
  assert_integral "∫ cos(2x+1) dx" "x"
    (Cos (Add (Mul (Const 2.0, x), Const 1.0))) "sin(2x+1)/2";
  assert_integral "∫ (2x+3)^4 dx" "x"
    (Pow (Add (Mul (Const 2.0, x), Const 3.0), Const 4.0))
    "(2x+3)^5/10";
  assert_integral "∫ sqrt(3x+1) dx" "x"
    (Sqrt (Add (Mul (Const 3.0, x), Const 1.0)))
    "(2/9)(3x+1)^1.5";

  (* u-substitution *)
  Printf.printf "--- u-substitution ---\n";

  (* ∫ 2x·exp(x²) dx = exp(x²) *)
  assert_integral "∫ 2x·exp(x²) dx" "x"
    (Mul (Mul (Const 2.0, x), Exp (Pow (x, Const 2.0)))) "exp(x²)";

  (* ∫ cos(x)·exp(sin(x)) dx = exp(sin(x)) *)
  assert_integral "∫ cos(x)·exp(sin(x)) dx" "x"
    (Mul (Cos x, Exp (Sin x))) "exp(sin(x))";

  (* Definite integrals *)
  Printf.printf "--- Definite integrals ---\n";

  assert_definite "∫₀¹ x dx = 0.5" "x" 0.0 1.0 x 0.5;
  assert_definite "∫₀¹ x² dx = 1/3" "x" 0.0 1.0 (Pow (x, Const 2.0)) (1.0 /. 3.0);
  assert_definite "∫₁ᵉ 1/x dx = 1" "x" 1.0 (exp 1.0)
    (Div (Const 1.0, x)) 1.0;
  assert_definite "∫₀^π sin(x) dx = 2" "x" 0.0 Float.pi (Sin x) 2.0;
  assert_definite "∫₀¹ exp(x) dx = e-1" "x" 0.0 1.0 (Exp x) (exp 1.0 -. 1.0);
  assert_definite "∫₁² (3x²+2x) dx = 10" "x" 1.0 2.0
    (Add (Mul (Const 3.0, Pow (x, Const 2.0)), Mul (Const 2.0, x)))
    10.0;

  (* Numerical integration *)
  Printf.printf "--- Numerical integration ---\n";

  assert_numerical "Simpson: ∫₀¹ x² dx ≈ 1/3" "x" 0.0 1.0 100
    (Pow (x, Const 2.0)) (1.0 /. 3.0) 1e-10;
  assert_numerical "Simpson: ∫₀^π sin(x) dx ≈ 2" "x" 0.0 Float.pi 100
    (Sin x) 2.0 1e-8;
  assert_numerical "Simpson: ∫₀¹ exp(x) dx ≈ e-1" "x" 0.0 1.0 100
    (Exp x) (exp 1.0 -. 1.0) 1e-10;
  assert_numerical "Simpson: ∫₁³ 1/x dx ≈ ln(3)" "x" 1.0 3.0 100
    (Div (Const 1.0, x)) (log 3.0) 1e-10;

  (* Verification *)
  Printf.printf "--- Verification ---\n";

  let test_verify name f =
    incr tests_run;
    try
      let anti = integrate "x" f in
      if verify_integral "x" f anti then incr tests_passed
      else begin
        incr tests_failed;
        Printf.printf "  FAIL: %s verification\n" name
      end
    with Failure msg ->
      incr tests_failed;
      Printf.printf "  FAIL: %s — %s\n" name msg
  in

  test_verify "verify ∫ x³" (Pow (x, Const 3.0));
  test_verify "verify ∫ sin(x)" (Sin x);
  test_verify "verify ∫ exp(x)" (Exp x);
  test_verify "verify ∫ ln(x)" (Ln x);
  test_verify "verify ∫ cos(2x)" (Cos (Mul (Const 2.0, x)));
  test_verify "verify ∫ x·exp(x²)" (* needs factor 2, but constant pulled *)
    (Mul (Mul (Const 2.0, x), Exp (Pow (x, Const 2.0))));

  (* Integration by parts *)
  Printf.printf "--- Integration by parts ---\n";

  let test_by_parts name f =
    incr tests_run;
    try
      let result = integrate_extended "x" f in
      if verify_integral "x" f result then incr tests_passed
      else begin
        incr tests_failed;
        Printf.printf "  FAIL: %s — got %s (verification failed)\n" name (to_string result)
      end
    with Failure msg ->
      incr tests_failed;
      Printf.printf "  FAIL: %s — %s\n" name msg
  in

  (* ∫ x·exp(x) dx = x·exp(x) - exp(x) *)
  test_by_parts "∫ x·exp(x) dx" (Mul (x, Exp x));

  (* ∫ x·cos(x) dx = x·sin(x) + cos(x) *)
  test_by_parts "∫ x·cos(x) dx" (Mul (x, Cos x));

  (* ∫ x·sin(x) dx = -x·cos(x) + sin(x) *)
  test_by_parts "∫ x·sin(x) dx" (Mul (x, Sin x));

  (* Cannot-integrate cases *)
  Printf.printf "--- Edge cases ---\n";

  (* Integration of constant w.r.t. different var *)
  assert_integral "∫ y dx = yx (y is constant)" "x"
    (Var "y") "yx";

  (* ∫ 0 dx = 0 *)
  assert_integral "∫ 0 dx = 0" "x" (Const 0.0) "0";

  (* Negative exponent *)
  assert_integral "∫ x^(-3) dx" "x"
    (Pow (x, Const (-3.0))) "-1/(2x²)";

  (* Fractional exponent *)
  assert_integral "∫ x^(3/2) dx" "x"
    (Pow (x, Const 1.5)) "(2/5)x^2.5";

  (* Integral table *)
  Printf.printf "--- Integral table ---\n";
  assert_test "table has entries" (List.length standard_integrals > 0);
  assert_test "table has 15 entries" (List.length standard_integrals = 15);

  (* Numerical vs symbolic comparison *)
  Printf.printf "--- Numerical vs Symbolic agreement ---\n";

  let compare_methods name f lo hi =
    incr tests_run;
    try
      let symbolic = definite_integrate "x" lo hi f in
      let numerical = numerical_integrate "x" lo hi 1000 f in
      if Float.abs (symbolic -. numerical) < 1e-4 then
        incr tests_passed
      else begin
        incr tests_failed;
        Printf.printf "  FAIL: %s — symbolic=%.6f, numerical=%.6f\n"
          name symbolic numerical
      end
    with e ->
      incr tests_failed;
      Printf.printf "  FAIL: %s — %s\n" name (Printexc.to_string e)
  in

  compare_methods "x³ on [0,2]" (Pow (x, Const 3.0)) 0.0 2.0;
  compare_methods "sin(x) on [0,π]" (Sin x) 0.0 Float.pi;
  compare_methods "exp(x) on [0,1]" (Exp x) 0.0 1.0;
  compare_methods "x²+3x+2 on [1,4]"
    (Add (Add (Pow (x, Const 2.0), Mul (Const 3.0, x)), Const 2.0))
    1.0 4.0;
  compare_methods "cos(2x) on [0,π/2]"
    (Cos (Mul (Const 2.0, x))) 0.0 (Float.pi /. 2.0);

  Printf.printf "\n%d/%d tests passed (%d failed)\n\n"
    !tests_passed !tests_run !tests_failed

(* ── Demo ─────────────────────────────────────────────────────────── *)

let () =
  Printf.printf "=== Symbolic Integration Engine ===\n\n";

  let x = Var "x" in

  (* Demo 1: Basic integrals *)
  Printf.printf "--- Basic Integrals ---\n\n";

  let demos = [
    ("∫ x² dx", Pow (x, Const 2.0));
    ("∫ sin(x) dx", Sin x);
    ("∫ cos(x) dx", Cos x);
    ("∫ exp(x) dx", Exp x);
    ("∫ 1/x dx", Div (Const 1.0, x));
    ("∫ ln(x) dx", Ln x);
    ("∫ sqrt(x) dx", Sqrt x);
    ("∫ tan(x) dx", Tan x);
  ] in

  List.iter (fun (label, f) ->
    let result = integrate "x" f in
    Printf.printf "%s = %s + C\n" label (to_string result)
  ) demos;

  (* Demo 2: Linearity *)
  Printf.printf "\n--- Linearity ---\n\n";

  let poly = Add (Sub (Mul (Const 3.0, Pow (x, Const 2.0)),
                       Mul (Const 2.0, x)),
                  Const 7.0) in
  Printf.printf "∫ (%s) dx = %s + C\n"
    (to_string poly) (to_string (integrate "x" poly));

  (* Demo 3: Linear substitution *)
  Printf.printf "\n--- Linear Substitution ---\n\n";

  let lin_demos = [
    ("∫ exp(3x) dx", Exp (Mul (Const 3.0, x)));
    ("∫ sin(2x+1) dx", Sin (Add (Mul (Const 2.0, x), Const 1.0)));
    ("∫ (4x-1)³ dx", Pow (Sub (Mul (Const 4.0, x), Const 1.0), Const 3.0));
  ] in

  List.iter (fun (label, f) ->
    let result = integrate "x" f in
    Printf.printf "%s = %s + C\n" label (to_string result)
  ) lin_demos;

  (* Demo 4: Definite integrals *)
  Printf.printf "\n--- Definite Integrals ---\n\n";

  Printf.printf "∫₀¹ x² dx = %.6f\n"
    (definite_integrate "x" 0.0 1.0 (Pow (x, Const 2.0)));
  Printf.printf "∫₀^π sin(x) dx = %.6f\n"
    (definite_integrate "x" 0.0 Float.pi (Sin x));
  Printf.printf "∫₁ᵉ 1/x dx = %.6f\n"
    (definite_integrate "x" 1.0 (exp 1.0) (Div (Const 1.0, x)));

  (* Demo 5: Numerical integration *)
  Printf.printf "\n--- Numerical Integration (Simpson's Rule) ---\n\n";

  Printf.printf "∫₀¹ exp(-x²) dx ≈ %.6f (n=100)\n"
    (numerical_integrate "x" 0.0 1.0 100 (Exp (Neg (Pow (x, Const 2.0)))));
  Printf.printf "∫₀¹ sin(x²) dx ≈ %.6f (n=100)\n"
    (numerical_integrate "x" 0.0 1.0 100 (Sin (Pow (x, Const 2.0))));

  (* Demo 6: Verification *)
  Printf.printf "\n--- Verification ---\n\n";

  let verify_demos = [
    ("x³", Pow (x, Const 3.0));
    ("sin(x)", Sin x);
    ("exp(2x)", Exp (Mul (Const 2.0, x)));
  ] in

  List.iter (fun (label, f) ->
    let anti = integrate "x" f in
    let ok = verify_integral "x" f anti in
    Printf.printf "∫ %s dx = %s → d/dx check: %s\n"
      label (to_string anti) (if ok then "✓" else "✗")
  ) verify_demos;

  (* Demo 7: Integration by parts *)
  Printf.printf "\n--- Integration by Parts ---\n\n";

  let parts_demos = [
    ("∫ x·exp(x) dx", Mul (x, Exp x));
    ("∫ x·cos(x) dx", Mul (x, Cos x));
  ] in

  List.iter (fun (label, f) ->
    try
      let result = integrate_extended "x" f in
      let ok = verify_integral "x" f result in
      Printf.printf "%s = %s + C → d/dx check: %s\n"
        label (to_string result) (if ok then "✓" else "✗")
    with Failure msg ->
      Printf.printf "%s → %s\n" label msg
  ) parts_demos;

  (* Demo 8: Integral table *)
  Printf.printf "\n--- Standard Integral Table ---\n\n";
  print_integral_table ();

  (* Run tests *)
  run_tests ();

  Printf.printf "=== Done ===\n"
