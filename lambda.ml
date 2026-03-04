(* lambda.ml — Untyped Lambda Calculus Interpreter
 *
 * A complete implementation of the untyped lambda calculus, the
 * foundation of functional programming and computability theory.
 *
 * Concepts demonstrated:
 * - Algebraic data types for lambda terms
 * - Alpha-equivalence and capture-avoiding substitution
 * - De Bruijn index representation (nameless terms)
 * - Beta reduction strategies (normal order, applicative order, call-by-value)
 * - Church encodings (booleans, numerals, pairs, lists)
 * - Fixed-point combinators (Y, Z, Turing)
 * - Classic combinators (S, K, I, B, C, W, Omega)
 * - Step-limited evaluation to handle non-termination
 * - Pretty printing with minimal parenthesization
 *
 * Usage:
 *   let id   = Lam ("x", Var "x")
 *   let app  = App (id, Var "y")
 *   let res  = eval_normal ~limit:100 app     (* Var "y" *)
 *   let s    = to_string res                   (* "y" *)
 *   let n3   = church_numeral 3                (* λf.λx.f (f (f x)) *)
 *   let six  = App (App (church_mul, n3), church_numeral 2)
 *   let six' = eval_normal ~limit:1000 six     (* λf.λx.f^6 x *)
 *)

(* ================================================================ *)
(* 1. TERM REPRESENTATION                                          *)
(* ================================================================ *)

(** Lambda term with named variables. *)
type term =
  | Var of string              (** Variable reference *)
  | Lam of string * term       (** Lambda abstraction: λx.body *)
  | App of term * term         (** Application: (f arg) *)

(** De Bruijn indexed term (nameless representation). *)
type db_term =
  | DBVar of int               (** Variable as index (0 = innermost binder) *)
  | DBLam of db_term           (** Lambda abstraction (no name needed) *)
  | DBApp of db_term * db_term (** Application *)

(* ================================================================ *)
(* 2. PRETTY PRINTING                                               *)
(* ================================================================ *)

(** Convert a term to a human-readable string with minimal parentheses.
    - λx.body  never needs outer parens
    - (f x)    application is left-associative, so f x y = (f x) y
    - λx.M N   means λx.(M N), not (λx.M) N *)
let rec to_string = function
  | Var x -> x
  | Lam (x, body) -> "λ" ^ x ^ "." ^ to_string body
  | App (f, arg) ->
    let f_str = match f with
      | Lam _ -> "(" ^ to_string f ^ ")"
      | _ -> to_string f
    in
    let arg_str = match arg with
      | Var x -> x
      | _ -> "(" ^ to_string arg ^ ")"
    in
    f_str ^ " " ^ arg_str

(** Convert a De Bruijn term to string, using numeric indices. *)
let rec db_to_string = function
  | DBVar i -> string_of_int i
  | DBLam body -> "λ." ^ db_to_string body
  | DBApp (f, arg) ->
    let f_str = match f with
      | DBLam _ -> "(" ^ db_to_string f ^ ")"
      | _ -> db_to_string f
    in
    let arg_str = match arg with
      | DBVar i -> string_of_int i
      | _ -> "(" ^ db_to_string arg ^ ")"
    in
    f_str ^ " " ^ arg_str

(* ================================================================ *)
(* 3. FREE VARIABLES AND ALPHA-EQUIVALENCE                          *)
(* ================================================================ *)

module StringSet = Set.Make(String)

(** Compute the set of free variables in a term. *)
let rec free_vars = function
  | Var x -> StringSet.singleton x
  | Lam (x, body) -> StringSet.remove x (free_vars body)
  | App (f, arg) -> StringSet.union (free_vars f) (free_vars arg)

(** Check if a variable occurs free in a term. *)
let is_free x t = StringSet.mem x (free_vars t)

(** Generate a fresh variable name not in the given set. *)
let fresh_var avoid base =
  if not (StringSet.mem base avoid) then base
  else
    let rec try_n n =
      let candidate = base ^ string_of_int n in
      if StringSet.mem candidate avoid then try_n (n + 1)
      else candidate
    in
    try_n 0

(** Rename all bound occurrences of [old_name] to [new_name] in body. *)
let rec rename old_name new_name = function
  | Var x -> if x = old_name then Var new_name else Var x
  | Lam (x, body) ->
    if x = old_name then Lam (new_name, rename old_name new_name body)
    else Lam (x, rename old_name new_name body)
  | App (f, arg) -> App (rename old_name new_name f, rename old_name new_name arg)

(** Capture-avoiding substitution: t[x := s]
    Replaces free occurrences of x in t with s, renaming bound
    variables as needed to avoid capturing free variables of s. *)
let rec subst x s = function
  | Var y -> if y = x then s else Var y
  | App (f, arg) -> App (subst x s f, subst x s arg)
  | Lam (y, body) ->
    if y = x then
      (* x is shadowed by this binder, no substitution inside *)
      Lam (y, body)
    else if not (is_free x body) then
      (* x doesn't appear free in body, nothing to do *)
      Lam (y, body)
    else if not (is_free y s) then
      (* No capture risk, substitute directly *)
      Lam (y, subst x s body)
    else
      (* y is free in s and x is free in body — must rename y *)
      let avoid = StringSet.union (StringSet.union (free_vars s) (free_vars body))
                    (StringSet.singleton x) in
      let y' = fresh_var avoid y in
      Lam (y', subst x s (rename y y' body))

(** Alpha-equivalence: structurally equal up to bound variable renaming. *)
let alpha_equiv t1 t2 =
  let rec equiv env1 env2 depth = function
    | (Var x, Var y) ->
      let dx = try List.assoc x env1 with Not_found -> -1 in
      let dy = try List.assoc y env2 with Not_found -> -1 in
      if dx >= 0 && dy >= 0 then dx = dy        (* both bound, same depth *)
      else if dx < 0 && dy < 0 then x = y       (* both free, same name *)
      else false                                  (* one bound, one free *)
    | (Lam (x, b1), Lam (y, b2)) ->
      equiv ((x, depth) :: env1) ((y, depth) :: env2) (depth + 1) (b1, b2)
    | (App (f1, a1), App (f2, a2)) ->
      equiv env1 env2 depth (f1, f2) && equiv env1 env2 depth (a1, a2)
    | _ -> false
  in
  equiv [] [] 0 (t1, t2)

(* ================================================================ *)
(* 4. DE BRUIJN INDEX CONVERSION                                    *)
(* ================================================================ *)

(** Convert a named term to De Bruijn representation. *)
let to_de_bruijn t =
  let rec go env = function
    | Var x ->
      (match List.assoc_opt x env with
       | Some i -> DBVar i
       | None -> DBVar (-1))  (* free variable sentinel *)
    | Lam (x, body) ->
      let env' = (x, 0) :: List.map (fun (n, i) -> (n, i + 1)) env in
      DBLam (go env' body)
    | App (f, arg) -> DBApp (go env f, go env arg)
  in
  go [] t

(** Convert De Bruijn term back to named form using generated names. *)
let from_de_bruijn t =
  let name_of i = String.make 1 (Char.chr (Char.code 'a' + (i mod 26))) ^
                  (if i >= 26 then string_of_int (i / 26) else "") in
  let rec go depth = function
    | DBVar i ->
      if i >= 0 && i < depth then Var (name_of (depth - 1 - i))
      else Var ("free" ^ string_of_int i)
    | DBLam body ->
      let x = name_of depth in
      Lam (x, go (depth + 1) body)
    | DBApp (f, arg) -> App (go depth f, go depth arg)
  in
  go 0 t

(** De Bruijn shift: increment free variables by [d], above cutoff [c]. *)
let rec db_shift d c = function
  | DBVar i -> if i >= c then DBVar (i + d) else DBVar i
  | DBLam body -> DBLam (db_shift d (c + 1) body)
  | DBApp (f, arg) -> DBApp (db_shift d c f, db_shift d c arg)

(** De Bruijn substitution: replace variable [j] with term [s]. *)
let rec db_subst j s = function
  | DBVar i -> if i = j then s else DBVar i
  | DBLam body -> DBLam (db_subst (j + 1) (db_shift 1 0 s) body)
  | DBApp (f, arg) -> DBApp (db_subst j s f, db_subst j s arg)

(** Beta reduction in De Bruijn: (λ.body) arg → body[0:=arg], shifted. *)
let db_beta body arg =
  db_shift (-1) 0 (db_subst 0 (db_shift 1 0 arg) body)

(* ================================================================ *)
(* 5. REDUCTION STRATEGIES                                          *)
(* ================================================================ *)

type reduction_result =
  | Normal of term      (** Reached normal form *)
  | Stuck of term       (** Hit step limit, not fully reduced *)

(** Try one step of beta reduction (leftmost-outermost = normal order).
    Returns None if already in normal form. *)
let rec step_normal = function
  | Var _ -> None
  | App (Lam (x, body), arg) -> Some (subst x arg body)
  | App (f, arg) ->
    (match step_normal f with
     | Some f' -> Some (App (f', arg))
     | None ->
       match step_normal arg with
       | Some arg' -> Some (App (f, arg'))
       | None -> None)
  | Lam (x, body) ->
    (match step_normal body with
     | Some body' -> Some (Lam (x, body'))
     | None -> None)

(** Try one step of applicative-order reduction (leftmost-innermost). *)
let rec step_applicative = function
  | Var _ -> None
  | App (Lam (x, body), arg) ->
    (* First reduce arg to normal form step by step *)
    (match step_applicative arg with
     | Some arg' -> Some (App (Lam (x, body), arg'))
     | None ->
       (* arg is in normal form, do the beta step *)
       Some (subst x arg body))
  | App (f, arg) ->
    (match step_applicative f with
     | Some f' -> Some (App (f', arg))
     | None ->
       match step_applicative arg with
       | Some arg' -> Some (App (f, arg'))
       | None -> None)
  | Lam (x, body) ->
    (match step_applicative body with
     | Some body' -> Some (Lam (x, body'))
     | None -> None)

(** Try one step of call-by-value reduction. *)
let rec step_cbv = function
  | Var _ -> None
  | Lam _ -> None  (* values don't reduce *)
  | App (Lam (x, body), arg) ->
    (match step_cbv arg with
     | Some arg' -> Some (App (Lam (x, body), arg'))
     | None ->
       (* arg is a value, do the beta step *)
       Some (subst x arg body))
  | App (f, arg) ->
    (match step_cbv f with
     | Some f' -> Some (App (f', arg))
     | None ->
       match step_cbv arg with
       | Some arg' -> Some (App (f, arg'))
       | None -> None)

(** Multi-step evaluation with step limit. *)
let eval_with_strategy step_fn ?(limit=1000) t =
  let rec go fuel t =
    if fuel <= 0 then Stuck t
    else match step_fn t with
      | None -> Normal t
      | Some t' -> go (fuel - 1) t'
  in
  go limit t

let eval_normal ?limit t = eval_with_strategy step_normal ?limit t
let eval_applicative ?limit t = eval_with_strategy step_applicative ?limit t
let eval_cbv ?limit t = eval_with_strategy step_cbv ?limit t

(** Count reduction steps needed (returns None if exceeds limit). *)
let count_steps step_fn ?(limit=10000) t =
  let rec go fuel count t =
    if fuel <= 0 then None
    else match step_fn t with
      | None -> Some count
      | Some t' -> go (fuel - 1) (count + 1) t'
  in
  go limit 0 t

(** Collect all intermediate terms during reduction. *)
let trace step_fn ?(limit=100) t =
  let rec go fuel acc t =
    if fuel <= 0 then List.rev (t :: acc)
    else match step_fn t with
      | None -> List.rev (t :: acc)
      | Some t' -> go (fuel - 1) (t :: acc) t'
  in
  go limit [] t

(* ================================================================ *)
(* 6. CHURCH ENCODINGS                                              *)
(* ================================================================ *)

(* ── Booleans ── *)

let church_true  = Lam ("t", Lam ("f", Var "t"))
let church_false = Lam ("t", Lam ("f", Var "f"))
let church_and   = Lam ("p", Lam ("q", App (App (Var "p", Var "q"), Var "p")))
let church_or    = Lam ("p", Lam ("q", App (App (Var "p", Var "p"), Var "q")))
let church_not   = Lam ("p", Lam ("t", Lam ("f", App (App (Var "p", Var "f"), Var "t"))))
let church_if    = Lam ("p", Lam ("a", Lam ("b", App (App (Var "p", Var "a"), Var "b"))))

(* ── Numerals ── *)

(** Church numeral n = λf.λx. f^n x *)
let church_numeral n =
  let rec apply_n n = function
    | _ when n <= 0 -> Var "x"
    | f -> App (Var "f", apply_n (n - 1) f)
  in
  Lam ("f", Lam ("x", apply_n n (Var "f")))

let church_succ = Lam ("n", Lam ("f", Lam ("x",
  App (Var "f", App (App (Var "n", Var "f"), Var "x")))))

let church_add = Lam ("m", Lam ("n", Lam ("f", Lam ("x",
  App (App (Var "m", Var "f"), App (App (Var "n", Var "f"), Var "x"))))))

let church_mul = Lam ("m", Lam ("n", Lam ("f",
  App (Var "m", App (Var "n", Var "f")))))

let church_pow = Lam ("m", Lam ("n", App (Var "n", Var "m")))

let church_is_zero = Lam ("n",
  App (App (Var "n", Lam ("_", church_false)), church_true))

(** Predecessor using the pairing trick. *)
let church_pred =
  let pair  = Lam ("a", Lam ("b", Lam ("f", App (App (Var "f", Var "a"), Var "b")))) in
  let fst_  = Lam ("p", App (Var "p", Lam ("a", Lam ("b", Var "a")))) in
  let snd_  = Lam ("p", App (Var "p", Lam ("a", Lam ("b", Var "b")))) in
  let zero  = church_numeral 0 in
  let shift = Lam ("p",
    App (App (pair, App (snd_, Var "p")),
         App (church_succ, App (snd_, Var "p")))) in
  Lam ("n", App (fst_, App (App (Var "n", shift), App (App (pair, zero), zero))))

let church_sub = Lam ("m", Lam ("n",
  App (App (Var "n", church_pred), Var "m")))

(** Extract an integer from a Church numeral by evaluation.
    Returns None if the term doesn't reduce to a numeral form. *)
let church_to_int ?(limit=5000) t =
  let f_var = Var "__f" and x_var = Var "__x" in
  let applied = App (App (t, Lam ("__n", App (Var "__succ", Var "__n"))), x_var) in
  match eval_normal ~limit applied with
  | Normal result ->
    let rec count = function
      | v when alpha_equiv v x_var -> Some 0
      | App (Var "__succ", rest) ->
        (match count rest with Some n -> Some (n + 1) | None -> None)
      | _ -> None
    in
    (* Alternative: apply to f and x, then count applications of f *)
    let applied2 = App (App (t, f_var), x_var) in
    (match eval_normal ~limit applied2 with
     | Normal result2 ->
       let rec count_f = function
         | v when alpha_equiv v x_var -> Some 0
         | App (f, rest) when alpha_equiv f f_var ->
           (match count_f rest with Some n -> Some (n + 1) | None -> None)
         | _ -> None
       in
       count_f result2
     | Stuck _ -> None)
  | Stuck _ -> None

(** Extract a boolean from a Church boolean by evaluation. *)
let church_to_bool ?(limit=1000) t =
  let result = App (App (t, Var "__true"), Var "__false") in
  match eval_normal ~limit result with
  | Normal (Var "__true") -> Some true
  | Normal (Var "__false") -> Some false
  | _ -> None

(* ── Pairs ── *)

let church_pair = Lam ("a", Lam ("b", Lam ("f", App (App (Var "f", Var "a"), Var "b"))))
let church_fst  = Lam ("p", App (Var "p", Lam ("a", Lam ("b", Var "a"))))
let church_snd  = Lam ("p", App (Var "p", Lam ("a", Lam ("b", Var "b"))))

(* ── Lists (Scott encoding) ── *)

let church_nil   = Lam ("c", Lam ("n", Var "n"))
let church_cons  = Lam ("h", Lam ("t", Lam ("c", Lam ("n",
  App (App (Var "c", Var "h"), App (App (Var "t", Var "c"), Var "n"))))))
let church_is_nil = Lam ("l",
  App (App (Var "l", Lam ("_h", Lam ("_t", church_false))), church_true))

(* ================================================================ *)
(* 7. CLASSIC COMBINATORS                                           *)
(* ================================================================ *)

let comb_I = Lam ("x", Var "x")                                   (* Identity *)
let comb_K = Lam ("x", Lam ("y", Var "x"))                        (* Constant *)
let comb_S = Lam ("x", Lam ("y", Lam ("z",                        (* Substitution *)
  App (App (Var "x", Var "z"), App (Var "y", Var "z")))))
let comb_B = Lam ("f", Lam ("g", Lam ("x",                        (* Composition *)
  App (Var "f", App (Var "g", Var "x")))))
let comb_C = Lam ("f", Lam ("x", Lam ("y",                        (* Flip *)
  App (App (Var "f", Var "y"), Var "x"))))
let comb_W = Lam ("f", Lam ("x",                                  (* Duplicate *)
  App (App (Var "f", Var "x"), Var "x")))
let comb_omega = Lam ("x", App (Var "x", Var "x"))                (* Self-application *)
let comb_Omega = App (comb_omega, comb_omega)                      (* Divergent term *)

(** Y combinator (Curry's fixed-point): Y f = f (Y f)
    Only works under normal-order evaluation. *)
let comb_Y = Lam ("f",
  App (Lam ("x", App (Var "f", App (Var "x", Var "x"))),
       Lam ("x", App (Var "f", App (Var "x", Var "x")))))

(** Z combinator (strict fixed-point, works under CBV):
    Z f = f (λv. Z f v) *)
let comb_Z = Lam ("f",
  App (Lam ("x", App (Var "f", Lam ("v", App (App (Var "x", Var "x"), Var "v")))),
       Lam ("x", App (Var "f", Lam ("v", App (App (Var "x", Var "x"), Var "v"))))))

(** Turing's fixed-point combinator: Θ = (λx.λf. f (x x f)) (λx.λf. f (x x f)) *)
let comb_Theta =
  let half = Lam ("x", Lam ("f", App (Var "f", App (App (Var "x", Var "x"), Var "f")))) in
  App (half, half)

(* ================================================================ *)
(* 8. TERM SIZE AND DEPTH                                           *)
(* ================================================================ *)

(** Count the number of nodes in a term (AST size). *)
let rec size = function
  | Var _ -> 1
  | Lam (_, body) -> 1 + size body
  | App (f, arg) -> 1 + size f + size arg

(** Maximum nesting depth of a term. *)
let rec depth = function
  | Var _ -> 0
  | Lam (_, body) -> 1 + depth body
  | App (f, arg) -> 1 + max (depth f) (depth arg)

(** Count the number of beta-redexes in a term. *)
let rec count_redexes = function
  | Var _ -> 0
  | Lam (_, body) -> count_redexes body
  | App (Lam (_, body), arg) -> 1 + count_redexes body + count_redexes arg
  | App (f, arg) -> count_redexes f + count_redexes arg

(* ================================================================ *)
(* 9. PARSING                                                       *)
(* ================================================================ *)

(** Simple parser for lambda calculus expressions.
    Syntax:
      term := atom+                (application is juxtaposition)
      atom := variable | '(' term ')' | 'λ' var '.' term | '\\' var '.' term
      variable := [a-zA-Z_][a-zA-Z0-9_']* *)

exception Parse_error of string

let parse s =
  let len = String.length s in
  let pos = ref 0 in

  let peek () = if !pos < len then Some s.[!pos] else None in
  let advance () = pos := !pos + 1 in
  let skip_ws () = while !pos < len && (s.[!pos] = ' ' || s.[!pos] = '\t' || s.[!pos] = '\n') do advance () done in

  let is_var_start c = (c >= 'a' && c <= 'z') || (c >= 'A' && c <= 'Z') || c = '_' in
  let is_var_cont c = is_var_start c || (c >= '0' && c <= '9') || c = '\'' in

  let parse_var () =
    skip_ws ();
    let start = !pos in
    if !pos >= len || not (is_var_start s.[!pos]) then
      raise (Parse_error (Printf.sprintf "Expected variable at position %d" !pos));
    while !pos < len && is_var_cont s.[!pos] do advance () done;
    String.sub s start (!pos - start)
  in

  let rec parse_term () =
    skip_ws ();
    let atoms = ref [] in
    let continue = ref true in
    while !continue do
      skip_ws ();
      match peek () with
      | Some c when c = '\\' || c = '\xce' (* UTF-8 λ first byte *) ->
        if !atoms = [] then begin
          atoms := [parse_lambda ()];
          continue := false  (* lambda extends to end *)
        end else
          continue := false
      | Some '(' ->
        advance ();
        let t = parse_term () in
        skip_ws ();
        (match peek () with
         | Some ')' -> advance ()
         | _ -> raise (Parse_error "Expected ')'"));
        atoms := t :: !atoms
      | Some c when is_var_start c ->
        atoms := (Var (parse_var ())) :: !atoms
      | _ -> continue := false
    done;
    match List.rev !atoms with
    | [] -> raise (Parse_error "Empty expression")
    | [single] -> single
    | first :: rest -> List.fold_left (fun f a -> App (f, a)) first rest

  and parse_lambda () =
    skip_ws ();
    (match peek () with
     | Some '\\' -> advance ()
     | Some '\xce' ->
       advance ();
       if !pos < len && s.[!pos] = '\xbb' then advance ()  (* UTF-8 λ = 0xCE 0xBB *)
       else raise (Parse_error "Invalid UTF-8 lambda character")
     | _ -> raise (Parse_error "Expected '\\' or 'λ'"));
    let x = parse_var () in
    skip_ws ();
    (match peek () with
     | Some '.' -> advance ()
     | _ -> raise (Parse_error "Expected '.' after lambda variable"));
    let body = parse_term () in
    Lam (x, body)
  in

  let result = parse_term () in
  skip_ws ();
  if !pos < len then
    raise (Parse_error (Printf.sprintf "Unexpected character '%c' at position %d" s.[!pos] !pos));
  result

(* ================================================================ *)
(* 10. TESTS                                                        *)
(* ================================================================ *)

let () =
  let pass = ref 0 in
  let fail = ref 0 in
  let test name f =
    try f (); incr pass; Printf.printf "  ✓ %s\n" name
    with e ->
      incr fail;
      Printf.printf "  ✗ %s: %s\n" name (Printexc.to_string e)
  in
  let assert_eq a b msg =
    if a <> b then failwith (Printf.sprintf "%s: got %s, expected %s" msg
      (match a with _ -> "<value>") (match b with _ -> "<value>"))
  in
  let assert_true b msg = if not b then failwith msg in
  let assert_alpha_eq t1 t2 msg =
    if not (alpha_equiv t1 t2) then
      failwith (Printf.sprintf "%s: %s ≠α %s" msg (to_string t1) (to_string t2))
  in
  let unwrap_normal = function
    | Normal t -> t
    | Stuck t -> failwith (Printf.sprintf "Stuck at: %s" (to_string t))
  in

  Printf.printf "\n🧪 Lambda Calculus Tests\n";
  Printf.printf "========================\n\n";

  Printf.printf "── Pretty Printing ──\n";
  test "variable" (fun () ->
    assert_eq (to_string (Var "x")) "x" "var");
  test "identity" (fun () ->
    assert_eq (to_string (Lam ("x", Var "x"))) "λx.x" "id");
  test "application" (fun () ->
    assert_eq (to_string (App (Var "f", Var "x"))) "f x" "app");
  test "nested lambda" (fun () ->
    assert_eq (to_string (Lam ("x", Lam ("y", Var "x")))) "λx.λy.x" "K");
  test "app of lambda" (fun () ->
    let s = to_string (App (Lam ("x", Var "x"), Var "y")) in
    assert_true (String.length s > 0) "non-empty");

  Printf.printf "\n── Free Variables ──\n";
  test "free var in var" (fun () ->
    assert_true (StringSet.equal (free_vars (Var "x")) (StringSet.singleton "x")) "fv(x)");
  test "bound var not free" (fun () ->
    assert_true (StringSet.is_empty (free_vars (Lam ("x", Var "x")))) "fv(λx.x)");
  test "free in body" (fun () ->
    let fv = free_vars (Lam ("x", App (Var "x", Var "y"))) in
    assert_true (StringSet.mem "y" fv && not (StringSet.mem "x" fv)) "fv(λx.xy)");
  test "multiple free" (fun () ->
    let fv = free_vars (App (Var "x", Var "y")) in
    assert_eq (StringSet.cardinal fv) 2 "fv(x y)");

  Printf.printf "\n── Substitution ──\n";
  test "subst var" (fun () ->
    assert_alpha_eq (subst "x" (Var "y") (Var "x")) (Var "y") "x[x:=y]");
  test "subst different var" (fun () ->
    assert_alpha_eq (subst "x" (Var "y") (Var "z")) (Var "z") "z[x:=y]");
  test "subst shadowed" (fun () ->
    let t = Lam ("x", Var "x") in
    assert_alpha_eq (subst "x" (Var "y") t) t "shadowed");
  test "capture-avoiding" (fun () ->
    (* (λy.x)[x:=y] should NOT become λy.y *)
    let result = subst "x" (Var "y") (Lam ("y", Var "x")) in
    assert_true (is_free "y" result) "capture avoided");

  Printf.printf "\n── Alpha-Equivalence ──\n";
  test "identical terms" (fun () ->
    assert_true (alpha_equiv (Var "x") (Var "x")) "x =α x");
  test "different vars" (fun () ->
    assert_true (not (alpha_equiv (Var "x") (Var "y"))) "x ≠α y");
  test "renamed binder" (fun () ->
    assert_true (alpha_equiv (Lam ("x", Var "x")) (Lam ("y", Var "y"))) "λx.x =α λy.y");
  test "nested renamed" (fun () ->
    let t1 = Lam ("a", Lam ("b", App (Var "a", Var "b"))) in
    let t2 = Lam ("x", Lam ("y", App (Var "x", Var "y"))) in
    assert_true (alpha_equiv t1 t2) "λa.λb.ab =α λx.λy.xy");

  Printf.printf "\n── Beta Reduction ──\n";
  test "identity applied" (fun () ->
    let result = unwrap_normal (eval_normal ~limit:10 (App (comb_I, Var "z"))) in
    assert_alpha_eq result (Var "z") "I z → z");
  test "K combinator" (fun () ->
    let result = unwrap_normal (eval_normal ~limit:10
      (App (App (comb_K, Var "a"), Var "b"))) in
    assert_alpha_eq result (Var "a") "K a b → a");
  test "S combinator" (fun () ->
    let result = unwrap_normal (eval_normal ~limit:100
      (App (App (App (comb_S, comb_K), comb_K), Var "q"))) in
    assert_alpha_eq result (Var "q") "S K K q → q");
  test "multiple steps" (fun () ->
    let t = App (App (Lam ("x", Lam ("y", App (Var "x", Var "y"))),
                      Lam ("z", Var "z")), Var "w") in
    let result = unwrap_normal (eval_normal ~limit:100 t) in
    assert_alpha_eq result (Var "w") "(λx.λy.x y)(λz.z) w → w");

  Printf.printf "\n── Applicative Order ──\n";
  test "simple app-order" (fun () ->
    let result = unwrap_normal (eval_applicative ~limit:10
      (App (comb_I, Var "a"))) in
    assert_alpha_eq result (Var "a") "I a →app a");
  test "K drops arg in app-order" (fun () ->
    let result = unwrap_normal (eval_applicative ~limit:20
      (App (App (comb_K, Var "a"), Var "b"))) in
    assert_alpha_eq result (Var "a") "K a b →app a");

  Printf.printf "\n── Call-by-Value ──\n";
  test "simple cbv" (fun () ->
    let result = unwrap_normal (eval_cbv ~limit:10
      (App (comb_I, Var "v"))) in
    assert_alpha_eq result (Var "v") "I v →cbv v");

  Printf.printf "\n── Church Booleans ──\n";
  test "true extracts first" (fun () ->
    assert_eq (church_to_bool church_true) (Some true) "true");
  test "false extracts second" (fun () ->
    assert_eq (church_to_bool church_false) (Some false) "false");
  test "and true true" (fun () ->
    let r = App (App (church_and, church_true), church_true) in
    assert_eq (church_to_bool (unwrap_normal (eval_normal ~limit:100 r))) (Some true) "T∧T");
  test "and true false" (fun () ->
    let r = App (App (church_and, church_true), church_false) in
    assert_eq (church_to_bool (unwrap_normal (eval_normal ~limit:100 r))) (Some false) "T∧F");
  test "or false true" (fun () ->
    let r = App (App (church_or, church_false), church_true) in
    assert_eq (church_to_bool (unwrap_normal (eval_normal ~limit:100 r))) (Some true) "F∨T");
  test "not true" (fun () ->
    let r = App (church_not, church_true) in
    assert_eq (church_to_bool (unwrap_normal (eval_normal ~limit:100 r))) (Some false) "¬T");

  Printf.printf "\n── Church Numerals ──\n";
  test "zero" (fun () ->
    assert_eq (church_to_int (church_numeral 0)) (Some 0) "0");
  test "three" (fun () ->
    assert_eq (church_to_int (church_numeral 3)) (Some 3) "3");
  test "succ 2 = 3" (fun () ->
    let r = App (church_succ, church_numeral 2) in
    assert_eq (church_to_int (unwrap_normal (eval_normal ~limit:200 r))) (Some 3) "S(2)");
  test "add 2 3 = 5" (fun () ->
    let r = App (App (church_add, church_numeral 2), church_numeral 3) in
    assert_eq (church_to_int (unwrap_normal (eval_normal ~limit:500 r))) (Some 5) "2+3");
  test "mul 2 3 = 6" (fun () ->
    let r = App (App (church_mul, church_numeral 2), church_numeral 3) in
    assert_eq (church_to_int (unwrap_normal (eval_normal ~limit:500 r))) (Some 6) "2×3");
  test "is_zero 0 = true" (fun () ->
    let r = App (church_is_zero, church_numeral 0) in
    assert_eq (church_to_bool (unwrap_normal (eval_normal ~limit:100 r))) (Some true) "0?");
  test "is_zero 3 = false" (fun () ->
    let r = App (church_is_zero, church_numeral 3) in
    assert_eq (church_to_bool (unwrap_normal (eval_normal ~limit:100 r))) (Some false) "3?");

  Printf.printf "\n── Church Pairs ──\n";
  test "fst (pair a b) = a" (fun () ->
    let p = App (App (church_pair, Var "a"), Var "b") in
    let r = App (church_fst, p) in
    assert_alpha_eq (unwrap_normal (eval_normal ~limit:100 r)) (Var "a") "fst");
  test "snd (pair a b) = b" (fun () ->
    let p = App (App (church_pair, Var "a"), Var "b") in
    let r = App (church_snd, p) in
    assert_alpha_eq (unwrap_normal (eval_normal ~limit:100 r)) (Var "b") "snd");

  Printf.printf "\n── De Bruijn Indices ──\n";
  test "var to de bruijn" (fun () ->
    let db = to_de_bruijn (Lam ("x", Var "x")) in
    assert_eq (db_to_string db) "λ.0" "λx.x → λ.0");
  test "nested to de bruijn" (fun () ->
    let t = Lam ("x", Lam ("y", App (Var "x", Var "y"))) in
    let db = to_de_bruijn t in
    assert_eq (db_to_string db) "λ.λ.1 0" "λx.λy.x y → λ.λ.1 0");
  test "roundtrip de bruijn" (fun () ->
    let t = Lam ("x", Lam ("y", App (Var "x", Var "y"))) in
    let rt = from_de_bruijn (to_de_bruijn t) in
    assert_true (alpha_equiv t rt) "roundtrip preserves alpha-equiv");

  Printf.printf "\n── Parsing ──\n";
  test "parse var" (fun () ->
    assert_alpha_eq (parse "x") (Var "x") "parse x");
  test "parse lambda" (fun () ->
    assert_alpha_eq (parse "\\x.x") (Lam ("x", Var "x")) "parse \\x.x");
  test "parse application" (fun () ->
    assert_alpha_eq (parse "f x") (App (Var "f", Var "x")) "parse f x");
  test "parse left-assoc app" (fun () ->
    assert_alpha_eq (parse "f x y")
      (App (App (Var "f", Var "x"), Var "y")) "parse f x y");
  test "parse parens" (fun () ->
    assert_alpha_eq (parse "f (x y)")
      (App (Var "f", App (Var "x", Var "y"))) "parse f (x y)");
  test "parse nested lambda" (fun () ->
    assert_alpha_eq (parse "\\x.\\y.x y")
      (Lam ("x", Lam ("y", App (Var "x", Var "y")))) "parse nested");

  Printf.printf "\n── Combinators ──\n";
  test "I x = x" (fun () ->
    assert_alpha_eq (unwrap_normal (eval_normal ~limit:10
      (App (comb_I, Var "x")))) (Var "x") "I");
  test "B f g x = f(g x)" (fun () ->
    let r = App (App (App (comb_B, Var "f"), Var "g"), Var "x") in
    let expected = App (Var "f", App (Var "g", Var "x")) in
    assert_alpha_eq (unwrap_normal (eval_normal ~limit:50 r)) expected "B");
  test "C f x y = f y x" (fun () ->
    let r = App (App (App (comb_C, Var "f"), Var "x"), Var "y") in
    let expected = App (App (Var "f", Var "y"), Var "x") in
    assert_alpha_eq (unwrap_normal (eval_normal ~limit:50 r)) expected "C");
  test "W f x = f x x" (fun () ->
    let r = App (App (comb_W, Var "f"), Var "x") in
    let expected = App (App (Var "f", Var "x"), Var "x") in
    assert_alpha_eq (unwrap_normal (eval_normal ~limit:50 r)) expected "W");
  test "Omega diverges" (fun () ->
    match eval_normal ~limit:50 comb_Omega with
    | Stuck _ -> ()
    | Normal t -> failwith (Printf.sprintf "Omega should diverge, got: %s" (to_string t)));

  Printf.printf "\n── Term Metrics ──\n";
  test "size of var" (fun () ->
    assert_eq (size (Var "x")) 1 "size(x)");
  test "size of id" (fun () ->
    assert_eq (size (Lam ("x", Var "x"))) 2 "size(λx.x)");
  test "depth of id" (fun () ->
    assert_eq (depth (Lam ("x", Var "x"))) 1 "depth(λx.x)");
  test "redex count" (fun () ->
    let t = App (Lam ("x", Var "x"), Var "y") in
    assert_eq (count_redexes t) 1 "1 redex");
  test "count_steps" (fun () ->
    let t = App (comb_I, Var "a") in
    assert_eq (count_steps step_normal t) (Some 1) "I a = 1 step");

  Printf.printf "\n── Trace ──\n";
  test "trace records steps" (fun () ->
    let t = App (comb_I, Var "z") in
    let tr = trace step_normal ~limit:10 t in
    assert_eq (List.length tr) 2 "trace length");

  Printf.printf "\n── Edge Cases ──\n";
  test "nested capture avoidance" (fun () ->
    (* (λy.λz.x)[x:=y z] should rename both y and z if needed *)
    let t = Lam ("y", Lam ("z", Var "x")) in
    let s = App (Var "y", Var "z") in
    let result = subst "x" s t in
    (* Result should have y and z free (from substitution) *)
    let fv = free_vars result in
    assert_true (StringSet.mem "y" fv) "y free in result";
    assert_true (StringSet.mem "z" fv) "z free in result");
  test "self-application reduction" (fun () ->
    let t = App (Lam ("x", App (Var "x", Var "x")), comb_I) in
    let result = unwrap_normal (eval_normal ~limit:100 t) in
    assert_alpha_eq result comb_I "(λx.x x) I → I");
  test "church_numeral 0 = λf.λx.x" (fun () ->
    let n0 = church_numeral 0 in
    let expected = Lam ("f", Lam ("x", Var "x")) in
    assert_true (alpha_equiv n0 expected) "0 = λf.λx.x");

  Printf.printf "\n════════════════════════\n";
  Printf.printf "Results: %d passed, %d failed\n\n" !pass !fail;
  if !fail > 0 then exit 1
