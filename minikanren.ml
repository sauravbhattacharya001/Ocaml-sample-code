(* minikanren.ml — A miniKanren-style logic programming engine in OCaml *)
(* Implements: unification, substitution, logic variables, conjunction,  *)
(* disjunction, fresh variables, reification, and relational programs.   *)
(* Applications: type inference, puzzle solving, relational arithmetic.  *)

(* ── Term representation ─────────────────────────────────────────────── *)

type term =
  | Var of int                  (* logic variable *)
  | Atom of string              (* atomic symbol *)
  | Pair of term * term         (* cons pair / tuple *)
  | Nil                         (* empty list *)

let var_counter = ref 0

let fresh_var () =
  let v = !var_counter in
  incr var_counter;
  Var v

let reset_vars () = var_counter := 0

(* ── Substitution (association list) ──────────────────────────────────── *)

type subst = (int * term) list

let empty_subst : subst = []

let rec walk (s : subst) (t : term) : term =
  match t with
  | Var v ->
    (match List.assoc_opt v s with
     | Some t' -> walk s t'
     | None -> t)
  | _ -> t

let rec walk_deep (s : subst) (t : term) : term =
  let t = walk s t in
  match t with
  | Pair (a, b) -> Pair (walk_deep s a, walk_deep s b)
  | _ -> t

let extend (s : subst) (v : int) (t : term) : subst = (v, t) :: s

(* ── Occurs check ────────────────────────────────────────────────────── *)

let rec occurs (s : subst) (v : int) (t : term) : bool =
  let t = walk s t in
  match t with
  | Var v' -> v = v'
  | Pair (a, b) -> occurs s v a || occurs s v b
  | _ -> false

(* ── Unification ─────────────────────────────────────────────────────── *)

let rec unify (s : subst) (u : term) (v : term) : subst option =
  let u = walk s u in
  let v = walk s v in
  match u, v with
  | u, v when u = v -> Some s
  | Var u_id, _ ->
    if occurs s u_id v then None
    else Some (extend s u_id v)
  | _, Var v_id ->
    if occurs s v_id u then None
    else Some (extend s v_id u)
  | Pair (ua, ud), Pair (va, vd) ->
    (match unify s ua va with
     | Some s' -> unify s' ud vd
     | None -> None)
  | _ -> None

(* ── Streams (lazy list of substitutions) ─────────────────────────────── *)

type stream =
  | Empty
  | Mature of subst * stream
  | Immature of (unit -> stream)

let rec mplus (s1 : stream) (s2 : stream) : stream =
  match s1 with
  | Empty -> s2
  | Mature (a, rest) -> Mature (a, mplus s2 rest)  (* interleave *)
  | Immature f -> Immature (fun () -> mplus s2 (f ()))

let rec bind (s : stream) (g : subst -> stream) : stream =
  match s with
  | Empty -> Empty
  | Mature (a, rest) -> mplus (g a) (bind rest g)
  | Immature f -> Immature (fun () -> bind (f ()) g)

(* ── Goals ───────────────────────────────────────────────────────────── *)

type goal = subst -> stream

let succeed : goal = fun s -> Mature (s, Empty)
let fail : goal = fun _ -> Empty

let ( === ) (u : term) (v : term) : goal = fun s ->
  match unify s u v with
  | Some s' -> Mature (s', Empty)
  | None -> Empty

let disj (g1 : goal) (g2 : goal) : goal = fun s ->
  mplus (g1 s) (g2 s)

let conj (g1 : goal) (g2 : goal) : goal = fun s ->
  bind (g1 s) g2

let ( ||| ) = disj
let ( &&& ) = conj

let fresh (f : term -> goal) : goal = fun s ->
  let v = fresh_var () in
  f v s

let fresh2 (f : term -> term -> goal) : goal = fun s ->
  let v1 = fresh_var () in
  let v2 = fresh_var () in
  f v1 v2 s

let fresh3 (f : term -> term -> term -> goal) : goal = fun s ->
  let v1 = fresh_var () in
  let v2 = fresh_var () in
  let v3 = fresh_var () in
  f v1 v2 v3 s

(* conde = disjunction of conjunctions *)
let conde (clauses : goal list list) : goal =
  List.fold_left (fun acc clause ->
    let conj_goal = List.fold_left conj succeed clause in
    disj acc conj_goal
  ) fail clauses

(* ── Stream operations ───────────────────────────────────────────────── *)

let rec take (n : int) (s : stream) : subst list =
  if n = 0 then []
  else match s with
    | Empty -> []
    | Mature (a, rest) -> a :: take (n - 1) rest
    | Immature f -> take n (f ())

let rec take_all (s : stream) : subst list =
  match s with
  | Empty -> []
  | Mature (a, rest) -> a :: take_all rest
  | Immature f -> take_all (f ())

(* Bounded take_all to prevent infinite loops *)
let take_all_bounded ?(limit=1000) (s : stream) : subst list =
  take limit s

(* ── Reification ─────────────────────────────────────────────────────── *)

let reify_name (n : int) : string =
  if n < 26 then Printf.sprintf "_.%c" (Char.chr (n + Char.code 'a'))
  else Printf.sprintf "_.%d" n

let rec reify_term (t : term) : string =
  match t with
  | Var v -> reify_name v
  | Atom s -> s
  | Nil -> "()"
  | Pair (a, b) ->
    let rec collect acc = function
      | Nil -> List.rev acc, None
      | Pair (x, rest) -> collect (x :: acc) rest
      | other -> List.rev acc, Some other
    in
    let elems, tail = collect [a] b in
    let elem_strs = List.map reify_term elems in
    match tail with
    | None -> "(" ^ String.concat " " elem_strs ^ ")"
    | Some t -> "(" ^ String.concat " " elem_strs ^ " . " ^ reify_term t ^ ")"

let reify (s : subst) (v : term) : string =
  reify_term (walk_deep s v)

(* ── Run interface ───────────────────────────────────────────────────── *)

let run (n : int) (f : term -> goal) : string list =
  reset_vars ();
  let q = fresh_var () in
  let results = take n (f q empty_subst) in
  List.map (fun s -> reify s q) results

let run_all (f : term -> goal) : string list =
  reset_vars ();
  let q = fresh_var () in
  let results = take_all_bounded ~limit:100 (f q empty_subst) in
  List.map (fun s -> reify s q) results

(* ── List operations (relational) ────────────────────────────────────── *)

let rec list_of_terms (ts : term list) : term =
  match ts with
  | [] -> Nil
  | t :: rest -> Pair (t, list_of_terms rest)

let rec appendo (l : term) (r : term) (out : term) : goal =
  (l === Nil &&& (r === out))
  ||| fresh2 (fun h t ->
    fresh (fun res ->
      l === Pair (h, t) &&&
      out === Pair (h, res) &&&
      (fun s -> Immature (fun () -> appendo t r res s))
    ))

let rec membero (x : term) (l : term) : goal =
  fresh2 (fun h t ->
    l === Pair (h, t) &&&
    ((x === h) ||| (fun s -> Immature (fun () -> membero x t s)))
  )

let rec reverseo (l : term) (out : term) : goal =
  let rec rev_acc (l : term) (acc : term) (out : term) : goal =
    (l === Nil &&& (acc === out))
    ||| fresh2 (fun h t ->
      l === Pair (h, t) &&&
      (fun s -> Immature (fun () -> rev_acc t (Pair (h, acc)) out s))
    )
  in
  rev_acc l Nil out

let rec lengtho (l : term) (n : int) : goal =
  if n = 0 then l === Nil
  else if n < 0 then fail
  else fresh2 (fun _h t ->
    l === Pair (_h, t) &&&
    lengtho t (n - 1)
  )

(* ── Relational arithmetic (Peano numbers) ───────────────────────────── *)

let zero = Atom "z"
let succ n = Pair (Atom "s", n)

let rec pluso (a : term) (b : term) (c : term) : goal =
  (a === zero &&& (b === c))
  ||| fresh2 (fun a' c' ->
    a === succ a' &&&
    c === succ c' &&&
    (fun s -> Immature (fun () -> pluso a' b c' s))
  )

let rec multo (a : term) (b : term) (c : term) : goal =
  (a === zero &&& (c === zero))
  ||| fresh2 (fun a' partial ->
    a === succ a' &&&
    pluso b partial c &&&
    (fun s -> Immature (fun () -> multo a' b partial s))
  )

let rec leo (a : term) (b : term) : goal =
  (a === zero)
  ||| fresh2 (fun a' b' ->
    a === succ a' &&&
    b === succ b' &&&
    (fun s -> Immature (fun () -> leo a' b' s))
  )

let int_to_peano (n : int) : term =
  let rec go n = if n = 0 then zero else succ (go (n - 1)) in
  go n

let rec peano_to_int (s : subst) (t : term) : int option =
  let t = walk_deep s t in
  match t with
  | Atom "z" -> Some 0
  | Pair (Atom "s", rest) ->
    (match peano_to_int s rest with
     | Some n -> Some (n + 1)
     | None -> None)
  | _ -> None

(* ── Puzzle: map coloring ────────────────────────────────────────────── *)

let coloro (x : term) : goal =
  x === Atom "red" ||| x === Atom "green" ||| x === Atom "blue"

let neq_color (x : term) (y : term) : goal = fun s ->
  let x' = walk s x in
  let y' = walk s y in
  if x' = y' then Empty
  else Mature (s, Empty)

(* Color a simple graph: nodes with adjacency constraints *)
let map_color_triangle () : string list =
  reset_vars ();
  let a = fresh_var () in
  let b = fresh_var () in
  let c = fresh_var () in
  let q = fresh_var () in
  let goal =
    coloro a &&& coloro b &&& coloro c &&&
    neq_color a b &&& neq_color b c &&& neq_color a c &&&
    (q === list_of_terms [a; b; c])
  in
  let results = take 10 (goal empty_subst) in
  List.map (fun s -> reify s q) results

(* ── Puzzle: permutations ────────────────────────────────────────────── *)

let rec permuto (l : term) (p : term) : goal =
  (l === Nil &&& (p === Nil))
  ||| fresh3 (fun h t rest ->
    l === Pair (h, t) &&&
    permuto t rest &&&
    (fun s -> Immature (fun () -> appendo (Pair (h, Nil)) rest p s))
    ||| fresh3 (fun h2 t2 rest2 ->
      l === Pair (h2, t2) &&&
      fresh (fun perm_t ->
        permuto t2 perm_t &&&
        (fun s -> Immature (fun () ->
          let q = fresh_var () in
          (appendo q (Pair (h2, Nil)) rest2 &&&
           appendo rest2 (Pair (h2, Nil)) p) s
        ))
      )
    )
  )

(* simpler: insertions-based permutation *)
let rec inserto (x : term) (l : term) (out : term) : goal =
  (out === Pair (x, l))
  ||| fresh3 (fun h t res ->
    l === Pair (h, t) &&&
    out === Pair (h, res) &&&
    (fun s -> Immature (fun () -> inserto x t res s))
  )

let rec perm (l : term) (out : term) : goal =
  (l === Nil &&& (out === Nil))
  ||| fresh3 (fun h t perm_t ->
    l === Pair (h, t) &&&
    perm t perm_t &&&
    (fun s -> Immature (fun () -> inserto h perm_t out s))
  )

(* ── Type inference (relational) ─────────────────────────────────────── *)

(* Simple typed lambda calculus types as terms *)
let t_int = Atom "int"
let t_bool = Atom "bool"
let t_arrow a b = list_of_terms [Atom "->"; a; b]

(* Expressions as terms *)
let e_var name = list_of_terms [Atom "var"; Atom name]
let e_lam name body = list_of_terms [Atom "lam"; Atom name; body]
let e_app f x = list_of_terms [Atom "app"; f; x]
let e_lit_int = Atom "lit-int"
let e_lit_bool = Atom "lit-bool"

(* Environment lookup *)
let rec lookupo (env : term) (name : term) (ty : term) : goal =
  fresh3 (fun h_name h_ty rest ->
    env === Pair (Pair (h_name, h_ty), rest) &&&
    ((h_name === name &&& (h_ty === ty))
     ||| (fun s ->
       let n = walk s h_name in
       let nm = walk s name in
       if n = nm then Empty
       else Immature (fun () -> lookupo rest name ty s)
     ))
  )

(* Type inference relation: typeo env expr type *)
let rec typeo (env : term) (expr : term) (ty : term) : goal =
  (* int literal *)
  (expr === e_lit_int &&& (ty === t_int))
  (* bool literal *)
  ||| (expr === e_lit_bool &&& (ty === t_bool))
  (* variable *)
  ||| fresh (fun name ->
    expr === list_of_terms [Atom "var"; name] &&&
    lookupo env name ty
  )
  (* lambda *)
  ||| fresh3 (fun name body arg_ty ->
    fresh (fun ret_ty ->
      expr === list_of_terms [Atom "lam"; name; body] &&&
      ty === t_arrow arg_ty ret_ty &&&
      (fun s -> Immature (fun () ->
        typeo (Pair (Pair (name, arg_ty), env)) body ret_ty s
      ))
    )
  )
  (* application *)
  ||| fresh3 (fun f x arg_ty ->
    expr === list_of_terms [Atom "app"; f; x] &&&
    (fun s -> Immature (fun () ->
      fresh (fun _dummy ->
        typeo env f (t_arrow arg_ty ty) &&&
        typeo env x arg_ty
      ) s
    ))
  )

(* ── Demo / main ─────────────────────────────────────────────────────── *)

let () =
  Printf.printf "=== miniKanren Logic Programming Engine ===\n\n";

  (* Basic unification *)
  Printf.printf "--- Unification ---\n";
  reset_vars ();
  let x = fresh_var () in
  (match unify empty_subst x (Atom "hello") with
   | Some s -> Printf.printf "unify(X, hello) => X = %s\n" (reify s x)
   | None -> Printf.printf "unify failed\n");

  let y = fresh_var () in
  (match unify empty_subst (Pair (x, y)) (Pair (Atom "a", Atom "b")) with
   | Some s ->
     Printf.printf "unify((X, Y), (a, b)) => X=%s, Y=%s\n"
       (reify s x) (reify s y)
   | None -> Printf.printf "unify failed\n");

  (* Run queries *)
  Printf.printf "\n--- Logic queries ---\n";
  let results = run 5 (fun q -> q === Atom "hello") in
  Printf.printf "run 5 (q == hello): %s\n"
    (String.concat ", " results);

  let results = run 5 (fun q ->
    q === Atom "a" ||| q === Atom "b" ||| q === Atom "c"
  ) in
  Printf.printf "run 5 (q == a | b | c): %s\n"
    (String.concat ", " results);

  (* Appendo *)
  Printf.printf "\n--- appendo ---\n";
  let results = run 5 (fun q ->
    appendo (list_of_terms [Atom "1"; Atom "2"])
            (list_of_terms [Atom "3"; Atom "4"]) q
  ) in
  Printf.printf "append [1,2] [3,4]: %s\n"
    (String.concat ", " results);

  (* Reverse appendo: find what to append *)
  let results = run 3 (fun q ->
    appendo q (list_of_terms [Atom "3"]) (list_of_terms [Atom "1"; Atom "2"; Atom "3"])
  ) in
  Printf.printf "append ? [3] = [1,2,3]: %s\n"
    (String.concat ", " results);

  (* membero *)
  Printf.printf "\n--- membero ---\n";
  let results = run 5 (fun q ->
    membero q (list_of_terms [Atom "a"; Atom "b"; Atom "c"])
  ) in
  Printf.printf "member ? [a,b,c]: %s\n"
    (String.concat ", " results);

  (* Peano arithmetic *)
  Printf.printf "\n--- Relational arithmetic ---\n";
  let results = run 1 (fun q ->
    pluso (int_to_peano 2) (int_to_peano 3) q
  ) in
  Printf.printf "2 + 3 = %s\n" (String.concat ", " results);

  (* Reverse: what + 2 = 5? *)
  let results = run 1 (fun q ->
    pluso q (int_to_peano 2) (int_to_peano 5)
  ) in
  Printf.printf "? + 2 = 5: %s\n" (String.concat ", " results);

  (* Multiplication *)
  let results = run 1 (fun q ->
    multo (int_to_peano 3) (int_to_peano 2) q
  ) in
  Printf.printf "3 * 2 = %s\n" (String.concat ", " results);

  (* Map coloring *)
  Printf.printf "\n--- Map coloring (triangle) ---\n";
  let colorings = map_color_triangle () in
  Printf.printf "Found %d valid 3-colorings of K3\n" (List.length colorings);
  List.iteri (fun i c -> Printf.printf "  %d: %s\n" (i + 1) c)
    (if List.length colorings > 6 then
       List.filteri (fun i _ -> i < 6) colorings
     else colorings);

  (* Permutations *)
  Printf.printf "\n--- Permutations ---\n";
  let results = run 10 (fun q ->
    perm (list_of_terms [Atom "a"; Atom "b"; Atom "c"]) q
  ) in
  Printf.printf "perm [a,b,c]: %d results\n" (List.length results);
  List.iter (fun r -> Printf.printf "  %s\n" r) results;

  Printf.printf "\nDone.\n"
