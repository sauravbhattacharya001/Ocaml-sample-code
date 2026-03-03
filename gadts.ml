(* gadts.ml - Generalized Algebraic Data Types (GADTs) in OCaml
 *
 * GADTs extend regular algebraic data types by allowing each constructor
 * to specify a different type for the overall type. This enables:
 * - Type-safe expression evaluators (no runtime type errors)
 * - Length-indexed vectors (statically checked bounds)
 * - Typed heterogeneous lists
 * - Type-level programming patterns
 *
 * GADTs are one of OCaml's most powerful advanced features, enabling
 * the type system to encode invariants that regular ADTs cannot express.
 *)

(* ============================================================
 * 1. TYPE-SAFE EXPRESSION EVALUATOR
 * ============================================================
 * The classic GADT example: an expression type where the type parameter
 * tracks the result type, making evaluation total (no runtime errors).
 *)

type _ expr =
  | Int : int -> int expr
  | Bool : bool -> bool expr
  | Float : float -> float expr
  | Add : int expr * int expr -> int expr
  | Mul : int expr * int expr -> int expr
  | FAdd : float expr * float expr -> float expr
  | Eq : 'a expr * 'a expr -> bool expr
  | If : bool expr * 'a expr * 'a expr -> 'a expr
  | Pair : 'a expr * 'b expr -> ('a * 'b) expr
  | Fst : ('a * 'b) expr -> 'a expr
  | Snd : ('a * 'b) expr -> 'b expr
  | Neg : int expr -> int expr
  | Not : bool expr -> bool expr
  | And : bool expr * bool expr -> bool expr
  | Or : bool expr * bool expr -> bool expr
  | Lt : int expr * int expr -> bool expr
  | IntToFloat : int expr -> float expr

(* Evaluate: note the return type is 'a, matching the phantom type.
 * The compiler KNOWS this is exhaustive and type-safe. *)
let rec eval : type a. a expr -> a = function
  | Int n -> n
  | Bool b -> b
  | Float f -> f
  | Add (a, b) -> eval a + eval b
  | Mul (a, b) -> eval a * eval b
  | FAdd (a, b) -> eval a +. eval b
  | Eq (a, b) -> eval a = eval b
  | If (c, t, e) -> if eval c then eval t else eval e
  | Pair (a, b) -> (eval a, eval b)
  | Fst p -> fst (eval p)
  | Snd p -> snd (eval p)
  | Neg a -> -(eval a)
  | Not a -> not (eval a)
  | And (a, b) -> eval a && eval b
  | Or (a, b) -> eval a || eval b
  | Lt (a, b) -> eval a < eval b
  | IntToFloat a -> Float.of_int (eval a)

(* Pretty-print expressions *)
let rec show : type a. a expr -> string = function
  | Int n -> string_of_int n
  | Bool b -> string_of_bool b
  | Float f -> string_of_float f
  | Add (a, b) -> "(" ^ show a ^ " + " ^ show b ^ ")"
  | Mul (a, b) -> "(" ^ show a ^ " * " ^ show b ^ ")"
  | FAdd (a, b) -> "(" ^ show a ^ " +. " ^ show b ^ ")"
  | Eq (a, b) -> "(" ^ show a ^ " = " ^ show b ^ ")"
  | If (c, t, e) -> "(if " ^ show c ^ " then " ^ show t ^ " else " ^ show e ^ ")"
  | Pair (a, b) -> "(" ^ show a ^ ", " ^ show b ^ ")"
  | Fst p -> "fst " ^ show p
  | Snd p -> "snd " ^ show p
  | Neg a -> "(-" ^ show a ^ ")"
  | Not a -> "(not " ^ show a ^ ")"
  | And (a, b) -> "(" ^ show a ^ " && " ^ show b ^ ")"
  | Or (a, b) -> "(" ^ show a ^ " || " ^ show b ^ ")"
  | Lt (a, b) -> "(" ^ show a ^ " < " ^ show b ^ ")"
  | IntToFloat a -> "float_of_int " ^ show a

(* Constant folding optimizer *)
let rec optimize : type a. a expr -> a expr = function
  | Add (Int 0, b) -> optimize b
  | Add (a, Int 0) -> optimize a
  | Mul (Int 0, _) -> Int 0
  | Mul (_, Int 0) -> Int 0
  | Mul (Int 1, b) -> optimize b
  | Mul (a, Int 1) -> optimize a
  | Add (Int a, Int b) -> Int (a + b)
  | Mul (Int a, Int b) -> Int (a * b)
  | And (Bool true, b) -> optimize b
  | And (Bool false, _) -> Bool false
  | Or (Bool true, _) -> Bool true
  | Or (Bool false, b) -> optimize b
  | Not (Bool b) -> Bool (not b)
  | Not (Not a) -> optimize a
  | Neg (Neg a) -> optimize a
  | Neg (Int n) -> Int (-n)
  | If (Bool true, t, _) -> optimize t
  | If (Bool false, _, e) -> optimize e
  | Add (a, b) -> Add (optimize a, optimize b)
  | Mul (a, b) -> Mul (optimize a, optimize b)
  | FAdd (a, b) -> FAdd (optimize a, optimize b)
  | If (c, t, e) -> If (optimize c, optimize t, optimize e)
  | e -> e

(* ============================================================
 * 2. PEANO NUMBERS AT THE TYPE LEVEL
 * ============================================================
 * Encode natural numbers as types for compile-time size tracking.
 *)

type zero = Zero
type 'n succ = Succ

(* Singleton witnesses for natural numbers *)
type _ nat =
  | Z : zero nat
  | S : 'n nat -> 'n succ nat

let rec nat_to_int : type n. n nat -> int = function
  | Z -> 0
  | S n -> 1 + nat_to_int n

(* ============================================================
 * 3. LENGTH-INDEXED VECTORS (SIZED LISTS)
 * ============================================================
 * Vectors whose length is tracked in the type, making head/tail
 * on empty vectors a compile-time error.
 *)

type (_, _) vec =
  | VNil : ('a, zero) vec
  | VCons : 'a * ('a, 'n) vec -> ('a, 'n succ) vec

(* Head and tail are TOTAL — VNil case is impossible *)
let vhead : type a n. (a, n succ) vec -> a = function
  | VCons (x, _) -> x

let vtail : type a n. (a, n succ) vec -> (a, n) vec = function
  | VCons (_, xs) -> xs

(* Map over a vector, preserving length *)
let rec vmap : type a b n. (a -> b) -> (a, n) vec -> (b, n) vec =
  fun f -> function
    | VNil -> VNil
    | VCons (x, xs) -> VCons (f x, vmap f xs)

(* Zip two same-length vectors *)
let rec vzip : type a b n. (a, n) vec -> (b, n) vec -> (a * b, n) vec =
  fun xs ys -> match xs, ys with
    | VNil, VNil -> VNil
    | VCons (x, xs'), VCons (y, ys') -> VCons ((x, y), vzip xs' ys')

(* Fold over a vector *)
let rec vfold : type a b n. (b -> a -> b) -> b -> (a, n) vec -> b =
  fun f acc -> function
    | VNil -> acc
    | VCons (x, xs) -> vfold f (f acc x) xs

(* Append two vectors — type tracks combined length *)
type (_, _, _) append =
  | AppZ : (zero, 'n, 'n) append
  | AppS : ('m, 'n, 'k) append -> ('m succ, 'n, 'k succ) append

let rec vappend : type a m n k.
  (m, n, k) append -> (a, m) vec -> (a, n) vec -> (a, k) vec =
  fun prf xs ys -> match prf, xs with
    | AppZ, VNil -> ys
    | AppS prf', VCons (x, xs') -> VCons (x, vappend prf' xs' ys)

(* Reverse a vector *)
let vec_to_list : type a n. (a, n) vec -> a list =
  fun v -> vfold (fun acc x -> x :: acc) [] v |> List.rev

let vec_length : type a n. (a, n) vec -> int =
  fun v -> vfold (fun acc _ -> acc + 1) 0 v

(* ============================================================
 * 4. TYPED HETEROGENEOUS LISTS
 * ============================================================
 * Lists that hold values of different types, with the type list
 * tracked at the type level.
 *)

type _ hlist =
  | HNil : unit hlist
  | HCons : 'a * 'b hlist -> ('a * 'b) hlist

let hhead : type a b. (a * b) hlist -> a = function
  | HCons (x, _) -> x

let htail : type a b. (a * b) hlist -> b hlist = function
  | HCons (_, xs) -> xs

(* ============================================================
 * 5. TYPE EQUALITY WITNESSES
 * ============================================================
 * Prove at runtime that two types are equal, then use the proof.
 *)

type (_, _) eq = Refl : ('a, 'a) eq

let cast : type a b. (a, b) eq -> a -> b = fun Refl x -> x

(* Symmetry and transitivity of type equality *)
let sym : type a b. (a, b) eq -> (b, a) eq = fun Refl -> Refl

let trans : type a b c. (a, b) eq -> (b, c) eq -> (a, c) eq =
  fun Refl Refl -> Refl

(* ============================================================
 * 6. TYPED FORMAT STRINGS (SIMPLIFIED PRINTF)
 * ============================================================
 * A mini type-safe printf using GADTs.
 *)

type (_, _) fmt =
  | Lit : string -> ('a, 'a) fmt
  | Str : ('a, 'b) fmt -> (string -> 'a, 'b) fmt
  | Int_f : ('a, 'b) fmt -> (int -> 'a, 'b) fmt
  | Float_f : ('a, 'b) fmt -> (float -> 'a, 'b) fmt
  | Bool_f : ('a, 'b) fmt -> (bool -> 'a, 'b) fmt
  | Cat : ('a, 'b) fmt * ('b, 'c) fmt -> ('a, 'c) fmt

(* Interpret a format into a continuation-based function *)
let rec sprintf_k : type a b. (a, b) fmt -> (string -> b) -> a =
  fun fmt k -> match fmt with
    | Lit s -> k s
    | Str rest -> fun s -> sprintf_k rest (fun r -> k (s ^ r))
    | Int_f rest -> fun n -> sprintf_k rest (fun r -> k (string_of_int n ^ r))
    | Float_f rest -> fun f -> sprintf_k rest (fun r -> k (string_of_float f ^ r))
    | Bool_f rest -> fun b -> sprintf_k rest (fun r -> k (string_of_bool b ^ r))
    | Cat (f1, f2) -> sprintf_k f1 (fun s1 -> sprintf_k f2 (fun s2 -> k (s1 ^ s2)))

let sprintf : type a. (a, string) fmt -> a =
  fun fmt -> sprintf_k fmt (fun s -> s)

(* ============================================================
 * 7. EXISTENTIAL TYPES WITH GADTS
 * ============================================================
 * Pack a value with its operations, hiding the concrete type.
 *)

type showable = Show : 'a * ('a -> string) -> showable

let show_val (Show (v, f)) = f v

let show_list (items : showable list) : string list =
  List.map show_val items

(* A typed key-value store using existentials *)
type 'a key = {
  key_name : string;
  key_id : int;
}

type binding = Bind : 'a key * 'a -> binding

let next_id = ref 0
let new_key name =
  let id = !next_id in
  incr next_id;
  { key_name = name; key_id = id }

let store_find : type a. a key -> binding list -> a option =
  fun k bindings ->
    let rec go = function
      | [] -> None
      | Bind (k', v) :: rest ->
        if k.key_id = k'.key_id then
          (* We know the types match because IDs are unique *)
          Some (Obj.magic v : a)
        else go rest
    in
    go bindings

(* ============================================================
 * 8. WELL-TYPED STACK MACHINE
 * ============================================================
 * A stack machine where the type system ensures stack safety.
 *)

type (_, _) stack_op =
  | Push : 'a -> ('s, 'a * 's) stack_op
  | Pop : ('a * 's, 's) stack_op
  | Dup : ('a * 's, 'a * ('a * 's)) stack_op
  | Swap : ('a * ('b * 's), 'b * ('a * 's)) stack_op
  | IAdd : (int * (int * 's), int * 's) stack_op
  | IMul : (int * (int * 's), int * 's) stack_op

type (_, _) program =
  | Halt : ('s, 's) program
  | Seq : ('s1, 's2) stack_op * ('s2, 's3) program -> ('s1, 's3) program

let exec_op : type s1 s2. (s1, s2) stack_op -> s1 -> s2 =
  fun op stack -> match op with
    | Push v -> (v, stack)
    | Pop -> snd stack
    | Dup -> let (x, _) as s = stack in (x, s)
    | Swap -> let (a, (b, s)) = stack in (b, (a, s))
    | IAdd -> let (a, (b, s)) = stack in (a + b, s)
    | IMul -> let (a, (b, s)) = stack in (a * b, s)

let rec exec_program : type s1 s2. (s1, s2) program -> s1 -> s2 =
  fun prog stack -> match prog with
    | Halt -> stack
    | Seq (op, rest) -> exec_program rest (exec_op op stack)

(* Helper to build programs *)
let ( >> ) op prog = Seq (op, prog)

(* ============================================================
 * TESTS
 * ============================================================ *)

let run_tests () =
  let passed = ref 0 in
  let failed = ref 0 in
  let test name f =
    try
      f ();
      incr passed;
      Printf.printf "  ✓ %s\n" name
    with e ->
      incr failed;
      Printf.printf "  ✗ %s: %s\n" name (Printexc.to_string e)
  in

  Printf.printf "\n=== GADT Tests ===\n\n";

  (* Expression evaluator tests *)
  Printf.printf "Expression Evaluator:\n";

  test "integer literal" (fun () ->
    assert (eval (Int 42) = 42));

  test "boolean literal" (fun () ->
    assert (eval (Bool true) = true));

  test "addition" (fun () ->
    assert (eval (Add (Int 3, Int 4)) = 7));

  test "multiplication" (fun () ->
    assert (eval (Mul (Int 5, Int 6)) = 30));

  test "nested arithmetic" (fun () ->
    assert (eval (Add (Mul (Int 2, Int 3), Int 4)) = 10));

  test "float addition" (fun () ->
    assert (eval (FAdd (Float 1.5, Float 2.5)) = 4.0));

  test "equality" (fun () ->
    assert (eval (Eq (Int 5, Int 5)) = true);
    assert (eval (Eq (Int 5, Int 3)) = false));

  test "if-then-else" (fun () ->
    assert (eval (If (Bool true, Int 1, Int 2)) = 1);
    assert (eval (If (Bool false, Int 1, Int 2)) = 2));

  test "pairs" (fun () ->
    assert (eval (Pair (Int 1, Bool true)) = (1, true));
    assert (eval (Fst (Pair (Int 1, Int 2))) = 1);
    assert (eval (Snd (Pair (Int 1, Int 2))) = 2));

  test "negation" (fun () ->
    assert (eval (Neg (Int 5)) = -5));

  test "boolean ops" (fun () ->
    assert (eval (And (Bool true, Bool false)) = false);
    assert (eval (Or (Bool false, Bool true)) = true);
    assert (eval (Not (Bool true)) = false));

  test "less than" (fun () ->
    assert (eval (Lt (Int 3, Int 5)) = true);
    assert (eval (Lt (Int 5, Int 3)) = false));

  test "int to float" (fun () ->
    assert (eval (IntToFloat (Int 42)) = 42.0));

  test "show expression" (fun () ->
    let s = show (Add (Int 3, Mul (Int 4, Int 5))) in
    assert (String.length s > 0));

  (* Optimizer tests *)
  Printf.printf "\nExpression Optimizer:\n";

  test "fold constants" (fun () ->
    assert (eval (optimize (Add (Int 3, Int 4))) = 7));

  test "eliminate add 0" (fun () ->
    match optimize (Add (Int 0, Int 5)) with
    | Int 5 -> ()
    | _ -> assert false);

  test "eliminate mul 0" (fun () ->
    match optimize (Mul (Int 0, Int 999)) with
    | Int 0 -> ()
    | _ -> assert false);

  test "eliminate mul 1" (fun () ->
    match optimize (Mul (Int 1, Int 7)) with
    | Int 7 -> ()
    | _ -> assert false);

  test "double negation" (fun () ->
    match optimize (Neg (Neg (Int 5))) with
    | Int 5 -> ()
    | _ -> assert false);

  test "double not" (fun () ->
    match optimize (Not (Not (Bool true))) with
    | Bool true -> ()
    | _ -> assert false);

  test "dead branch elimination" (fun () ->
    assert (eval (optimize (If (Bool true, Int 42, Int 0))) = 42));

  (* Peano / Vector tests *)
  Printf.printf "\nLength-Indexed Vectors:\n";

  test "nat to int" (fun () ->
    assert (nat_to_int Z = 0);
    assert (nat_to_int (S (S (S Z))) = 3));

  test "vhead" (fun () ->
    assert (vhead (VCons (1, VNil)) = 1);
    assert (vhead (VCons (10, VCons (20, VNil))) = 10));

  test "vtail" (fun () ->
    assert (vhead (vtail (VCons (1, VCons (2, VNil)))) = 2));

  test "vmap" (fun () ->
    let v = VCons (1, VCons (2, VCons (3, VNil))) in
    let v' = vmap (fun x -> x * 2) v in
    assert (vhead v' = 2);
    assert (vhead (vtail v') = 4));

  test "vzip" (fun () ->
    let a = VCons (1, VCons (2, VNil)) in
    let b = VCons ("a", VCons ("b", VNil)) in
    let z = vzip a b in
    assert (vhead z = (1, "a")));

  test "vfold" (fun () ->
    let v = VCons (1, VCons (2, VCons (3, VNil))) in
    assert (vfold ( + ) 0 v = 6));

  test "vec_to_list" (fun () ->
    let v = VCons (1, VCons (2, VCons (3, VNil))) in
    assert (vec_to_list v = [1; 2; 3]));

  test "vec_length" (fun () ->
    assert (vec_length VNil = 0);
    assert (vec_length (VCons (1, VCons (2, VNil))) = 2));

  test "vappend" (fun () ->
    let a = VCons (1, VCons (2, VNil)) in
    let b = VCons (3, VNil) in
    let prf = AppS (AppS AppZ) in
    let c = vappend prf a b in
    assert (vec_to_list c = [1; 2; 3]));

  (* Heterogeneous list tests *)
  Printf.printf "\nHeterogeneous Lists:\n";

  test "hlist basics" (fun () ->
    let h = HCons (42, HCons ("hello", HCons (true, HNil))) in
    assert (hhead h = 42);
    assert (hhead (htail h) = "hello");
    assert (hhead (htail (htail h)) = true));

  (* Type equality tests *)
  Printf.printf "\nType Equality:\n";

  test "cast with Refl" (fun () ->
    let eq : (int, int) eq = Refl in
    assert (cast eq 42 = 42));

  test "symmetry" (fun () ->
    let eq : (int, int) eq = Refl in
    let _ : (int, int) eq = sym eq in
    ());

  test "transitivity" (fun () ->
    let ab : (int, int) eq = Refl in
    let bc : (int, int) eq = Refl in
    let _ : (int, int) eq = trans ab bc in
    ());

  (* Format string tests *)
  Printf.printf "\nTyped Printf:\n";

  test "literal format" (fun () ->
    assert (sprintf (Lit "hello") = "hello"));

  test "string interpolation" (fun () ->
    assert (sprintf (Cat (Lit "Hello, ", Str (Lit "!"))) "world" = "Hello, world!"));

  test "int interpolation" (fun () ->
    assert (sprintf (Cat (Lit "x=", Int_f (Lit ""))) 42 = "x=42"));

  test "multiple args" (fun () ->
    let fmt = Cat (Str (Lit " is "), Int_f (Lit " years old")) in
    assert (sprintf fmt "Alice" 30 = "Alice is 30 years old"));

  test "bool format" (fun () ->
    assert (sprintf (Bool_f (Lit "")) true = "true"));

  test "float format" (fun () ->
    let s = sprintf (Float_f (Lit "")) 3.14 in
    assert (String.length s > 0));

  (* Existential type tests *)
  Printf.printf "\nExistentials:\n";

  test "showable values" (fun () ->
    let items = [
      Show (42, string_of_int);
      Show ("hello", fun s -> "\"" ^ s ^ "\"");
      Show (3.14, string_of_float);
    ] in
    let strs = show_list items in
    assert (List.nth strs 0 = "42");
    assert (List.nth strs 1 = "\"hello\""));

  (* Stack machine tests *)
  Printf.printf "\nStack Machine:\n";

  test "push and halt" (fun () ->
    let prog = Push 42 >> Halt in
    let (result, ()) = exec_program prog () in
    assert (result = 42));

  test "addition" (fun () ->
    let prog = Push 3 >> Push 4 >> IAdd >> Halt in
    let (result, ()) = exec_program prog () in
    assert (result = 7));

  test "multiplication" (fun () ->
    let prog = Push 5 >> Push 6 >> IMul >> Halt in
    let (result, ()) = exec_program prog () in
    assert (result = 30));

  test "dup" (fun () ->
    let prog = Push 5 >> Dup >> IAdd >> Halt in
    let (result, ()) = exec_program prog () in
    assert (result = 10));

  test "swap" (fun () ->
    let prog = Push 1 >> Push 2 >> Swap >> Halt in
    let (a, (b, ())) = exec_program prog () in
    assert (a = 1 && b = 2));

  test "complex program: (3+4)*5" (fun () ->
    let prog = Push 3 >> Push 4 >> IAdd >> Push 5 >> IMul >> Halt in
    let (result, ()) = exec_program prog () in
    assert (result = 35));

  test "pop" (fun () ->
    let prog = Push 1 >> Push 2 >> Pop >> Halt in
    let (result, ()) = exec_program prog () in
    assert (result = 1));

  Printf.printf "\n=== Results: %d passed, %d failed ===\n" !passed !failed;
  if !failed > 0 then exit 1

let () = run_tests ()
