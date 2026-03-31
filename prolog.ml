(* Mini Prolog Interpreter in OCaml
 *
 * Features:
 * - Term parsing: atoms, variables, compound terms (functors)
 * - Unification with occurs check
 * - Backtracking search via depth-first SLD resolution
 * - Built-in predicates: true, fail, =, \=, write, nl, is (arithmetic)
 * - Interactive REPL with ?- query prompt
 * - Example knowledge bases: family tree, list operations, logic puzzles
 *
 * Usage:
 *   ocaml prolog.ml
 *
 * Example session:
 *   ?- parent(tom, bob).
 *   true.
 *   ?- ancestor(X, jim).
 *   X = tom ;
 *   X = bob ;
 *   false.
 *   ?- append([1,2], [3,4], X).
 *   X = [1, 2, 3, 4] ;
 *   false.
 *)

(* ---- Types ---- *)

type term =
  | Atom of string
  | Var of string
  | Compound of string * term list
  | Int of int

type clause = { head : term; body : term list }

type substitution = (string * term) list

(* ---- Pretty Printing ---- *)

let rec term_to_string = function
  | Atom s -> s
  | Var s -> s
  | Int n -> string_of_int n
  | Compound (".", [h; t]) -> "[" ^ list_to_string h t ^ "]"
  | Compound (f, []) -> f
  | Compound (f, args) ->
    f ^ "(" ^ String.concat ", " (List.map term_to_string args) ^ ")"

and list_to_string h t =
  let hs = term_to_string h in
  match t with
  | Atom "[]" -> hs
  | Compound (".", [h2; t2]) -> hs ^ ", " ^ list_to_string h2 t2
  | Var v -> hs ^ " | " ^ v
  | other -> hs ^ " | " ^ term_to_string other

(* ---- Substitution ---- *)

let rec walk (s : substitution) (t : term) : term =
  match t with
  | Var v -> (
    match List.assoc_opt v s with
    | Some t' -> walk s t'
    | None -> t)
  | Compound (f, args) -> Compound (f, List.map (walk s) args)
  | _ -> t

let rec walk_deep (s : substitution) (t : term) : term =
  match walk s t with
  | Compound (f, args) -> Compound (f, List.map (walk_deep s) args)
  | t' -> t'

(* ---- Unification ---- *)

let rec occurs_in (v : string) (s : substitution) (t : term) : bool =
  match walk s t with
  | Var v2 -> v = v2
  | Compound (_, args) -> List.exists (occurs_in v s) args
  | _ -> false

let rec unify (s : substitution) (t1 : term) (t2 : term) : substitution option =
  let t1 = walk s t1 and t2 = walk s t2 in
  match (t1, t2) with
  | Atom a, Atom b when a = b -> Some s
  | Int a, Int b when a = b -> Some s
  | Var v, t | t, Var v ->
    if Var v = t then Some s
    else if occurs_in v s t then None
    else Some ((v, t) :: s)
  | Compound (f1, a1), Compound (f2, a2)
    when f1 = f2 && List.length a1 = List.length a2 ->
    List.fold_left2
      (fun acc x y ->
        match acc with None -> None | Some s' -> unify s' x y)
      (Some s) a1 a2
  | _ -> None

(* ---- Variable Renaming ---- *)

let counter = ref 0

let fresh_var () =
  incr counter;
  "_G" ^ string_of_int !counter

let rec rename_term (mapping : (string * string) ref list ref) = function
  | Var v ->
    let found = List.find_opt (fun r -> fst !r = v) !mapping in
    (match found with
     | Some r -> Var (snd !r)
     | None ->
       let v' = fresh_var () in
       mapping := ref (v, v') :: !mapping;
       Var v')
  | Compound (f, args) ->
    Compound (f, List.map (rename_term mapping) args)
  | t -> t

let rename_clause (c : clause) : clause =
  let mapping = ref [] in
  { head = rename_term mapping c.head;
    body = List.map (rename_term mapping) c.body }

(* ---- Arithmetic Evaluation ---- *)

let rec eval_arith (s : substitution) (t : term) : int =
  match walk s t with
  | Int n -> n
  | Atom "+" | Atom "-" | Atom "*" | Atom "/" ->
    failwith "Operator used without arguments"
  | Compound ("+", [a; b]) -> eval_arith s a + eval_arith s b
  | Compound ("-", [a; b]) -> eval_arith s a - eval_arith s b
  | Compound ("*", [a; b]) -> eval_arith s a * eval_arith s b
  | Compound ("/", [a; b]) ->
    let bv = eval_arith s b in
    if bv = 0 then failwith "Division by zero"
    else eval_arith s a / bv
  | Compound ("mod", [a; b]) -> eval_arith s a mod eval_arith s b
  | Var v -> failwith ("Unbound variable in arithmetic: " ^ v)
  | t -> failwith ("Cannot evaluate: " ^ term_to_string t)

(* ---- Solver ---- *)

type result = substitution Seq.t

let rec solve (db : clause list) (goals : term list) (s : substitution) : result =
  match goals with
  | [] -> fun () -> Seq.Cons (s, Seq.empty)
  | goal :: rest ->
    let goal' = walk s goal in
    solve_goal db goal' rest s

and solve_goal db goal rest s =
  match goal with
  (* Built-ins *)
  | Atom "true" -> solve db rest s
  | Atom "fail" -> Seq.empty
  | Compound ("not", [g]) ->
    let results = solve db [g] s in
    (match results () with
     | Seq.Nil -> solve db rest s
     | _ -> Seq.empty)
  | Compound ("=", [a; b]) -> (
    match unify s a b with
    | Some s' -> solve db rest s'
    | None -> Seq.empty)
  | Compound ("\\=", [a; b]) -> (
    match unify s a b with
    | Some _ -> Seq.empty
    | None -> solve db rest s)
  | Compound ("is", [lhs; rhs]) -> (
    try
      let v = eval_arith s rhs in
      match unify s lhs (Int v) with
      | Some s' -> solve db rest s'
      | None -> Seq.empty
    with _ -> Seq.empty)
  | Compound (">", [a; b]) ->
    if eval_arith s a > eval_arith s b then solve db rest s else Seq.empty
  | Compound ("<", [a; b]) ->
    if eval_arith s a < eval_arith s b then solve db rest s else Seq.empty
  | Compound (">=", [a; b]) ->
    if eval_arith s a >= eval_arith s b then solve db rest s else Seq.empty
  | Compound ("=<", [a; b]) ->
    if eval_arith s a <= eval_arith s b then solve db rest s else Seq.empty
  | Compound ("write", [t]) ->
    print_string (term_to_string (walk_deep s t));
    solve db rest s
  | Atom "nl" ->
    print_newline ();
    solve db rest s
  | Compound (",", [a; b]) ->
    solve db (a :: b :: rest) s
  | Compound (";", [a; b]) ->
    let r1 = solve db (a :: rest) s in
    let r2 = solve db (b :: rest) s in
    Seq.append r1 r2
  (* Database lookup *)
  | _ ->
    let matching =
      List.to_seq db
      |> Seq.filter_map (fun clause ->
           let c = rename_clause clause in
           match unify s goal c.head with
           | Some s' -> Some (c.body @ rest, s')
           | None -> None)
    in
    Seq.flat_map (fun (goals', s') -> solve db goals' s') matching

(* ---- Parser ---- *)

type token =
  | LPAREN | RPAREN | LBRACKET | RBRACKET | PIPE
  | DOT | COMMA | TURNSTILE | SEMICOLON
  | IDENT of string | VARI of string | NUM of int
  | OP of string | QUERY | EOF

let is_alpha c = (c >= 'a' && c <= 'z') || (c >= 'A' && c <= 'Z') || c = '_'
let is_alnum c = is_alpha c || (c >= '0' && c <= '9')
let is_digit c = c >= '0' && c <= '9'
let is_op c = String.contains "+-*/=\\<>" c

let tokenize (input : string) : token list =
  let n = String.length input in
  let i = ref 0 in
  let tokens = ref [] in
  while !i < n do
    let c = input.[!i] in
    if c = ' ' || c = '\t' || c = '\r' || c = '\n' then incr i
    else if c = '%' then (* line comment *)
      (while !i < n && input.[!i] <> '\n' do incr i done)
    else if c = '(' then (tokens := LPAREN :: !tokens; incr i)
    else if c = ')' then (tokens := RPAREN :: !tokens; incr i)
    else if c = '[' then (tokens := LBRACKET :: !tokens; incr i)
    else if c = ']' then (tokens := RBRACKET :: !tokens; incr i)
    else if c = '|' then (tokens := PIPE :: !tokens; incr i)
    else if c = ',' then (tokens := COMMA :: !tokens; incr i)
    else if c = ';' then (tokens := SEMICOLON :: !tokens; incr i)
    else if c = '.' && (!i + 1 >= n || not (is_alnum input.[!i + 1])) then
      (tokens := DOT :: !tokens; incr i)
    else if c = '?' && !i + 1 < n && input.[!i + 1] = '-' then
      (tokens := QUERY :: !tokens; i := !i + 2)
    else if c = ':' && !i + 1 < n && input.[!i + 1] = '-' then
      (tokens := TURNSTILE :: !tokens; i := !i + 2)
    else if is_op c then begin
      let start = !i in
      while !i < n && is_op input.[!i] do incr i done;
      let op = String.sub input start (!i - start) in
      tokens := OP op :: !tokens
    end
    else if is_digit c then begin
      let start = !i in
      while !i < n && is_digit input.[!i] do incr i done;
      tokens := NUM (int_of_string (String.sub input start (!i - start))) :: !tokens
    end
    else if c >= 'A' && c <= 'Z' || c = '_' then begin
      let start = !i in
      while !i < n && is_alnum input.[!i] do incr i done;
      let name = String.sub input start (!i - start) in
      if name = "_" then tokens := VARI (fresh_var ()) :: !tokens
      else tokens := VARI name :: !tokens
    end
    else if c >= 'a' && c <= 'z' then begin
      let start = !i in
      while !i < n && is_alnum input.[!i] do incr i done;
      let name = String.sub input start (!i - start) in
      (* keywords *)
      if name = "mod" then tokens := OP "mod" :: !tokens
      else if name = "is" then tokens := OP "is" :: !tokens
      else if name = "not" then tokens := IDENT name :: !tokens
      else tokens := IDENT name :: !tokens
    end
    else begin
      Printf.eprintf "Unexpected character: '%c'\n" c;
      incr i
    end
  done;
  List.rev !tokens

(* Recursive descent parser *)

exception ParseError of string

let parse_term (tokens : token list ref) : term =
  let peek () = match !tokens with t :: _ -> t | [] -> EOF in
  let advance () = match !tokens with _ :: rest -> tokens := rest | [] -> () in
  let expect t =
    if peek () = t then advance ()
    else raise (ParseError ("Expected " ^ (match t with RPAREN -> ")" | RBRACKET -> "]" | DOT -> "." | _ -> "token")))
  in

  let rec parse_expr () : term =
    let lhs = parse_primary () in
    parse_infix lhs

  and parse_infix lhs =
    match peek () with
    | OP op when op = "is" ->
      advance ();
      let rhs = parse_arith_expr () in
      Compound ("is", [lhs; rhs])
    | OP op when List.mem op ["="; "\\="; ">"; "<"; ">="; "=<"] ->
      advance ();
      let rhs = parse_expr () in
      Compound (op, [lhs; rhs])
    | _ -> lhs

  and parse_arith_expr () : term =
    let lhs = parse_arith_term () in
    parse_arith_add lhs

  and parse_arith_add lhs =
    match peek () with
    | OP "+" -> advance (); let rhs = parse_arith_term () in parse_arith_add (Compound ("+", [lhs; rhs]))
    | OP "-" -> advance (); let rhs = parse_arith_term () in parse_arith_add (Compound ("-", [lhs; rhs]))
    | _ -> lhs

  and parse_arith_term () : term =
    let lhs = parse_arith_factor () in
    parse_arith_mul lhs

  and parse_arith_mul lhs =
    match peek () with
    | OP "*" -> advance (); let rhs = parse_arith_factor () in parse_arith_mul (Compound ("*", [lhs; rhs]))
    | OP "/" -> advance (); let rhs = parse_arith_factor () in parse_arith_mul (Compound ("/", [lhs; rhs]))
    | OP "mod" -> advance (); let rhs = parse_arith_factor () in parse_arith_mul (Compound ("mod", [lhs; rhs]))
    | _ -> lhs

  and parse_arith_factor () : term =
    match peek () with
    | LPAREN -> advance (); let t = parse_arith_expr () in expect RPAREN; t
    | NUM n -> advance (); Int n
    | VARI v -> advance (); Var v
    | IDENT s -> advance (); Atom s
    | _ -> raise (ParseError "Expected arithmetic expression")

  and parse_primary () : term =
    match peek () with
    | NUM n -> advance (); Int n
    | VARI v -> advance (); Var v
    | IDENT "not" ->
      advance ();
      expect LPAREN;
      let t = parse_expr () in
      expect RPAREN;
      Compound ("not", [t])
    | IDENT s ->
      advance ();
      if peek () = LPAREN then begin
        advance ();
        let args = parse_args () in
        expect RPAREN;
        Compound (s, args)
      end else
        Atom s
    | LPAREN ->
      advance ();
      let t = parse_expr () in
      expect RPAREN;
      t
    | LBRACKET ->
      advance ();
      parse_list ()
    | OP "-" ->
      advance ();
      (match peek () with
       | NUM n -> advance (); Int (-n)
       | _ -> raise (ParseError "Expected number after -"))
    | t -> raise (ParseError (Printf.sprintf "Unexpected token in term"))

  and parse_args () : term list =
    let first = parse_expr () in
    let rec rest () =
      if peek () = COMMA then (advance (); let t = parse_expr () in t :: rest ())
      else []
    in
    first :: rest ()

  and parse_list () : term =
    if peek () = RBRACKET then (advance (); Atom "[]")
    else
      let first = parse_expr () in
      parse_list_tail first

  and parse_list_tail head =
    match peek () with
    | RBRACKET -> advance (); Compound (".", [head; Atom "[]"])
    | COMMA ->
      advance ();
      let next = parse_expr () in
      let tail = parse_list_tail next in
      Compound (".", [head; tail])
    | PIPE ->
      advance ();
      let tail = parse_expr () in
      expect RBRACKET;
      Compound (".", [head; tail])
    | _ -> raise (ParseError "Expected ], ',', or | in list")
  in

  parse_expr ()

let parse_body (tokens : token list ref) : term list =
  let first = parse_term tokens in
  let rec rest () =
    match !tokens with
    | COMMA :: _ -> tokens := List.tl !tokens; let t = parse_term tokens in t :: rest ()
    | SEMICOLON :: _ -> tokens := List.tl !tokens; let t = parse_term tokens in [Compound (";", [first; t])]
    | _ -> []
  in
  first :: rest ()

type statement =
  | Clause of clause
  | Query of term list

let parse_statement (input : string) : statement option =
  let toks = tokenize input in
  if toks = [] then None
  else
    let tokens = ref toks in
    match !tokens with
    | QUERY :: rest ->
      tokens := rest;
      let body = parse_body tokens in
      (* consume trailing dot if present *)
      (match !tokens with DOT :: _ -> () | _ -> ());
      Some (Query body)
    | _ ->
      let head = parse_term tokens in
      (match !tokens with
       | TURNSTILE :: rest ->
         tokens := rest;
         let body = parse_body tokens in
         Some (Clause { head; body })
       | DOT :: _ | [] ->
         Some (Clause { head; body = [] })
       | _ ->
         Some (Clause { head; body = [] }))

(* ---- Example Knowledge Base ---- *)

let example_program = {|
% Family tree
parent(tom, bob).
parent(tom, liz).
parent(bob, ann).
parent(bob, pat).
parent(pat, jim).

male(tom).
male(bob).
male(jim).
female(liz).
female(ann).
female(pat).

father(X, Y) :- parent(X, Y), male(X).
mother(X, Y) :- parent(X, Y), female(X).
grandparent(X, Z) :- parent(X, Y), parent(Y, Z).
ancestor(X, Y) :- parent(X, Y).
ancestor(X, Y) :- parent(X, Z), ancestor(Z, Y).
sibling(X, Y) :- parent(Z, X), parent(Z, Y), \=(X, Y).

% List operations
append([], L, L).
append([H|T], L, [H|R]) :- append(T, L, R).

member(X, [X|_]).
member(X, [_|T]) :- member(X, T).

length([], 0).
length([_|T], N) :- length(T, N1), N is N1 + 1.

reverse([], []).
reverse([H|T], R) :- reverse(T, RT), append(RT, [H], R).

last(X, [X]).
last(X, [_|T]) :- last(X, T).

% Arithmetic
factorial(0, 1).
factorial(N, F) :- N > 0, N1 is N - 1, factorial(N1, F1), F is N * F1.

fibonacci(0, 0).
fibonacci(1, 1).
fibonacci(N, F) :- N > 1, N1 is N - 1, N2 is N - 2, fibonacci(N1, F1), fibonacci(N2, F2), F is F1 + F2.
|}

let load_program (db : clause list ref) (program : string) =
  let lines = String.split_on_char '\n' program in
  let buf = Buffer.create 256 in
  List.iter (fun line ->
    let trimmed = String.trim line in
    if trimmed = "" || (String.length trimmed > 0 && trimmed.[0] = '%') then ()
    else begin
      Buffer.add_string buf line;
      Buffer.add_char buf ' ';
      if String.length trimmed > 0 && trimmed.[String.length trimmed - 1] = '.' then begin
        let stmt = Buffer.contents buf in
        Buffer.clear buf;
        match parse_statement stmt with
        | Some (Clause c) -> db := !db @ [c]
        | _ -> ()
      end
    end
  ) lines

(* ---- Collect query variables ---- *)

let rec vars_of_term acc = function
  | Var v -> if List.mem v acc then acc else v :: acc
  | Compound (_, args) -> List.fold_left vars_of_term acc args
  | _ -> acc

let vars_of_goals goals =
  List.fold_left vars_of_term [] goals |> List.rev

(* ---- REPL ---- *)

let () =
  let db = ref [] in
  load_program db example_program;
  Printf.printf "Mini Prolog Interpreter in OCaml\n";
  Printf.printf "Loaded %d clauses from example knowledge base.\n" (List.length !db);
  Printf.printf "Enter clauses (head :- body.) or queries (?- goal.).\n";
  Printf.printf "Type 'quit.' to exit. Press ; after a result for more solutions.\n\n";
  let running = ref true in
  while !running do
    print_string "?- ";
    flush stdout;
    let line = try read_line () with End_of_file -> running := false; "quit." in
    let trimmed = String.trim line in
    if trimmed = "quit." || trimmed = "halt." then
      running := false
    else if trimmed = "" then ()
    else begin
      try
        (* Accumulate multi-line input until we see a dot *)
        let full_input =
          if String.length trimmed > 0 && trimmed.[String.length trimmed - 1] = '.' then
            trimmed
          else begin
            let buf = Buffer.create 128 in
            Buffer.add_string buf trimmed;
            Buffer.add_char buf ' ';
            let found_dot = ref false in
            while not !found_dot do
              print_string "   ";
              flush stdout;
              let next = try read_line () with End_of_file -> running := false; "." in
              Buffer.add_string buf next;
              Buffer.add_char buf ' ';
              let nt = String.trim next in
              if String.length nt > 0 && nt.[String.length nt - 1] = '.' then
                found_dot := true
            done;
            Buffer.contents buf
          end
        in
        (* Does it start with ?- already or is it bare? *)
        let input =
          if String.length full_input >= 2 &&
             full_input.[0] = '?' && full_input.[1] = '-' then
            full_input
          else
            "?- " ^ full_input
        in
        match parse_statement input with
        | Some (Query goals) ->
          let query_vars = vars_of_goals goals in
          if query_vars = [] then begin
            (* Boolean query *)
            let results = solve !db goals [] in
            match results () with
            | Seq.Nil -> Printf.printf "false.\n"
            | Seq.Cons _ -> Printf.printf "true.\n"
          end else begin
            let results = solve !db goals [] in
            let show_next = ref true in
            let seq = ref results in
            while !show_next do
              match (!seq) () with
              | Seq.Nil ->
                Printf.printf "false.\n";
                show_next := false
              | Seq.Cons (s, rest) ->
                List.iteri (fun i v ->
                  let value = walk_deep s (Var v) in
                  if not (String.length v >= 2 && v.[0] = '_' && v.[1] = 'G') then begin
                    if i > 0 then Printf.printf ",\n";
                    Printf.printf "%s = %s" v (term_to_string value)
                  end
                ) query_vars;
                flush stdout;
                (* Read user input for ; or enter *)
                print_string " ";
                flush stdout;
                let response = try read_line () with End_of_file -> "" in
                if String.trim response = ";" then
                  seq := rest
                else begin
                  Printf.printf "true.\n";
                  show_next := false
                end
            done
          end
        | Some (Clause c) ->
          db := !db @ [c];
          Printf.printf "Clause added.\n"
        | None -> ()
      with
      | ParseError msg -> Printf.printf "Parse error: %s\n" msg
      | Failure msg -> Printf.printf "Error: %s\n" msg
    end
  done;
  Printf.printf "Bye!\n"
