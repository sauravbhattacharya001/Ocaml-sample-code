(* Blackboard Architecture Simulator
   ===================================
   A classic AI cooperative problem-solving system where multiple autonomous
   "knowledge sources" (KS) read from and write to a shared blackboard.

   Features:
   - Shared blackboard with typed entries at multiple abstraction levels
   - Multiple knowledge sources with precondition-triggered activation
   - Scheduler that picks the best KS to run each cycle (priority + relevance)
   - Built-in domains: cryptogram solver, number sequence completion, expression simplifier
   - Event log and execution trace
   - Interactive REPL for step-by-step or auto-run execution

   Usage: ocamlfind ocamlopt -package str -linkpkg blackboard.ml -o blackboard
          (or) ocaml str.cma blackboard.ml

   Run:
     ./blackboard                   -- interactive REPL
     ./blackboard --domain crypto   -- cryptogram solver
     ./blackboard --domain sequence -- number sequence
     ./blackboard --domain simplify -- expression simplifier
     ./blackboard --auto            -- auto-run to completion
*)

(* ── Blackboard Entry ──────────────────────────────────────────────── *)

type level = Raw | Partial | Refined | Solution

let level_to_string = function
  | Raw -> "raw" | Partial -> "partial"
  | Refined -> "refined" | Solution -> "solution"

let level_rank = function
  | Raw -> 0 | Partial -> 1 | Refined -> 2 | Solution -> 3

type entry = {
  key   : string;
  value : string;
  level : level;
  source: string;   (* which KS wrote it *)
  step  : int;      (* when *)
}

(* ── Blackboard ────────────────────────────────────────────────────── *)

type blackboard = {
  mutable entries : entry list;
  mutable step    : int;
  mutable log     : string list;
  mutable solved  : bool;
}

let bb_create () = { entries = []; step = 0; log = []; solved = false }

let bb_write bb ~key ~value ~level ~source =
  let e = { key; value; level; source; step = bb.step } in
  bb.entries <- e :: bb.entries;
  let msg = Printf.sprintf "[step %d] %s wrote %s=%s (%s)"
    bb.step source key value (level_to_string level) in
  bb.log <- msg :: bb.log

let bb_read bb key =
  let matching = List.filter (fun e -> e.key = key) bb.entries in
  (* return highest-level, most recent *)
  let sorted = List.sort (fun a b ->
    let c = compare (level_rank b.level) (level_rank a.level) in
    if c <> 0 then c else compare b.step a.step
  ) matching in
  match sorted with [] -> None | e :: _ -> Some e

let bb_read_all bb key =
  List.filter (fun e -> e.key = key) bb.entries
  |> List.sort (fun a b -> compare b.step a.step)

let bb_has bb key =
  List.exists (fun e -> e.key = key) bb.entries

let bb_keys bb =
  List.map (fun e -> e.key) bb.entries
  |> List.sort_uniq String.compare

(* ── Knowledge Source ──────────────────────────────────────────────── *)

type knowledge_source = {
  ks_name     : string;
  ks_priority : int;    (* higher = more preferred *)
  ks_can_run  : blackboard -> bool;
  ks_run      : blackboard -> unit;
}

(* ── Scheduler ─────────────────────────────────────────────────────── *)

let schedule (sources : knowledge_source list) bb =
  let runnable = List.filter (fun ks -> ks.ks_can_run bb) sources in
  let sorted = List.sort (fun a b -> compare b.ks_priority a.ks_priority) runnable in
  match sorted with [] -> None | ks :: _ -> Some ks

let run_one sources bb =
  match schedule sources bb with
  | None ->
    bb.log <- Printf.sprintf "[step %d] No runnable knowledge source" bb.step :: bb.log;
    false
  | Some ks ->
    bb.log <- Printf.sprintf "[step %d] Scheduler picked: %s" bb.step ks.ks_name :: bb.log;
    ks.ks_run bb;
    bb.step <- bb.step + 1;
    true

let run_all ?(max_steps=100) sources bb =
  let rec loop n =
    if n >= max_steps then
      bb.log <- "[!] Max steps reached" :: bb.log
    else if bb.solved then ()
    else if not (run_one sources bb) then ()
    else loop (n + 1)
  in
  loop 0

(* ── Domain: Cryptogram Solver ─────────────────────────────────────── *)
(* Simple substitution cipher solver using frequency analysis + pattern matching *)

module Crypto = struct
  let english_freq = [
    'e',12.7; 't',9.1; 'a',8.2; 'o',7.5; 'i',7.0; 'n',6.7; 's',6.3;
    'h',6.1; 'r',6.0; 'd',4.3; 'l',4.0; 'c',2.8; 'u',2.8; 'm',2.4;
    'w',2.4; 'f',2.2; 'g',2.0; 'y',2.0; 'p',1.9; 'b',1.5; 'v',1.0;
    'k',0.8; 'j',0.2; 'x',0.2; 'q',0.1; 'z',0.1
  ]

  let count_freq s =
    let tbl = Hashtbl.create 26 in
    String.iter (fun c ->
      if c >= 'a' && c <= 'z' then
        Hashtbl.replace tbl c (1 + try Hashtbl.find tbl c with Not_found -> 0)
    ) (String.lowercase_ascii s);
    let lst = Hashtbl.fold (fun k v acc -> (k,v)::acc) tbl [] in
    List.sort (fun (_,a) (_,b) -> compare b a) lst

  let single_letter_words = ["a"; "i"]
  let common_short = ["the"; "and"; "for"; "are"; "but"; "not"; "you"; "all"; "can"; "had"; "her"; "was"; "one"]

  let words_of s =
    let buf = Buffer.create 16 in
    let acc = ref [] in
    String.iter (fun c ->
      if (c >= 'a' && c <= 'z') || (c >= 'A' && c <= 'Z') then
        Buffer.add_char buf (Char.lowercase_ascii c)
      else begin
        if Buffer.length buf > 0 then begin
          acc := Buffer.contents buf :: !acc;
          Buffer.clear buf
        end
      end
    ) s;
    if Buffer.length buf > 0 then acc := Buffer.contents buf :: !acc;
    List.rev !acc

  let pattern_of w =
    let tbl = Hashtbl.create 8 in
    let next = ref 0 in
    String.init (String.length w) (fun i ->
      let c = w.[i] in
      let n = try Hashtbl.find tbl c with Not_found ->
        let v = !next in incr next; Hashtbl.replace tbl c v; v in
      Char.chr (n + Char.code 'A')
    )

  let setup_puzzle cipher =
    let bb = bb_create () in
    bb_write bb ~key:"cipher" ~value:cipher ~level:Raw ~source:"user";
    bb_write bb ~key:"mapping" ~value:"" ~level:Raw ~source:"init";
    bb

  let get_mapping bb =
    let tbl = Hashtbl.create 26 in
    List.iter (fun e ->
      if String.length e.key = 5 && String.sub e.key 0 4 = "map:" then
        let cipher_c = e.key.[4] in
        let plain_c = e.value.[0] in
        Hashtbl.replace tbl cipher_c plain_c
    ) bb.entries;
    tbl

  let apply_mapping tbl s =
    String.init (String.length s) (fun i ->
      let c = s.[i] in
      let lc = Char.lowercase_ascii c in
      try
        let p = Hashtbl.find tbl lc in
        if c >= 'A' && c <= 'Z' then Char.uppercase_ascii p else p
      with Not_found -> if lc >= 'a' && lc <= 'z' then '_' else c
    )

  let mapped_count bb =
    let tbl = get_mapping bb in Hashtbl.length tbl

  (* KS: Frequency analyzer — maps most frequent cipher letter to 'e', etc. *)
  let ks_freq_analyzer = {
    ks_name = "FreqAnalyzer";
    ks_priority = 10;
    ks_can_run = (fun bb ->
      bb_has bb "cipher" && mapped_count bb < 3
    );
    ks_run = (fun bb ->
      match bb_read bb "cipher" with
      | None -> ()
      | Some e ->
        let freq = count_freq e.value in
        let eng = List.map fst english_freq in
        let to_map = min 5 (List.length freq) in
        for i = 0 to to_map - 1 do
          let (cc, _) = List.nth freq i in
          let pc = List.nth eng i in
          let key = Printf.sprintf "map:%c" cc in
          if not (bb_has bb key) then
            bb_write bb ~key ~value:(String.make 1 pc) ~level:Partial
              ~source:"FreqAnalyzer"
        done
    );
  }

  (* KS: Single-letter word resolver *)
  let ks_single_letter = {
    ks_name = "SingleLetterResolver";
    ks_priority = 15;
    ks_can_run = (fun bb ->
      match bb_read bb "cipher" with
      | None -> false
      | Some e ->
        let ws = words_of e.value in
        List.exists (fun w -> String.length w = 1) ws
        && not (bb_has bb "single_done")
    );
    ks_run = (fun bb ->
      match bb_read bb "cipher" with
      | None -> ()
      | Some e ->
        let ws = words_of e.value in
        let singles = List.filter (fun w -> String.length w = 1) ws
          |> List.sort_uniq String.compare in
        (* In English, single-letter words are 'a' and 'I' *)
        List.iteri (fun i w ->
          if i < List.length single_letter_words then begin
            let plain = List.nth single_letter_words i in
            let key = Printf.sprintf "map:%c" w.[0] in
            bb_write bb ~key ~value:plain ~level:Refined
              ~source:"SingleLetterResolver"
          end
        ) singles;
        bb_write bb ~key:"single_done" ~value:"true" ~level:Raw
          ~source:"SingleLetterResolver"
    );
  }

  (* KS: Pattern matcher — uses word patterns to guess mappings *)
  let ks_pattern_match = {
    ks_name = "PatternMatcher";
    ks_priority = 8;
    ks_can_run = (fun bb ->
      mapped_count bb >= 3 && mapped_count bb < 20
      && not (bb_has bb "pattern_done")
    );
    ks_run = (fun bb ->
      match bb_read bb "cipher" with
      | None -> ()
      | Some e ->
        let ws = words_of e.value in
        let three_letter = List.filter (fun w -> String.length w = 3) ws in
        let tbl = get_mapping bb in
        (* Try to match 3-letter words against common words *)
        List.iter (fun cw ->
          let pat = pattern_of cw in
          List.iter (fun common ->
            if String.length common = 3 && pattern_of common = pat then begin
              for i = 0 to 2 do
                let cc = cw.[i] in
                let pc = common.[i] in
                let key = Printf.sprintf "map:%c" cc in
                if not (Hashtbl.mem tbl cc) then
                  bb_write bb ~key ~value:(String.make 1 pc)
                    ~level:Refined ~source:"PatternMatcher"
              done
            end
          ) common_short
        ) three_letter;
        bb_write bb ~key:"pattern_done" ~value:"true" ~level:Raw
          ~source:"PatternMatcher"
    );
  }

  (* KS: Solution checker *)
  let ks_checker = {
    ks_name = "SolutionChecker";
    ks_priority = 5;
    ks_can_run = (fun bb -> mapped_count bb >= 5 && not bb.solved);
    ks_run = (fun bb ->
      match bb_read bb "cipher" with
      | None -> ()
      | Some e ->
        let tbl = get_mapping bb in
        let decoded = apply_mapping tbl e.value in
        bb_write bb ~key:"decoded" ~value:decoded ~level:Solution
          ~source:"SolutionChecker";
        let underscores = String.fold_left (fun n c -> if c = '_' then n+1 else n) 0 decoded in
        let alpha = String.fold_left (fun n c ->
          if (c >= 'a' && c <= 'z') || (c >= 'A' && c <= 'Z') || c = '_' then n+1 else n
        ) 0 decoded in
        if alpha > 0 && (float underscores /. float alpha) < 0.15 then begin
          bb.solved <- true;
          bb_write bb ~key:"status" ~value:"solved" ~level:Solution
            ~source:"SolutionChecker"
        end
    );
  }

  let all_ks = [ks_freq_analyzer; ks_single_letter; ks_pattern_match; ks_checker]

  let demo () =
    (* Simple substitution: shift by 3 (Caesar) *)
    let plaintext = "the quick brown fox jumps over a lazy dog" in
    let cipher = String.init (String.length plaintext) (fun i ->
      let c = plaintext.[i] in
      if c >= 'a' && c <= 'z' then
        Char.chr ((Char.code c - Char.code 'a' + 3) mod 26 + Char.code 'a')
      else c
    ) in
    let bb = setup_puzzle cipher in
    (bb, all_ks, cipher, plaintext)
end

(* ── Domain: Number Sequence Completion ────────────────────────────── *)

module Sequence = struct
  let setup_puzzle nums =
    let bb = bb_create () in
    let s = String.concat "," (List.map string_of_int nums) in
    bb_write bb ~key:"sequence" ~value:s ~level:Raw ~source:"user";
    bb

  let parse_seq s =
    String.split_on_char ',' s
    |> List.filter_map (fun t ->
      let t = String.trim t in
      try Some (int_of_string t) with _ -> None)

  (* KS: Constant difference detector *)
  let ks_const_diff = {
    ks_name = "ConstDiffDetector";
    ks_priority = 12;
    ks_can_run = (fun bb ->
      bb_has bb "sequence" && not (bb_has bb "pattern_type")
    );
    ks_run = (fun bb ->
      match bb_read bb "sequence" with
      | None -> ()
      | Some e ->
        let nums = parse_seq e.value in
        if List.length nums >= 3 then begin
          let diffs = List.combine (List.tl nums)
            (List.filteri (fun i _ -> i < List.length nums - 1) nums)
            |> List.map (fun (a,b) -> a - b) in
          let all_same = match diffs with
            | [] -> false
            | d :: rest -> List.for_all ((=) d) rest in
          if all_same then begin
            let d = List.hd diffs in
            bb_write bb ~key:"pattern_type" ~value:"arithmetic"
              ~level:Refined ~source:"ConstDiffDetector";
            bb_write bb ~key:"common_diff" ~value:(string_of_int d)
              ~level:Refined ~source:"ConstDiffDetector";
            let last = List.nth nums (List.length nums - 1) in
            let next = last + d in
            bb_write bb ~key:"next" ~value:(string_of_int next)
              ~level:Solution ~source:"ConstDiffDetector";
            bb.solved <- true
          end
        end
    );
  }

  (* KS: Constant ratio detector *)
  let ks_const_ratio = {
    ks_name = "ConstRatioDetector";
    ks_priority = 11;
    ks_can_run = (fun bb ->
      bb_has bb "sequence" && not (bb_has bb "pattern_type")
    );
    ks_run = (fun bb ->
      match bb_read bb "sequence" with
      | None -> ()
      | Some e ->
        let nums = parse_seq e.value in
        if List.length nums >= 3 then begin
          let ratios = List.combine (List.tl nums)
            (List.filteri (fun i _ -> i < List.length nums - 1) nums)
            |> List.filter_map (fun (a,b) ->
              if b <> 0 && a mod b = 0 then Some (a / b) else None) in
          if List.length ratios = List.length nums - 1 then begin
            let all_same = match ratios with
              | [] -> false
              | r :: rest -> List.for_all ((=) r) rest in
            if all_same then begin
              let r = List.hd ratios in
              bb_write bb ~key:"pattern_type" ~value:"geometric"
                ~level:Refined ~source:"ConstRatioDetector";
              bb_write bb ~key:"common_ratio" ~value:(string_of_int r)
                ~level:Refined ~source:"ConstRatioDetector";
              let last = List.nth nums (List.length nums - 1) in
              let next = last * r in
              bb_write bb ~key:"next" ~value:(string_of_int next)
                ~level:Solution ~source:"ConstRatioDetector";
              bb.solved <- true
            end
          end
        end
    );
  }

  (* KS: Second-difference (quadratic) detector *)
  let ks_second_diff = {
    ks_name = "SecondDiffDetector";
    ks_priority = 9;
    ks_can_run = (fun bb ->
      bb_has bb "sequence" && not (bb_has bb "pattern_type")
    );
    ks_run = (fun bb ->
      match bb_read bb "sequence" with
      | None -> ()
      | Some e ->
        let nums = parse_seq e.value in
        if List.length nums >= 4 then begin
          let diffs = List.combine (List.tl nums)
            (List.filteri (fun i _ -> i < List.length nums - 1) nums)
            |> List.map (fun (a,b) -> a - b) in
          let diffs2 = List.combine (List.tl diffs)
            (List.filteri (fun i _ -> i < List.length diffs - 1) diffs)
            |> List.map (fun (a,b) -> a - b) in
          let all_same = match diffs2 with
            | [] -> false
            | d :: rest -> List.for_all ((=) d) rest in
          if all_same then begin
            let d2 = List.hd diffs2 in
            bb_write bb ~key:"pattern_type" ~value:"quadratic"
              ~level:Refined ~source:"SecondDiffDetector";
            bb_write bb ~key:"second_diff" ~value:(string_of_int d2)
              ~level:Refined ~source:"SecondDiffDetector";
            let last_d = List.nth diffs (List.length diffs - 1) in
            let next_d = last_d + d2 in
            let last = List.nth nums (List.length nums - 1) in
            let next = last + next_d in
            bb_write bb ~key:"next" ~value:(string_of_int next)
              ~level:Solution ~source:"SecondDiffDetector";
            bb.solved <- true
          end
        end
    );
  }

  (* KS: Fibonacci-like detector *)
  let ks_fib = {
    ks_name = "FibonacciDetector";
    ks_priority = 10;
    ks_can_run = (fun bb ->
      bb_has bb "sequence" && not (bb_has bb "pattern_type")
    );
    ks_run = (fun bb ->
      match bb_read bb "sequence" with
      | None -> ()
      | Some e ->
        let nums = parse_seq e.value in
        if List.length nums >= 4 then begin
          let is_fib = ref true in
          for i = 2 to List.length nums - 1 do
            if List.nth nums i <> List.nth nums (i-1) + List.nth nums (i-2) then
              is_fib := false
          done;
          if !is_fib then begin
            bb_write bb ~key:"pattern_type" ~value:"fibonacci-like"
              ~level:Refined ~source:"FibonacciDetector";
            let n = List.length nums in
            let next = List.nth nums (n-1) + List.nth nums (n-2) in
            bb_write bb ~key:"next" ~value:(string_of_int next)
              ~level:Solution ~source:"FibonacciDetector";
            bb.solved <- true
          end
        end
    );
  }

  let all_ks = [ks_const_diff; ks_const_ratio; ks_second_diff; ks_fib]

  let demo () =
    let nums = [2; 6; 18; 54; 162] in
    let bb = setup_puzzle nums in
    (bb, all_ks, nums)
end

(* ── Domain: Expression Simplifier ─────────────────────────────────── *)

module Simplify = struct
  type expr =
    | Num of int
    | Var of string
    | Add of expr * expr
    | Mul of expr * expr
    | Sub of expr * expr
    | Neg of expr

  let rec expr_to_string = function
    | Num n -> string_of_int n
    | Var x -> x
    | Add (a, b) -> Printf.sprintf "(%s + %s)" (expr_to_string a) (expr_to_string b)
    | Mul (a, b) -> Printf.sprintf "(%s * %s)" (expr_to_string a) (expr_to_string b)
    | Sub (a, b) -> Printf.sprintf "(%s - %s)" (expr_to_string a) (expr_to_string b)
    | Neg a -> Printf.sprintf "(-%s)" (expr_to_string a)

  (* Simple tokenizer and parser *)
  type token = TNum of int | TVar of string | TPlus | TMinus | TStar | TLParen | TRParen

  let tokenize s =
    let tokens = ref [] in
    let i = ref 0 in
    let len = String.length s in
    while !i < len do
      let c = s.[!i] in
      if c = ' ' then incr i
      else if c >= '0' && c <= '9' then begin
        let start = !i in
        while !i < len && s.[!i] >= '0' && s.[!i] <= '9' do incr i done;
        tokens := TNum (int_of_string (String.sub s start (!i - start))) :: !tokens
      end
      else if (c >= 'a' && c <= 'z') || (c >= 'A' && c <= 'Z') then begin
        let start = !i in
        while !i < len && ((s.[!i] >= 'a' && s.[!i] <= 'z') || (s.[!i] >= 'A' && s.[!i] <= 'Z')) do incr i done;
        tokens := TVar (String.sub s start (!i - start)) :: !tokens
      end
      else begin
        (match c with
         | '+' -> tokens := TPlus :: !tokens
         | '-' -> tokens := TMinus :: !tokens
         | '*' -> tokens := TStar :: !tokens
         | '(' -> tokens := TLParen :: !tokens
         | ')' -> tokens := TRParen :: !tokens
         | _ -> ());
        incr i
      end
    done;
    List.rev !tokens

  (* Recursive descent parser *)
  let parse s =
    let toks = ref (tokenize s) in
    let peek () = match !toks with t :: _ -> Some t | [] -> None in
    let advance () = match !toks with _ :: rest -> toks := rest | [] -> () in
    let rec parse_expr () = parse_add ()
    and parse_add () =
      let left = ref (parse_mul ()) in
      let continue = ref true in
      while !continue do
        match peek () with
        | Some TPlus -> advance (); left := Add (!left, parse_mul ())
        | Some TMinus -> advance (); left := Sub (!left, parse_mul ())
        | _ -> continue := false
      done;
      !left
    and parse_mul () =
      let left = ref (parse_unary ()) in
      let continue = ref true in
      while !continue do
        match peek () with
        | Some TStar -> advance (); left := Mul (!left, parse_unary ())
        | _ -> continue := false
      done;
      !left
    and parse_unary () =
      match peek () with
      | Some TMinus -> advance (); Neg (parse_unary ())
      | _ -> parse_atom ()
    and parse_atom () =
      match peek () with
      | Some (TNum n) -> advance (); Num n
      | Some (TVar x) -> advance (); Var x
      | Some TLParen -> advance (); let e = parse_expr () in
        (match peek () with Some TRParen -> advance () | _ -> ()); e
      | _ -> Num 0
    in
    parse_expr ()

  (* Simplification rules *)
  let rec simplify = function
    | Add (Num 0, b) -> simplify b
    | Add (a, Num 0) -> simplify a
    | Add (Num a, Num b) -> Num (a + b)
    | Mul (Num 0, _) -> Num 0
    | Mul (_, Num 0) -> Num 0
    | Mul (Num 1, b) -> simplify b
    | Mul (a, Num 1) -> simplify a
    | Mul (Num a, Num b) -> Num (a * b)
    | Sub (a, Num 0) -> simplify a
    | Sub (Num a, Num b) -> Num (a - b)
    | Neg (Num 0) -> Num 0
    | Neg (Neg a) -> simplify a
    | Neg (Num n) -> Num (-n)
    | Add (a, b) ->
      let a' = simplify a and b' = simplify b in
      if a' = a && b' = b then Add (a, b) else simplify (Add (a', b'))
    | Mul (a, b) ->
      let a' = simplify a and b' = simplify b in
      if a' = a && b' = b then Mul (a, b) else simplify (Mul (a', b'))
    | Sub (a, b) ->
      let a' = simplify a and b' = simplify b in
      if a' = a && b' = b then Sub (a, b) else simplify (Sub (a', b'))
    | Neg a ->
      let a' = simplify a in
      if a' = a then Neg a else simplify (Neg a')
    | x -> x

  let setup_puzzle expr_str =
    let bb = bb_create () in
    bb_write bb ~key:"expr" ~value:expr_str ~level:Raw ~source:"user";
    bb

  (* KS: Parser *)
  let ks_parser = {
    ks_name = "ExprParser";
    ks_priority = 15;
    ks_can_run = (fun bb -> bb_has bb "expr" && not (bb_has bb "parsed"));
    ks_run = (fun bb ->
      match bb_read bb "expr" with
      | None -> ()
      | Some e ->
        let ast = parse e.value in
        bb_write bb ~key:"parsed" ~value:(expr_to_string ast) ~level:Partial
          ~source:"ExprParser"
    );
  }

  (* KS: Constant folder *)
  let ks_fold = {
    ks_name = "ConstantFolder";
    ks_priority = 12;
    ks_can_run = (fun bb -> bb_has bb "parsed" && not (bb_has bb "folded"));
    ks_run = (fun bb ->
      match bb_read bb "expr" with
      | None -> ()
      | Some e ->
        let ast = parse e.value in
        let simplified = simplify ast in
        let result = expr_to_string simplified in
        bb_write bb ~key:"folded" ~value:result ~level:Refined
          ~source:"ConstantFolder";
        bb_write bb ~key:"simplified" ~value:result ~level:Solution
          ~source:"ConstantFolder";
        bb.solved <- true
    );
  }

  let all_ks = [ks_parser; ks_fold]

  let demo () =
    let expr_str = "(3 + 0) * (x + (2 * 1)) - (0 * y)" in
    let bb = setup_puzzle expr_str in
    (bb, all_ks, expr_str)
end

(* ── Pretty Printing ───────────────────────────────────────────────── *)

let print_blackboard bb =
  Printf.printf "\n╔══════════════════════════════════════════════════════╗\n";
  Printf.printf "║             BLACKBOARD  (step %d)                    ║\n" bb.step;
  Printf.printf "╠══════════════════════════════════════════════════════╣\n";
  let keys = bb_keys bb in
  List.iter (fun key ->
    match bb_read bb key with
    | None -> ()
    | Some e ->
      let v = if String.length e.value > 40
        then String.sub e.value 0 37 ^ "..."
        else e.value in
      Printf.printf "║ %-14s │ %-8s │ %-22s ║\n"
        key (level_to_string e.level) v
  ) keys;
  Printf.printf "╚══════════════════════════════════════════════════════╝\n";
  if bb.solved then
    Printf.printf "  ✓ SOLVED\n"

let print_log bb =
  Printf.printf "\n── Execution Trace ──\n";
  List.rev bb.log |> List.iter (fun l -> Printf.printf "  %s\n" l)

let print_help () =
  Printf.printf "\n";
  Printf.printf "╔══════════════════════════════════════════════════════╗\n";
  Printf.printf "║       Blackboard Architecture Simulator             ║\n";
  Printf.printf "║  Cooperative multi-agent problem solving in OCaml   ║\n";
  Printf.printf "╠══════════════════════════════════════════════════════╣\n";
  Printf.printf "║  Commands:                                          ║\n";
  Printf.printf "║    step          - run one knowledge source         ║\n";
  Printf.printf "║    run           - run to completion                ║\n";
  Printf.printf "║    board         - show blackboard state            ║\n";
  Printf.printf "║    log           - show execution trace             ║\n";
  Printf.printf "║    agents        - list knowledge sources           ║\n";
  Printf.printf "║    reset         - reset current domain             ║\n";
  Printf.printf "║    domain <name> - switch domain                    ║\n";
  Printf.printf "║                    (crypto, sequence, simplify)     ║\n";
  Printf.printf "║    help          - show this help                   ║\n";
  Printf.printf "║    quit          - exit                             ║\n";
  Printf.printf "╚══════════════════════════════════════════════════════╝\n"

(* ── REPL ──────────────────────────────────────────────────────────── *)

type domain = DCrypto | DSequence | DSimplify

let setup_domain = function
  | DCrypto ->
    let (bb, ks, cipher, _plain) = Crypto.demo () in
    Printf.printf "\n🔐 Cryptogram Solver\n";
    Printf.printf "   Cipher: %s\n" cipher;
    (bb, ks)
  | DSequence ->
    let (bb, ks, nums) = Sequence.demo () in
    Printf.printf "\n🔢 Number Sequence Completion\n";
    Printf.printf "   Sequence: %s\n"
      (String.concat ", " (List.map string_of_int nums));
    (bb, ks)
  | DSimplify ->
    let (bb, ks, expr) = Simplify.demo () in
    Printf.printf "\n📐 Expression Simplifier\n";
    Printf.printf "   Expression: %s\n" expr;
    (bb, ks)

let domain_of_string = function
  | "crypto" -> Some DCrypto
  | "sequence" -> Some DSequence
  | "simplify" -> Some DSimplify
  | _ -> None

let () =
  let auto = ref false in
  let domain = ref DCrypto in
  (* Parse args *)
  let args = Array.to_list Sys.argv |> List.tl in
  let rec parse_args = function
    | [] -> ()
    | "--auto" :: rest -> auto := true; parse_args rest
    | "--domain" :: d :: rest ->
      (match domain_of_string d with
       | Some dom -> domain := dom
       | None -> Printf.printf "Unknown domain: %s\n" d);
      parse_args rest
    | _ :: rest -> parse_args rest
  in
  parse_args args;

  let bb = ref (fst (setup_domain !domain)) in
  let ks = ref (snd (setup_domain !domain)) in

  if !auto then begin
    Printf.printf "\n⚡ Auto-running to completion...\n";
    run_all !ks !bb;
    print_blackboard !bb;
    print_log !bb
  end else begin
    print_help ();
    print_blackboard !bb;
    let running = ref true in
    while !running do
      Printf.printf "\nblackboard> %!";
      let line = try input_line stdin with End_of_file -> "quit" in
      let cmd = String.trim line in
      match cmd with
      | "quit" | "exit" | "q" ->
        Printf.printf "Goodbye!\n"; running := false
      | "step" | "s" ->
        if !bb.solved then
          Printf.printf "Already solved!\n"
        else if run_one !ks !bb then begin
          print_blackboard !bb
        end else
          Printf.printf "No knowledge source can run.\n"
      | "run" | "r" ->
        if !bb.solved then
          Printf.printf "Already solved!\n"
        else begin
          run_all !ks !bb;
          print_blackboard !bb
        end
      | "board" | "b" -> print_blackboard !bb
      | "log" | "l" -> print_log !bb
      | "agents" | "a" ->
        Printf.printf "\n── Knowledge Sources ──\n";
        List.iter (fun k ->
          Printf.printf "  [%d] %-25s %s\n"
            k.ks_priority k.ks_name
            (if k.ks_can_run !bb then "✓ ready" else "✗ blocked")
        ) !ks
      | "reset" ->
        let (b, k) = setup_domain !domain in
        bb := b; ks := k;
        print_blackboard !bb
      | "help" | "h" -> print_help ()
      | _ ->
        if String.length cmd > 7 && String.sub cmd 0 7 = "domain " then begin
          let d = String.trim (String.sub cmd 7 (String.length cmd - 7)) in
          match domain_of_string d with
          | Some dom ->
            domain := dom;
            let (b, k) = setup_domain dom in
            bb := b; ks := k;
            print_blackboard !bb
          | None -> Printf.printf "Unknown domain: %s (try: crypto, sequence, simplify)\n" d
        end else
          Printf.printf "Unknown command. Type 'help' for commands.\n"
    done
  end
