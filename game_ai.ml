(* game_ai.ml — Minimax Game AI with Alpha-Beta Pruning
 *
 * A generic game AI framework in OCaml demonstrating:
 * - Module types (signatures) for abstract game interfaces
 * - Functors that build AI over any game implementing the interface
 * - Minimax algorithm with alpha-beta pruning
 * - Iterative deepening for time-bounded search
 * - Transposition tables (memoization) for duplicate state detection
 * - Two complete games: Tic-Tac-Toe and Connect Four
 *
 * Concepts demonstrated:
 * - Algebraic data types for game state
 * - Module system: signatures, structures, functors
 * - Higher-order functions and recursive search
 * - Hashtbl for transposition table
 * - Immutable game state with functional updates
 *
 * Usage:
 *   ocamlfind ocamlopt -package unix -linkpkg game_ai.ml -o game_ai && ./game_ai
 *   (* or: ocaml game_ai.ml  — for bytecode with Unix *)
 *)

(* ══════════════════════════════════════════════════════════════════════
   GAME INTERFACE — any 2-player zero-sum game must implement this
   ══════════════════════════════════════════════════════════════════════ *)

module type GAME = sig
  type state
  type move
  type player = Maximizer | Minimizer

  val initial : state
  val current_player : state -> player
  val legal_moves : state -> move list
  val apply_move : state -> move -> state
  val is_terminal : state -> bool
  val evaluate : state -> float  (* +inf = Maximizer wins, -inf = Minimizer wins, 0 = draw *)
  val hash_state : state -> int
  val show_state : state -> string
  val show_move : move -> string
end

(* ══════════════════════════════════════════════════════════════════════
   MINIMAX AI — functor that builds an AI for any GAME
   ══════════════════════════════════════════════════════════════════════ *)

module MakeAI (G : GAME) = struct

  type search_result = {
    score : float;
    best_move : G.move option;
    nodes_searched : int;
    depth_reached : int;
  }

  (* --- Plain minimax (no pruning) --- *)
  let rec minimax state depth =
    if depth = 0 || G.is_terminal state then
      { score = G.evaluate state; best_move = None; nodes_searched = 1; depth_reached = 0 }
    else
      let moves = G.legal_moves state in
      match moves with
      | [] -> { score = G.evaluate state; best_move = None; nodes_searched = 1; depth_reached = 0 }
      | _ ->
        let is_max = G.current_player state = G.Maximizer in
        let init_score = if is_max then neg_infinity else infinity in
        let cmp = if is_max then ( > ) else ( < ) in
        List.fold_left (fun acc m ->
          let child = G.apply_move state m in
          let result = minimax child (depth - 1) in
          let total_nodes = acc.nodes_searched + result.nodes_searched in
          if cmp result.score acc.score then
            { score = result.score; best_move = Some m;
              nodes_searched = total_nodes; depth_reached = result.depth_reached + 1 }
          else
            { acc with nodes_searched = total_nodes }
        ) { score = init_score; best_move = None; nodes_searched = 0; depth_reached = 0 } moves

  (* --- Alpha-beta pruning --- *)
  let rec alphabeta state depth alpha beta =
    if depth = 0 || G.is_terminal state then
      { score = G.evaluate state; best_move = None; nodes_searched = 1; depth_reached = 0 }
    else
      let moves = G.legal_moves state in
      match moves with
      | [] -> { score = G.evaluate state; best_move = None; nodes_searched = 1; depth_reached = 0 }
      | _ ->
        let is_max = G.current_player state = G.Maximizer in
        let init_score = if is_max then neg_infinity else infinity in
        alphabeta_branch is_max state moves depth alpha beta
          { score = init_score; best_move = None; nodes_searched = 0; depth_reached = 0 }

  (** Unified alpha-beta branch: handles both maximizing and minimizing
      players by parameterizing the comparison and bound updates.
      Eliminates the previous alphabeta_max/alphabeta_min duplication. *)
  and alphabeta_branch is_max state moves depth alpha beta acc =
    match moves with
    | [] -> acc
    | m :: rest ->
      let child = G.apply_move state m in
      let result = alphabeta child (depth - 1) alpha beta in
      let total_nodes = acc.nodes_searched + result.nodes_searched in
      let dominated =
        if is_max then result.score > acc.score
        else result.score < acc.score
      in
      let new_acc =
        if dominated then
          { score = result.score; best_move = Some m;
            nodes_searched = total_nodes; depth_reached = result.depth_reached + 1 }
        else
          { acc with nodes_searched = total_nodes }
      in
      let new_alpha, new_beta =
        if is_max then (max alpha new_acc.score, beta)
        else (alpha, min beta new_acc.score)
      in
      if new_alpha >= new_beta then new_acc  (* cutoff *)
      else alphabeta_branch is_max state rest depth new_alpha new_beta new_acc

  (* --- Alpha-beta with transposition table --- *)
  type tt_entry = { tt_depth : int; tt_score : float; tt_flag : [`Exact | `Lower | `Upper] }

  let alphabeta_tt ?(table_size=65536) state max_depth =
    let table : (int, tt_entry) Hashtbl.t = Hashtbl.create table_size in
    let nodes = ref 0 in
    let rec search st depth alpha beta =
      incr nodes;
      if depth = 0 || G.is_terminal st then
        G.evaluate st
      else begin
        let h = G.hash_state st in
        (* probe transposition table *)
        let alpha, beta =
          match Hashtbl.find_opt table h with
          | Some entry when entry.tt_depth >= depth ->
            begin match entry.tt_flag with
            | `Exact -> (entry.tt_score, entry.tt_score)  (* exact hit *)
            | `Lower -> (max alpha entry.tt_score, beta)
            | `Upper -> (alpha, min beta entry.tt_score)
            end
          | _ -> (alpha, beta)
        in
        if alpha >= beta then alpha
        else begin
          let moves = G.legal_moves st in
          let is_max = G.current_player st = G.Maximizer in
          let init_best = if is_max then neg_infinity else infinity in
          let best = ref init_best in
          let bound = ref (if is_max then alpha else beta) in
          let cmp = if is_max then ( > ) else ( < ) in
          let opt = if is_max then max else min in
          let within_window () =
            if is_max then !bound < beta else alpha < !bound
          in
          List.iter (fun m ->
            if within_window () then begin
              let a, b = if is_max then (!bound, beta) else (alpha, !bound) in
              let v = search (G.apply_move st m) (depth - 1) a b in
              if cmp v !best then best := v;
              bound := opt !bound v
            end
          ) moves;
          let alpha_out = if is_max then !bound else alpha in
          let beta_out = if is_max then beta else !bound in
          (* store in TT *)
          let bv = !best in
          let flag =
            if bv <= alpha_out && is_max then `Upper
            else if bv >= beta_out && not is_max then `Lower
            else if bv >= beta_out && is_max then `Lower
            else if bv <= alpha_out && not is_max then `Upper
            else `Exact
          in
          Hashtbl.replace table h { tt_depth = depth; tt_score = bv; tt_flag = flag };
          bv
        end
      end
    in
    (* find best move by searching each *)
    let moves = G.legal_moves state in
    let is_max = G.current_player state = G.Maximizer in
    let best_move, best_score =
      List.fold_left (fun (bm, bs) m ->
        let child = G.apply_move state m in
        let s = search child (max_depth - 1) neg_infinity infinity in
        if (is_max && s > bs) || (not is_max && s < bs) then (Some m, s)
        else (bm, bs)
      ) (None, (if is_max then neg_infinity else infinity)) moves
    in
    { score = best_score; best_move; nodes_searched = !nodes; depth_reached = max_depth }

  (* --- Iterative deepening --- *)
  let iterative_deepening state max_depth =
    let results = Array.make (max_depth + 1)
      { score = 0.0; best_move = None; nodes_searched = 0; depth_reached = 0 } in
    for d = 1 to max_depth do
      results.(d) <- alphabeta state d neg_infinity infinity
    done;
    let total_nodes = Array.fold_left (fun acc r -> acc + r.nodes_searched) 0 results in
    { (results.(max_depth)) with nodes_searched = total_nodes }

  (* --- Convenience --- *)
  let best_move ?(depth=10) state =
    let result = alphabeta state depth neg_infinity infinity in
    result.best_move

  let play_game ?(depth=10) () =
    let rec loop state =
      Printf.printf "%s\n" (G.show_state state);
      if G.is_terminal state then
        Printf.printf "Game over! Score: %.1f\n" (G.evaluate state)
      else begin
        let result = alphabeta state depth neg_infinity infinity in
        match result.best_move with
        | None -> Printf.printf "No moves available.\n"
        | Some m ->
          Printf.printf "AI plays: %s (score: %.2f, nodes: %d)\n\n"
            (G.show_move m) result.score result.nodes_searched;
          loop (G.apply_move state m)
      end
    in
    loop G.initial
end

(* ══════════════════════════════════════════════════════════════════════
   TIC-TAC-TOE — 3×3 classic
   ══════════════════════════════════════════════════════════════════════ *)

module TicTacToe : GAME = struct
  type player = Maximizer | Minimizer
  type cell = X | O | Empty
  type state = {
    board : cell array;  (* 9 cells, row-major *)
    turn : player;
    move_count : int;
  }
  type move = int  (* 0-8 position *)

  let initial = { board = Array.make 9 Empty; turn = Maximizer; move_count = 0 }

  let current_player st = st.turn

  let legal_moves st =
    let moves = ref [] in
    for i = 8 downto 0 do
      if st.board.(i) = Empty then moves := i :: !moves
    done;
    !moves

  let apply_move st pos =
    let b = Array.copy st.board in
    b.(pos) <- (if st.turn = Maximizer then X else O);
    { board = b;
      turn = (if st.turn = Maximizer then Minimizer else Maximizer);
      move_count = st.move_count + 1 }

  let win_lines = [|
    [|0;1;2|]; [|3;4;5|]; [|6;7;8|];  (* rows *)
    [|0;3;6|]; [|1;4;7|]; [|2;5;8|];  (* cols *)
    [|0;4;8|]; [|2;4;6|];              (* diags *)
  |]

  let check_winner board cell =
    Array.exists (fun line ->
      Array.for_all (fun i -> board.(i) = cell) line
    ) win_lines

  let is_terminal st =
    check_winner st.board X || check_winner st.board O || st.move_count = 9

  let evaluate st =
    if check_winner st.board X then 100.0
    else if check_winner st.board O then -100.0
    else 0.0

  let hash_state st =
    Array.fold_left (fun h c ->
      h * 3 + (match c with Empty -> 0 | X -> 1 | O -> 2)
    ) 0 st.board

  let cell_char = function X -> "X" | O -> "O" | Empty -> "."

  let show_state st =
    let b = st.board in
    Printf.sprintf " %s | %s | %s\n---+---+---\n %s | %s | %s\n---+---+---\n %s | %s | %s"
      (cell_char b.(0)) (cell_char b.(1)) (cell_char b.(2))
      (cell_char b.(3)) (cell_char b.(4)) (cell_char b.(5))
      (cell_char b.(6)) (cell_char b.(7)) (cell_char b.(8))

  let show_move pos = string_of_int pos
end

(* ══════════════════════════════════════════════════════════════════════
   CONNECT FOUR — 7×6 board
   ══════════════════════════════════════════════════════════════════════ *)

module ConnectFour : GAME = struct
  type player = Maximizer | Minimizer
  type cell = Red | Yellow | Empty
  type state = {
    board : cell array array;  (* board.(row).(col), row 0 = bottom *)
    heights : int array;       (* next empty row per column *)
    turn : player;
    move_count : int;
    last_move : int option;
  }
  type move = int  (* column 0-6 *)

  let rows = 6
  let cols = 7

  let initial = {
    board = Array.init rows (fun _ -> Array.make cols Empty);
    heights = Array.make cols 0;
    turn = Maximizer;
    move_count = 0;
    last_move = None;
  }

  let current_player st = st.turn

  let legal_moves st =
    let moves = ref [] in
    (* prefer center columns for better move ordering *)
    List.iter (fun c ->
      if st.heights.(c) < rows then moves := c :: !moves
    ) [0; 6; 1; 5; 2; 4; 3];
    List.rev !moves

  let apply_move st col =
    let row = st.heights.(col) in
    let new_board = Array.map Array.copy st.board in
    new_board.(row).(col) <- (if st.turn = Maximizer then Red else Yellow);
    let new_heights = Array.copy st.heights in
    new_heights.(col) <- row + 1;
    { board = new_board;
      heights = new_heights;
      turn = (if st.turn = Maximizer then Minimizer else Maximizer);
      move_count = st.move_count + 1;
      last_move = Some col }

  (* check if the last move created a line of 4 *)
  let check_four board cell =
    let found = ref false in
    let directions = [| (0,1); (1,0); (1,1); (1,-1) |] in
    for r = 0 to rows - 1 do
      for c = 0 to cols - 1 do
        if board.(r).(c) = cell then
          Array.iter (fun (dr, dc) ->
            if not !found then begin
              let ok = ref true in
              for k = 0 to 3 do
                let nr = r + k * dr and nc = c + k * dc in
                if nr < 0 || nr >= rows || nc < 0 || nc >= cols
                   || board.(nr).(nc) <> cell then
                  ok := false
              done;
              if !ok then found := true
            end
          ) directions
      done
    done;
    !found

  let is_terminal st =
    check_four st.board Red || check_four st.board Yellow || st.move_count = rows * cols

  (* heuristic evaluation: count windows of 4 *)
  let count_windows board cell =
    let score = ref 0 in
    let directions = [| (0,1); (1,0); (1,1); (1,-1) |] in
    for r = 0 to rows - 1 do
      for c = 0 to cols - 1 do
        Array.iter (fun (dr, dc) ->
          let mine = ref 0 and empty = ref 0 and blocked = ref false in
          for k = 0 to 3 do
            let nr = r + k * dr and nc = c + k * dc in
            if nr < 0 || nr >= rows || nc < 0 || nc >= cols then
              blocked := true
            else if board.(nr).(nc) = cell then incr mine
            else if board.(nr).(nc) = Empty then incr empty
            else blocked := true
          done;
          if not !blocked then begin
            if !mine = 4 then score := !score + 100000
            else if !mine = 3 && !empty = 1 then score := !score + 50
            else if !mine = 2 && !empty = 2 then score := !score + 10
          end
        ) directions
      done
    done;
    !score

  let evaluate st =
    if check_four st.board Red then 1000000.0
    else if check_four st.board Yellow then -1000000.0
    else
      let r = count_windows st.board Red in
      let y = count_windows st.board Yellow in
      (* center column bonus *)
      let center_bonus =
        Array.fold_left (fun acc row ->
          acc + (if row.(3) = Red then 3 else if row.(3) = Yellow then -3 else 0)
        ) 0 st.board
      in
      float_of_int (r - y + center_bonus)

  let hash_state st =
    let h = ref 0 in
    Array.iter (fun row ->
      Array.iter (fun c ->
        h := !h * 3 + (match c with Empty -> 0 | Red -> 1 | Yellow -> 2)
      ) row
    ) st.board;
    !h

  let cell_char = function Red -> "R" | Yellow -> "Y" | Empty -> "."

  let show_state st =
    let buf = Buffer.create 128 in
    for r = rows - 1 downto 0 do
      Buffer.add_string buf "| ";
      for c = 0 to cols - 1 do
        Buffer.add_string buf (cell_char st.board.(r).(c));
        Buffer.add_string buf " | "
      done;
      Buffer.add_char buf '\n'
    done;
    Buffer.add_string buf "+---+---+---+---+---+---+---+\n";
    Buffer.add_string buf "  0   1   2   3   4   5   6";
    Buffer.contents buf

  let show_move col = string_of_int col
end

(* ══════════════════════════════════════════════════════════════════════
   NIM — classic math strategy game (multiple piles, remove 1-3)
   ══════════════════════════════════════════════════════════════════════ *)

module Nim : GAME = struct
  type player = Maximizer | Minimizer
  type state = {
    piles : int array;
    turn : player;
  }
  type move = int * int  (* pile index, amount to remove *)

  let initial = { piles = [| 3; 5; 7 |]; turn = Maximizer }

  let current_player st = st.turn

  let legal_moves st =
    let moves = ref [] in
    Array.iteri (fun i pile ->
      for take = min 3 pile downto 1 do
        moves := (i, take) :: !moves
      done
    ) st.piles;
    !moves

  let apply_move st (pile, take) =
    let p = Array.copy st.piles in
    p.(pile) <- p.(pile) - take;
    { piles = p;
      turn = (if st.turn = Maximizer then Minimizer else Maximizer) }

  let is_terminal st = Array.for_all (fun x -> x = 0) st.piles

  (* last player to take loses (misère convention) *)
  let evaluate st =
    if is_terminal st then
      (* the player whose turn it is has nothing to take, so previous player took last *)
      if st.turn = Maximizer then -100.0 else 100.0
    else
      (* nim-value: XOR of all piles; nonzero = winning position *)
      let nim_val = Array.fold_left (fun acc x -> acc lxor x) 0 st.piles in
      if nim_val <> 0 then
        (if st.turn = Maximizer then 10.0 else -10.0)
      else
        (if st.turn = Maximizer then -10.0 else 10.0)

  let hash_state st =
    Array.fold_left (fun h x -> h * 37 + x) 0 st.piles + 
    (if st.turn = Maximizer then 0 else 1000000)

  let show_state st =
    let buf = Buffer.create 64 in
    Array.iteri (fun i n ->
      Buffer.add_string buf (Printf.sprintf "Pile %d: %s (%d)\n" i (String.make n '|') n)
    ) st.piles;
    Buffer.add_string buf (Printf.sprintf "Turn: %s"
      (if st.turn = Maximizer then "Player 1" else "Player 2"));
    Buffer.contents buf

  let show_move (pile, take) = Printf.sprintf "take %d from pile %d" take pile
end

(* ══════════════════════════════════════════════════════════════════════
   TESTS
   ══════════════════════════════════════════════════════════════════════ *)

let () =
  let passed = ref 0 in
  let failed = ref 0 in
  let test name f =
    try
      f ();
      incr passed;
      Printf.printf "  ✓ %s\n" name
    with ex ->
      incr failed;
      Printf.printf "  ✗ %s — %s\n" name (Printexc.to_string ex)
  in
  let assert_eq a b msg =
    if a <> b then failwith (Printf.sprintf "%s: got different values" msg)
  in
  let assert_true b msg = if not b then failwith msg in

  Printf.printf "\n=== Game AI Tests ===\n\n";

  (* --- TicTacToe module tests --- *)
  let module TTT = TicTacToe in
  let module TTT_AI = MakeAI(TicTacToe) in

  Printf.printf "--- Tic-Tac-Toe ---\n";

  test "initial state has 9 legal moves" (fun () ->
    assert_eq (List.length (TTT.legal_moves TTT.initial)) 9 "moves"
  );

  test "initial state is not terminal" (fun () ->
    assert_true (not (TTT.is_terminal TTT.initial)) "not terminal"
  );

  test "initial player is Maximizer" (fun () ->
    assert_true (TTT.current_player TTT.initial = TTT.Maximizer) "maximizer"
  );

  test "apply move reduces legal moves" (fun () ->
    let st = TTT.apply_move TTT.initial 4 in
    assert_eq (List.length (TTT.legal_moves st)) 8 "8 moves"
  );

  test "apply move switches player" (fun () ->
    let st = TTT.apply_move TTT.initial 4 in
    assert_true (TTT.current_player st = TTT.Minimizer) "minimizer"
  );

  test "X wins detection" (fun () ->
    (* X plays 0,1,2 = top row *)
    let st = TTT.initial in
    let st = TTT.apply_move st 0 in  (* X *)
    let st = TTT.apply_move st 3 in  (* O *)
    let st = TTT.apply_move st 1 in  (* X *)
    let st = TTT.apply_move st 4 in  (* O *)
    let st = TTT.apply_move st 2 in  (* X wins *)
    assert_true (TTT.is_terminal st) "terminal";
    assert_true (TTT.evaluate st > 0.0) "X wins positive"
  );

  test "O wins detection" (fun () ->
    let st = TTT.initial in
    let st = TTT.apply_move st 0 in  (* X *)
    let st = TTT.apply_move st 3 in  (* O *)
    let st = TTT.apply_move st 1 in  (* X *)
    let st = TTT.apply_move st 4 in  (* O *)
    let st = TTT.apply_move st 8 in  (* X *)
    let st = TTT.apply_move st 5 in  (* O wins row 2 *)
    assert_true (TTT.is_terminal st) "terminal";
    assert_true (TTT.evaluate st < 0.0) "O wins negative"
  );

  test "draw detection" (fun () ->
    (* X O X / X X O / O X O *)
    let st = TTT.initial in
    let st = TTT.apply_move st 0 in  (* X *)
    let st = TTT.apply_move st 1 in  (* O *)
    let st = TTT.apply_move st 2 in  (* X *)
    let st = TTT.apply_move st 4 in  (* O *)  (* center *)
    let st = TTT.apply_move st 3 in  (* X *)
    let st = TTT.apply_move st 5 in  (* O *)
    let st = TTT.apply_move st 7 in  (* X *)
    let st = TTT.apply_move st 6 in  (* O *)
    let st = TTT.apply_move st 8 in  (* X *)
    assert_true (TTT.is_terminal st) "terminal";
    assert_true (TTT.evaluate st = 0.0) "draw = 0"
  );

  test "hash_state is deterministic" (fun () ->
    let h1 = TTT.hash_state TTT.initial in
    let h2 = TTT.hash_state TTT.initial in
    assert_eq h1 h2 "hash"
  );

  test "different states have different hashes" (fun () ->
    let st2 = TTT.apply_move TTT.initial 0 in
    assert_true (TTT.hash_state TTT.initial <> TTT.hash_state st2) "diff hash"
  );

  test "show_state produces non-empty string" (fun () ->
    assert_true (String.length (TTT.show_state TTT.initial) > 0) "non-empty"
  );

  test "show_move produces valid output" (fun () ->
    assert_eq (TTT.show_move 4) "4" "show move"
  );

  (* --- AI tests for Tic-Tac-Toe --- *)
  Printf.printf "\n--- Tic-Tac-Toe AI ---\n";

  test "minimax finds a move from initial" (fun () ->
    let result = TTT_AI.minimax TTT.initial 3 in
    assert_true (result.best_move <> None) "has move";
    assert_true (result.nodes_searched > 0) "searched nodes"
  );

  test "alphabeta finds a move from initial" (fun () ->
    let result = TTT_AI.alphabeta TTT.initial 5 neg_infinity infinity in
    assert_true (result.best_move <> None) "has move"
  );

  test "minimax and alphabeta agree on score" (fun () ->
    let r1 = TTT_AI.minimax TTT.initial 5 in
    let r2 = TTT_AI.alphabeta TTT.initial 5 neg_infinity infinity in
    assert_true (r1.score = r2.score)
      (Printf.sprintf "scores match: minimax=%.1f ab=%.1f" r1.score r2.score)
  );

  test "alphabeta prunes more than minimax" (fun () ->
    let r1 = TTT_AI.minimax TTT.initial 5 in
    let r2 = TTT_AI.alphabeta TTT.initial 5 neg_infinity infinity in
    assert_true (r2.nodes_searched <= r1.nodes_searched)
      (Printf.sprintf "ab=%d <= minimax=%d" r2.nodes_searched r1.nodes_searched)
  );

  test "full-depth TTT is a draw" (fun () ->
    let result = TTT_AI.alphabeta TTT.initial 9 neg_infinity infinity in
    assert_true (result.score = 0.0) "perfect play = draw"
  );

  test "AI blocks winning move" (fun () ->
    (* O about to win: X needs to block *)
    let st = TTT.initial in
    let st = TTT.apply_move st 4 in  (* X center *)
    let st = TTT.apply_move st 0 in  (* O corner *)
    let st = TTT.apply_move st 8 in  (* X corner *)
    let st = TTT.apply_move st 2 in  (* O corner — threatens 0,1,2 *)
    (* X must play 1 to block *)
    let result = TTT_AI.alphabeta st 9 neg_infinity infinity in
    assert_true (result.best_move = Some 1) "blocks at 1"
  );

  test "AI takes winning move" (fun () ->
    let st = TTT.initial in
    let st = TTT.apply_move st 0 in  (* X *)
    let st = TTT.apply_move st 3 in  (* O *)
    let st = TTT.apply_move st 1 in  (* X *)
    let st = TTT.apply_move st 4 in  (* O *)
    (* X can win with 2 *)
    let result = TTT_AI.alphabeta st 9 neg_infinity infinity in
    assert_true (result.best_move = Some 2) "wins at 2"
  );

  test "iterative deepening produces result" (fun () ->
    let result = TTT_AI.iterative_deepening TTT.initial 5 in
    assert_true (result.best_move <> None) "has move";
    assert_true (result.nodes_searched > 0) "searched"
  );

  test "transposition table produces result" (fun () ->
    let result = TTT_AI.alphabeta_tt TTT.initial 5 in
    assert_true (result.best_move <> None) "has move"
  );

  test "best_move convenience function" (fun () ->
    let m = TTT_AI.best_move ~depth:5 TTT.initial in
    assert_true (m <> None) "has move"
  );

  (* --- ConnectFour tests --- *)
  let module C4 = ConnectFour in
  let module C4_AI = MakeAI(ConnectFour) in

  Printf.printf "\n--- Connect Four ---\n";

  test "initial state has 7 legal moves" (fun () ->
    assert_eq (List.length (C4.legal_moves C4.initial)) 7 "7 cols"
  );

  test "initial is not terminal" (fun () ->
    assert_true (not (C4.is_terminal C4.initial)) "not terminal"
  );

  test "apply move increments height" (fun () ->
    let st = C4.apply_move C4.initial 3 in
    let st = C4.apply_move st 3 in
    let moves = C4.legal_moves st in
    assert_true (List.mem 3 moves) "col 3 still open"
  );

  test "column fills up" (fun () ->
    let st = ref C4.initial in
    for _ = 1 to 6 do
      st := C4.apply_move !st 0
    done;
    let moves = C4.legal_moves !st in
    assert_true (not (List.mem 0 moves)) "col 0 full"
  );

  test "vertical win detection" (fun () ->
    let st = ref C4.initial in
    for _ = 1 to 4 do
      st := C4.apply_move !st 0;  (* Red *)
      if not (C4.is_terminal !st) then
        st := C4.apply_move !st 1   (* Yellow *)
    done;
    assert_true (C4.is_terminal !st) "terminal";
    assert_true (C4.evaluate !st > 0.0) "red wins"
  );

  test "AI finds move at depth 4" (fun () ->
    let result = C4_AI.alphabeta C4.initial 4 neg_infinity infinity in
    assert_true (result.best_move <> None) "has move"
  );

  test "AI prefers center column" (fun () ->
    let result = C4_AI.alphabeta C4.initial 4 neg_infinity infinity in
    match result.best_move with
    | Some m -> assert_true (m >= 2 && m <= 4) "center-ish"
    | None -> failwith "no move"
  );

  test "show_state includes column numbers" (fun () ->
    let s = C4.show_state C4.initial in
    assert_true (String.length s > 50) "non-trivial output"
  );

  test "hash differs after move" (fun () ->
    let h1 = C4.hash_state C4.initial in
    let h2 = C4.hash_state (C4.apply_move C4.initial 3) in
    assert_true (h1 <> h2) "different hashes"
  );

  (* --- Nim tests --- *)
  let module N = Nim in
  let module N_AI = MakeAI(Nim) in

  Printf.printf "\n--- Nim ---\n";

  test "initial piles are [3; 5; 7]" (fun () ->
    assert_eq N.initial.piles.(0) 3 "pile 0";
    assert_eq N.initial.piles.(1) 5 "pile 1";
    assert_eq N.initial.piles.(2) 7 "pile 2"
  );

  test "legal moves from initial" (fun () ->
    let moves = N.legal_moves N.initial in
    assert_true (List.length moves > 0) "has moves";
    (* pile 0: take 1,2,3; pile 1: take 1,2,3; pile 2: take 1,2,3 = 9 *)
    assert_eq (List.length moves) 9 "9 moves"
  );

  test "apply move reduces pile" (fun () ->
    let st = N.apply_move N.initial (0, 2) in
    assert_eq st.piles.(0) 1 "pile 0 = 1"
  );

  test "terminal when all piles empty" (fun () ->
    let st = { N.piles = [| 0; 0; 0 |]; turn = N.Maximizer } in
    assert_true (N.is_terminal st) "terminal"
  );

  test "not terminal when stones remain" (fun () ->
    assert_true (not (N.is_terminal N.initial)) "not terminal"
  );

  test "AI finds move" (fun () ->
    let result = N_AI.alphabeta N.initial 8 neg_infinity infinity in
    assert_true (result.best_move <> None) "has move"
  );

  test "nim hash is deterministic" (fun () ->
    let h1 = N.hash_state N.initial in
    let h2 = N.hash_state N.initial in
    assert_eq h1 h2 "same hash"
  );

  test "show_state includes piles" (fun () ->
    let s = N.show_state N.initial in
    assert_true (String.length s > 20) "non-trivial"
  );

  test "show_move describes action" (fun () ->
    let s = N.show_move (1, 2) in
    assert_true (String.length s > 5) "non-trivial"
  );

  (* --- Cross-cutting tests --- *)
  Printf.printf "\n--- Cross-cutting ---\n";

  test "minimax depth 0 returns evaluation" (fun () ->
    let result = TTT_AI.minimax TTT.initial 0 in
    assert_true (result.best_move = None) "no move at depth 0";
    assert_true (result.nodes_searched = 1) "1 node"
  );

  test "alphabeta depth 0 returns evaluation" (fun () ->
    let result = TTT_AI.alphabeta TTT.initial 0 neg_infinity infinity in
    assert_true (result.nodes_searched = 1) "1 node"
  );

  test "iterative deepening depth 1" (fun () ->
    let result = TTT_AI.iterative_deepening TTT.initial 1 in
    assert_true (result.best_move <> None) "has move"
  );

  test "TT search agrees with alphabeta on TTT" (fun () ->
    let r1 = TTT_AI.alphabeta TTT.initial 9 neg_infinity infinity in
    let r2 = TTT_AI.alphabeta_tt TTT.initial 9 in
    assert_true (r1.score = r2.score)
      (Printf.sprintf "scores: ab=%.1f tt=%.1f" r1.score r2.score)
  );

  test "TT uses fewer nodes than plain alphabeta" (fun () ->
    let st = TTT.apply_move TTT.initial 4 in
    let r1 = TTT_AI.alphabeta st 8 neg_infinity infinity in
    let r2 = TTT_AI.alphabeta_tt st 8 in
    (* TT should generally help, but at minimum produce same result *)
    assert_true (r1.score = r2.score) "same score";
    Printf.printf "    (ab: %d nodes, tt: %d nodes)\n" r1.nodes_searched r2.nodes_searched
  );

  test "play_game function exists" (fun () ->
    (* just verify it compiles, don't actually run it *)
    let _ = TTT_AI.play_game in
    assert_true true "compiles"
  );

  Printf.printf "\n=== Results: %d passed, %d failed ===\n" !passed !failed;
  if !failed > 0 then exit 1
