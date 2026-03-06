(* diff.ml — Myers Diff Algorithm
 *
 * Implementation of Eugene Myers' "An O(ND) Difference Algorithm and Its
 * Variations" (1986) — the same algorithm used by git diff and GNU diff.
 *
 * Concepts demonstrated:
 * - Dynamic programming on the edit graph
 * - Shortest edit script (SES) computation
 * - Longest common subsequence (LCS) extraction
 * - Unified diff output formatting
 * - Patch application and reversal
 * - Line-level and word-level diffing
 * - Three-way merge with conflict detection
 *
 * Complexity: O(ND) time and space where N = m+n and D = edit distance
 *)

(* ── Edit operations ────────────────────────────────────────────────── *)

type 'a edit =
  | Equal of 'a   (** Element present in both sequences *)
  | Insert of 'a  (** Element added (present only in new) *)
  | Delete of 'a  (** Element removed (present only in old) *)

type 'a hunk = {
  old_start : int;   (** 1-based line number in old *)
  old_count : int;
  new_start : int;   (** 1-based line number in new *)
  new_count : int;
  edits     : 'a edit list;
}

type 'a diff_result = {
  edits     : 'a edit list;
  lcs       : 'a list;          (** Longest common subsequence *)
  distance  : int;              (** Edit distance (inserts + deletes) *)
  hunks     : 'a hunk list;     (** Grouped change hunks *)
  similarity: float;            (** 0.0–1.0 similarity ratio *)
}

(* ── Merge types ────────────────────────────────────────────────────── *)

type 'a merge_chunk =
  | Resolved of 'a list
  | Conflict of { base: 'a list; ours: 'a list; theirs: 'a list }

type 'a merge_result = {
  chunks       : 'a merge_chunk list;
  merged       : 'a list option;    (** None if conflicts exist *)
  conflict_count: int;
}

(* ── Patch types ────────────────────────────────────────────────────── *)

type 'a patch = {
  old_name : string;
  new_name : string;
  hunks    : 'a hunk list;
}

(* ── Myers core algorithm ───────────────────────────────────────────── *)

(** Compute shortest edit script using Myers' O(ND) algorithm. *)
let myers_diff ?(equal = (=)) (a : 'a array) (b : 'a array) : 'a edit list =
  let n = Array.length a in
  let m = Array.length b in
  if n = 0 && m = 0 then []
  else if n = 0 then Array.to_list b |> List.map (fun x -> Insert x)
  else if m = 0 then Array.to_list a |> List.map (fun x -> Delete x)
  else begin
    let max_d = n + m in
    (* v.(k + max_d) = furthest reaching x on diagonal k *)
    let v_size = 2 * max_d + 1 in
    let trace = Array.make 0 [||] in
    let trace_list = ref [] in

    let v = Array.make v_size 0 in
    let found = ref false in
    let final_d = ref 0 in

    let d = ref 0 in
    while !d <= max_d && not !found do
      trace_list := Array.copy v :: !trace_list;
      let dd = !d in
      let k = ref (-dd) in
      while !k <= dd && not !found do
        let kk = !k in
        let x =
          if kk = -dd || (kk <> dd && v.(kk - 1 + max_d) < v.(kk + 1 + max_d))
          then v.(kk + 1 + max_d)
          else v.(kk - 1 + max_d) + 1
        in
        let x = ref x in
        let y = ref (!x - kk) in
        while !x < n && !y < m && equal a.(!x) b.(!y) do
          incr x; incr y
        done;
        v.(kk + max_d) <- !x;
        if !x >= n && !y >= m then begin
          found := true;
          final_d := dd
        end;
        k := !k + 2
      done;
      d := !d + 1
    done;

    (* Backtrack to recover the edit script *)
    let trace_arr = Array.of_list (List.rev !trace_list) in
    ignore trace;
    let edits = ref [] in
    let x = ref n in
    let y = ref m in

    for d = !final_d downto 1 do
      let v_prev = trace_arr.(d - 1) in
      let k = !x - !y in
      let prev_k =
        if k = -d || (k <> d && v_prev.(k - 1 + max_d) < v_prev.(k + 1 + max_d))
        then k + 1
        else k - 1
      in
      let prev_x = v_prev.(prev_k + max_d) in
      let prev_y = prev_x - prev_k in

      (* Diagonal moves (equals) *)
      while !x > prev_x + (if prev_k < k then 1 else 0)
            && !y > prev_y + (if prev_k > k then 1 else 0) do
        decr x; decr y;
        edits := Equal a.(!x) :: !edits
      done;

      (* The actual edit *)
      if d > 0 then begin
        if prev_k < k then begin
          (* Move right = delete from a *)
          decr x;
          edits := Delete a.(!x) :: !edits
        end else begin
          (* Move down = insert from b *)
          decr y;
          edits := Insert b.(!y) :: !edits
        end
      end
    done;

    (* Remaining diagonal *)
    while !x > 0 && !y > 0 do
      decr x; decr y;
      edits := Equal a.(!x) :: !edits
    done;
    while !x > 0 do
      decr x;
      edits := Delete a.(!x) :: !edits
    done;
    while !y > 0 do
      decr y;
      edits := Insert b.(!y) :: !edits
    done;

    !edits
  end

(* ── Extract LCS from edit script ───────────────────────────────────── *)

let lcs_of_edits edits =
  List.filter_map (function Equal x -> Some x | _ -> None) edits

(* ── Edit distance ──────────────────────────────────────────────────── *)

let edit_distance edits =
  List.fold_left (fun acc e ->
    match e with Equal _ -> acc | Insert _ | Delete _ -> acc + 1
  ) 0 edits

(* ── Similarity ratio ──────────────────────────────────────────────── *)

let similarity (a : 'a array) (b : 'a array) edits =
  let total = Array.length a + Array.length b in
  if total = 0 then 1.0
  else
    let lcs_len = List.length (lcs_of_edits edits) in
    (2.0 *. float_of_int lcs_len) /. float_of_int total

(* ── Hunk grouping ──────────────────────────────────────────────────── *)

(** Group edits into hunks with context lines. *)
let group_hunks ?(context = 3) edits =
  (* Assign line numbers *)
  let indexed =
    let old_line = ref 1 and new_line = ref 1 in
    List.map (fun e ->
      let ol = !old_line and nl = !new_line in
      (match e with
       | Equal _ -> incr old_line; incr new_line
       | Delete _ -> incr old_line
       | Insert _ -> incr new_line);
      (ol, nl, e)
    ) edits
  in
  (* Find change positions *)
  let changes =
    List.mapi (fun i (_, _, e) ->
      match e with Equal _ -> None | _ -> Some i
    ) indexed
    |> List.filter_map Fun.id
  in
  if changes = [] then []
  else begin
    let arr = Array.of_list indexed in
    let n = Array.length arr in

    (* Group nearby changes *)
    let groups = ref [] in
    let cur_start = ref (List.hd changes) in
    let cur_end = ref !cur_start in
    List.iter (fun ci ->
      if ci - !cur_end > 2 * context then begin
        groups := (!cur_start, !cur_end) :: !groups;
        cur_start := ci;
      end;
      cur_end := ci
    ) changes;
    groups := (!cur_start, !cur_end) :: !groups;
    let groups = List.rev !groups in

    List.map (fun (gs, ge) ->
      let lo = max 0 (gs - context) in
      let hi = min (n - 1) (ge + context) in
      let edits_slice = ref [] in
      for i = hi downto lo do
        let (_, _, e) = arr.(i) in
        edits_slice := e :: !edits_slice
      done;
      let (os, ns, _) = arr.(lo) in
      let old_count = ref 0 and new_count = ref 0 in
      List.iter (fun e ->
        match e with
        | Equal _ -> incr old_count; incr new_count
        | Delete _ -> incr old_count
        | Insert _ -> incr new_count
      ) !edits_slice;
      { old_start = os; old_count = !old_count;
        new_start = ns; new_count = !new_count;
        edits = !edits_slice }
    ) groups
  end

(* ── Full diff ──────────────────────────────────────────────────────── *)

let diff ?(equal = (=)) ?(context = 3) (a : 'a array) (b : 'a array) : 'a diff_result =
  let edits = myers_diff ~equal a b in
  { edits;
    lcs = lcs_of_edits edits;
    distance = edit_distance edits;
    hunks = group_hunks ~context edits;
    similarity = similarity a b edits }

(* ── String/line diffing helpers ────────────────────────────────────── *)

let split_lines s =
  if s = "" then [||]
  else
    let lines = ref [] in
    let buf = Buffer.create 80 in
    String.iter (fun c ->
      if c = '\n' then begin
        lines := Buffer.contents buf :: !lines;
        Buffer.clear buf
      end else
        Buffer.add_char buf c
    ) s;
    if Buffer.length buf > 0 then
      lines := Buffer.contents buf :: !lines;
    Array.of_list (List.rev !lines)

let diff_lines ?(context = 3) (old_text : string) (new_text : string) =
  diff ~context (split_lines old_text) (split_lines new_text)

let diff_words (old_text : string) (new_text : string) =
  let split_words s =
    let words = ref [] in
    let buf = Buffer.create 16 in
    String.iter (fun c ->
      if c = ' ' || c = '\t' || c = '\n' then begin
        if Buffer.length buf > 0 then begin
          words := Buffer.contents buf :: !words;
          Buffer.clear buf
        end;
        words := String.make 1 c :: !words
      end else
        Buffer.add_char buf c
    ) s;
    if Buffer.length buf > 0 then
      words := Buffer.contents buf :: !words;
    Array.of_list (List.rev !words)
  in
  diff (split_words old_text) (split_words new_text)

let diff_chars (old_text : string) (new_text : string) =
  let to_arr s = Array.init (String.length s) (fun i -> s.[i]) in
  let r = diff (to_arr old_text) (to_arr new_text) in
  { edits = List.map (function
      | Equal c -> Equal (String.make 1 c)
      | Insert c -> Insert (String.make 1 c)
      | Delete c -> Delete (String.make 1 c)
    ) r.edits;
    lcs = List.map (String.make 1) r.lcs;
    distance = r.distance;
    hunks = [];
    similarity = r.similarity }

(* ── Unified diff format ────────────────────────────────────────────── *)

let format_unified ?(old_name = "a") ?(new_name = "b") (result : string diff_result) =
  let buf = Buffer.create 256 in
  Buffer.add_string buf (Printf.sprintf "--- %s\n" old_name);
  Buffer.add_string buf (Printf.sprintf "+++ %s\n" new_name);
  List.iter (fun hunk ->
    Buffer.add_string buf (Printf.sprintf "@@ -%d,%d +%d,%d @@\n"
      hunk.old_start hunk.old_count hunk.new_start hunk.new_count);
    List.iter (fun e ->
      match e with
      | Equal s  -> Buffer.add_string buf (Printf.sprintf " %s\n" s)
      | Delete s -> Buffer.add_string buf (Printf.sprintf "-%s\n" s)
      | Insert s -> Buffer.add_string buf (Printf.sprintf "+%s\n" s)
    ) hunk.edits
  ) result.hunks;
  Buffer.contents buf

(* ── Side-by-side format ────────────────────────────────────────────── *)

let format_side_by_side ?(width = 80) (result : string diff_result) =
  let half = (width - 3) / 2 in
  let buf = Buffer.create 256 in
  let pad s w =
    let len = String.length s in
    if len >= w then String.sub s 0 w
    else s ^ String.make (w - len) ' '
  in
  let sep = String.make width '-' in
  Buffer.add_string buf (sep ^ "\n");
  List.iter (fun e ->
    match e with
    | Equal s ->
      Buffer.add_string buf (Printf.sprintf "%s | %s\n" (pad s half) (pad s half))
    | Delete s ->
      Buffer.add_string buf (Printf.sprintf "%s < %s\n" (pad s half) (pad "" half))
    | Insert s ->
      Buffer.add_string buf (Printf.sprintf "%s > %s\n" (pad "" half) (pad s half))
  ) result.edits;
  Buffer.add_string buf (sep ^ "\n");
  Buffer.contents buf

(* ── Inline colored format (ANSI) ──────────────────────────────────── *)

let format_inline_colored (result : string diff_result) =
  let buf = Buffer.create 256 in
  List.iter (fun e ->
    match e with
    | Equal s  -> Buffer.add_string buf (Printf.sprintf " %s\n" s)
    | Delete s -> Buffer.add_string buf (Printf.sprintf "\027[31m-%s\027[0m\n" s)
    | Insert s -> Buffer.add_string buf (Printf.sprintf "\027[32m+%s\027[0m\n" s)
  ) result.edits;
  Buffer.contents buf

(* ── Patch application ──────────────────────────────────────────────── *)

(** Apply a diff to transform old into new *)
let apply_patch (old_arr : 'a array) (edits : 'a edit list) : 'a array =
  let result = ref [] in
  List.iter (fun e ->
    match e with
    | Equal x  -> result := x :: !result
    | Insert x -> result := x :: !result
    | Delete _ -> ()
  ) edits;
  Array.of_list (List.rev !result)

(** Reverse a diff (swap insert/delete) *)
let reverse_edits edits =
  List.map (function
    | Equal x  -> Equal x
    | Insert x -> Delete x
    | Delete x -> Insert x
  ) edits

(** Apply reversed patch to go from new back to old *)
let reverse_patch (new_arr : 'a array) (edits : 'a edit list) : 'a array =
  apply_patch new_arr (reverse_edits edits)

(* ── Edit script statistics ─────────────────────────────────────────── *)

type edit_stats = {
  equal_count  : int;
  insert_count : int;
  delete_count : int;
  total_edits  : int;
  change_ratio : float;  (** Fraction of elements changed *)
}

let compute_stats edits =
  let eq = ref 0 and ins = ref 0 and del = ref 0 in
  List.iter (function
    | Equal _  -> incr eq
    | Insert _ -> incr ins
    | Delete _ -> incr del
  ) edits;
  let total = !eq + !ins + !del in
  { equal_count = !eq;
    insert_count = !ins;
    delete_count = !del;
    total_edits = !ins + !del;
    change_ratio = if total = 0 then 0.0
      else float_of_int (!ins + !del) /. float_of_int total }

(* ── Three-way merge ────────────────────────────────────────────────── *)

(** Three-way merge: given a common base, merge "ours" and "theirs" changes.
    Produces conflict markers when both sides change the same region. *)
let merge3 ?(equal = (=)) (base : 'a array) (ours : 'a array) (theirs : 'a array)
    : 'a merge_result =
  let edits_ours = myers_diff ~equal base ours in
  let edits_theirs = myers_diff ~equal base theirs in

  (* Convert edits to indexed changes relative to base *)
  let changes_of edits =
    let idx = ref 0 in
    let changes = ref [] in
    List.iter (fun e ->
      match e with
      | Equal _ -> incr idx
      | Delete _ -> changes := (`Del, !idx) :: !changes; incr idx
      | Insert x -> changes := (`Ins x, !idx) :: !changes
    ) edits;
    List.rev !changes
  in

  let ours_changes = changes_of edits_ours in
  let theirs_changes = changes_of edits_theirs in

  (* Check if same base index is modified by both *)
  let ours_dels =
    List.filter_map (fun (op, i) ->
      match op with `Del -> Some i | _ -> None) ours_changes
    |> List.sort_uniq compare
  in
  let theirs_dels =
    List.filter_map (fun (op, i) ->
      match op with `Del -> Some i | _ -> None) theirs_changes
    |> List.sort_uniq compare
  in

  (* Simple merge: if no overlapping deletions, merge cleanly *)
  let overlap = List.filter (fun i -> List.mem i theirs_dels) ours_dels in

  if overlap = [] then begin
    (* Clean merge: apply both sets of changes *)
    let merged_ours = apply_patch base edits_ours in
    let merged_theirs_edits = myers_diff ~equal base theirs in
    (* Apply theirs changes to ours result *)
    let final_edits = myers_diff ~equal merged_ours
        (apply_patch base merged_theirs_edits) in
    let final = apply_patch merged_ours final_edits in
    { chunks = [Resolved (Array.to_list final)];
      merged = Some (Array.to_list final);
      conflict_count = 0 }
  end else begin
    (* Has conflicts — produce chunks *)
    let base_list = Array.to_list base in
    let ours_list = Array.to_list ours in
    let theirs_list = Array.to_list theirs in
    { chunks = [Conflict { base = base_list;
                           ours = ours_list;
                           theirs = theirs_list }];
      merged = None;
      conflict_count = 1 }
  end

(* ── Diff summary / report ──────────────────────────────────────────── *)

let format_summary (result : string diff_result) =
  let stats = compute_stats result.edits in
  Printf.sprintf
    "Diff Summary:\n\
     - Lines compared: %d old, %d new\n\
     - Equal lines: %d\n\
     - Insertions: %d\n\
     - Deletions: %d\n\
     - Edit distance: %d\n\
     - Similarity: %.1f%%\n\
     - Hunks: %d\n"
    (stats.equal_count + stats.delete_count)
    (stats.equal_count + stats.insert_count)
    stats.equal_count
    stats.insert_count
    stats.delete_count
    result.distance
    (result.similarity *. 100.0)
    (List.length result.hunks)

(* ── Semantic diff helpers ──────────────────────────────────────────── *)

(** Patience diff: find unique matching lines first for better alignment *)
let patience_anchors (a : string array) (b : string array) =
  (* Find lines unique in both sequences *)
  let count arr =
    let tbl = Hashtbl.create 16 in
    Array.iteri (fun i s ->
      let cur = try Hashtbl.find tbl s with Not_found -> [] in
      Hashtbl.replace tbl s (i :: cur)
    ) arr;
    tbl
  in
  let ca = count a and cb = count b in
  let anchors = ref [] in
  Hashtbl.iter (fun s indices_a ->
    if List.length indices_a = 1 then
      match Hashtbl.find_opt cb s with
      | Some [ib] -> anchors := (List.hd indices_a, ib, s) :: !anchors
      | _ -> ()
  ) ca;
  (* Sort by position in a *)
  List.sort (fun (ia, _, _) (ib, _, _) -> compare ia ib) !anchors

(** Find longest increasing subsequence of anchors (by b-index) *)
let lis_anchors anchors =
  if anchors = [] then []
  else begin
    let arr = Array.of_list anchors in
    let n = Array.length arr in
    let tails = Array.make n 0 in
    let preds = Array.make n (-1) in
    let len = ref 0 in
    for i = 0 to n - 1 do
      let (_, bi, _) = arr.(i) in
      (* Binary search for position *)
      let lo = ref 0 and hi = ref !len in
      while !lo < !hi do
        let mid = (!lo + !hi) / 2 in
        let (_, bm, _) = arr.(tails.(mid)) in
        if bm < bi then lo := mid + 1
        else hi := mid
      done;
      tails.(!lo) <- i;
      preds.(i) <- if !lo > 0 then tails.(!lo - 1) else -1;
      if !lo + 1 > !len then len := !lo + 1
    done;
    (* Reconstruct *)
    let result = ref [] in
    let k = ref tails.(!len - 1) in
    while !k >= 0 do
      result := arr.(!k) :: !result;
      k := preds.(!k)
    done;
    !result
  end

(** Patience diff: use unique-line anchors for better alignment, then
    fill gaps with standard Myers diff. *)
let patience_diff ?(context = 3) (a : string array) (b : string array) : string diff_result =
  let anchors = patience_anchors a b in
  let lis = lis_anchors anchors in
  if lis = [] then
    diff ~context a b
  else begin
    (* Build edit script using anchors as fixed equal points *)
    let edits = ref [] in
    let ai = ref 0 and bi = ref 0 in
    List.iter (fun (ia, ib, _s) ->
      (* Diff the gap before this anchor *)
      if !ai < ia || !bi < ib then begin
        let sub_a = Array.sub a !ai (ia - !ai) in
        let sub_b = Array.sub b !bi (ib - !bi) in
        let sub_edits = myers_diff sub_a sub_b in
        edits := List.rev_append sub_edits !edits
      end;
      edits := Equal a.(ia) :: !edits;
      ai := ia + 1;
      bi := ib + 1
    ) lis;
    (* Diff remaining tail *)
    let tail_a = Array.sub a !ai (Array.length a - !ai) in
    let tail_b = Array.sub b !bi (Array.length b - !bi) in
    let tail_edits = myers_diff tail_a tail_b in
    edits := List.rev_append tail_edits !edits;
    let edits = List.rev !edits in
    { edits;
      lcs = lcs_of_edits edits;
      distance = edit_distance edits;
      hunks = group_hunks ~context edits;
      similarity = similarity a b edits }
  end

(* ════════════════════════════════════════════════════════════════════ *)
(*  TESTS                                                              *)
(* ════════════════════════════════════════════════════════════════════ *)

let () =
  let passed = ref 0 and failed = ref 0 in
  let test name f =
    try f (); incr passed; Printf.printf "  ✓ %s\n" name
    with e ->
      incr failed;
      Printf.printf "  ✗ %s: %s\n" name (Printexc.to_string e)
  in
  let assert_eq a b =
    if a <> b then failwith (Printf.sprintf "expected equal") in
  let assert_true b = if not b then failwith "expected true" in

  Printf.printf "\n═══ Diff Algorithm Tests ═══\n\n";

  (* ── Basic Myers diff ── *)
  Printf.printf "── Basic Myers Diff ──\n";

  test "empty sequences" (fun () ->
    let r = diff [||] [||] in
    assert_eq r.edits [];
    assert_eq r.distance 0;
    assert_true (r.similarity = 1.0)
  );

  test "identical sequences" (fun () ->
    let r = diff [|1;2;3|] [|1;2;3|] in
    assert_eq r.distance 0;
    assert_true (r.similarity = 1.0);
    assert_eq r.lcs [1;2;3]
  );

  test "all inserts" (fun () ->
    let r = diff [||] [|1;2;3|] in
    assert_eq r.distance 3;
    assert_eq r.edits [Insert 1; Insert 2; Insert 3]
  );

  test "all deletes" (fun () ->
    let r = diff [|1;2;3|] [||] in
    assert_eq r.distance 3;
    assert_eq r.edits [Delete 1; Delete 2; Delete 3]
  );

  test "single insert" (fun () ->
    let r = diff [|1;3|] [|1;2;3|] in
    assert_eq r.distance 1;
    assert_eq r.lcs [1;3]
  );

  test "single delete" (fun () ->
    let r = diff [|1;2;3|] [|1;3|] in
    assert_eq r.distance 1;
    assert_eq r.lcs [1;3]
  );

  test "substitution" (fun () ->
    let r = diff [|1;2;3|] [|1;4;3|] in
    assert_eq r.distance 2; (* delete 2 + insert 4 *)
    assert_eq r.lcs [1;3]
  );

  test "complete replacement" (fun () ->
    let r = diff [|1;2|] [|3;4|] in
    assert_eq r.distance 4
  );

  test "interleaved changes" (fun () ->
    let r = diff [|1;2;3;4;5|] [|1;3;5|] in
    assert_eq r.distance 2;
    assert_eq r.lcs [1;3;5]
  );

  test "prefix change" (fun () ->
    let r = diff [|0;1;2|] [|9;1;2|] in
    assert_eq r.distance 2;
    assert_eq r.lcs [1;2]
  );

  test "suffix change" (fun () ->
    let r = diff [|1;2;0|] [|1;2;9|] in
    assert_eq r.distance 2;
    assert_eq r.lcs [1;2]
  );

  (* ── LCS ── *)
  Printf.printf "── LCS Extraction ──\n";

  test "lcs classic" (fun () ->
    let r = diff [|1;2;3;4;5|] [|2;4;5;6|] in
    assert_eq r.lcs [2;4;5]
  );

  test "lcs empty when disjoint" (fun () ->
    let r = diff [|1;2|] [|3;4|] in
    assert_eq r.lcs []
  );

  test "lcs single element" (fun () ->
    let r = diff [|5|] [|5|] in
    assert_eq r.lcs [5]
  );

  (* ── Similarity ── *)
  Printf.printf "── Similarity Ratio ──\n";

  test "identical similarity is 1.0" (fun () ->
    let r = diff [|"a";"b";"c"|] [|"a";"b";"c"|] in
    assert_true (r.similarity = 1.0)
  );

  test "disjoint similarity is 0.0" (fun () ->
    let r = diff [|"a"|] [|"b"|] in
    assert_true (r.similarity = 0.0)
  );

  test "half similar" (fun () ->
    let r = diff [|"a";"b"|] [|"a";"c"|] in
    assert_true (r.similarity = 0.5)
  );

  (* ── Edit stats ── *)
  Printf.printf "── Edit Statistics ──\n";

  test "stats counts" (fun () ->
    let r = diff [|1;2;3|] [|1;4;3;5|] in
    let s = compute_stats r.edits in
    assert_eq s.equal_count 2;
    assert_eq s.delete_count 1;
    assert_eq s.insert_count 2;
    assert_eq s.total_edits 3
  );

  test "stats zero edits" (fun () ->
    let s = compute_stats [Equal 1; Equal 2] in
    assert_eq s.total_edits 0;
    assert_true (s.change_ratio = 0.0)
  );

  (* ── Line diffing ── *)
  Printf.printf "── Line Diffing ──\n";

  test "diff_lines simple" (fun () ->
    let r = diff_lines "foo\nbar\nbaz" "foo\nqux\nbaz" in
    assert_eq r.distance 2;
    assert_eq r.lcs ["foo"; "baz"]
  );

  test "diff_lines empty old" (fun () ->
    let r = diff_lines "" "hello\nworld" in
    assert_eq r.distance 2
  );

  test "diff_lines empty new" (fun () ->
    let r = diff_lines "hello" "" in
    assert_eq r.distance 1
  );

  test "diff_lines multiline insert" (fun () ->
    let r = diff_lines "a\nb" "a\nx\ny\nb" in
    assert_eq r.distance 2
  );

  (* ── Character diffing ── *)
  Printf.printf "── Character Diffing ──\n";

  test "diff_chars simple" (fun () ->
    let r = diff_chars "abc" "adc" in
    assert_eq r.distance 2
  );

  test "diff_chars empty" (fun () ->
    let r = diff_chars "" "abc" in
    assert_eq r.distance 3
  );

  test "diff_chars identical" (fun () ->
    let r = diff_chars "hello" "hello" in
    assert_eq r.distance 0
  );

  (* ── Word diffing ── *)
  Printf.printf "── Word Diffing ──\n";

  test "diff_words simple" (fun () ->
    let r = diff_words "the cat sat" "the dog sat" in
    assert_eq r.distance 2 (* delete "cat", insert "dog" *)
  );

  test "diff_words identical" (fun () ->
    let r = diff_words "hello world" "hello world" in
    assert_eq r.distance 0
  );

  (* ── Hunk grouping ── *)
  Printf.printf "── Hunk Grouping ──\n";

  test "no hunks when identical" (fun () ->
    let r = diff [|1;2;3|] [|1;2;3|] in
    assert_eq r.hunks []
  );

  test "single hunk for small diff" (fun () ->
    let r = diff ~context:1 [|1;2;3|] [|1;4;3|] in
    assert_true (List.length r.hunks = 1)
  );

  test "hunk line numbers" (fun () ->
    let r = diff_lines ~context:0 "a\nb\nc" "a\nx\nc" in
    match r.hunks with
    | [h] ->
      assert_eq h.old_start 2;
      assert_eq h.new_start 2
    | _ -> failwith "expected 1 hunk"
  );

  test "multiple hunks for distant changes" (fun () ->
    let a = Array.init 20 (fun i -> i) in
    let b = Array.copy a in
    b.(2) <- 99;
    b.(17) <- 99;
    let r = diff ~context:1 a b in
    assert_true (List.length r.hunks >= 2)
  );

  (* ── Unified format ── *)
  Printf.printf "── Unified Format ──\n";

  test "unified format header" (fun () ->
    let r = diff_lines "a\nb" "a\nc" in
    let s = format_unified ~old_name:"old.txt" ~new_name:"new.txt" r in
    assert_true (String.length s > 0);
    assert_true (let i = ref false in
      String.iter (fun c -> if c = '-' then i := true) s; !i)
  );

  test "unified format empty diff" (fun () ->
    let r = diff_lines "same" "same" in
    let s = format_unified r in
    assert_eq s "--- a\n+++ b\n"
  );

  (* ── Side-by-side format ── *)
  Printf.printf "── Side-by-side Format ──\n";

  test "side by side output" (fun () ->
    let r = diff_lines "old line" "new line" in
    let s = format_side_by_side ~width:60 r in
    assert_true (String.length s > 0)
  );

  (* ── Inline colored format ── *)
  Printf.printf "── Inline Colored ──\n";

  test "inline colored has ANSI codes" (fun () ->
    let r = diff_lines "old" "new" in
    let s = format_inline_colored r in
    assert_true (String.contains s '\027')
  );

  (* ── Patch application ── *)
  Printf.printf "── Patch Application ──\n";

  test "apply patch reconstructs new" (fun () ->
    let a = [|"a";"b";"c"|] in
    let b = [|"a";"x";"c";"d"|] in
    let r = diff a b in
    let result = apply_patch a r.edits in
    assert_eq (Array.to_list result) (Array.to_list b)
  );

  test "apply empty patch" (fun () ->
    let a = [|1;2;3|] in
    let r = diff a a in
    let result = apply_patch a r.edits in
    assert_eq (Array.to_list result) [1;2;3]
  );

  test "reverse patch reconstructs old" (fun () ->
    let a = [|"x";"y";"z"|] in
    let b = [|"x";"w";"z"|] in
    let r = diff a b in
    let result = reverse_patch b r.edits in
    assert_eq (Array.to_list result) (Array.to_list a)
  );

  test "patch roundtrip" (fun () ->
    let a = [|1;2;3;4;5|] in
    let b = [|1;3;6;5;7|] in
    let r = diff a b in
    let forward = apply_patch a r.edits in
    let backward = reverse_patch forward r.edits in
    assert_eq (Array.to_list forward) (Array.to_list b);
    assert_eq (Array.to_list backward) (Array.to_list a)
  );

  (* ── Edit reversal ── *)
  Printf.printf "── Edit Reversal ──\n";

  test "reverse edits swaps insert/delete" (fun () ->
    let edits = [Equal 1; Insert 2; Delete 3] in
    let rev = reverse_edits edits in
    assert_eq rev [Equal 1; Delete 2; Insert 3]
  );

  (* ── Custom equality ── *)
  Printf.printf "── Custom Equality ──\n";

  test "case-insensitive diff" (fun () ->
    let eq a b = String.lowercase_ascii a = String.lowercase_ascii b in
    let r = diff ~equal:eq [|"Hello";"World"|] [|"hello";"world"|] in
    assert_eq r.distance 0
  );

  test "custom equality with threshold" (fun () ->
    let eq a b = abs (a - b) <= 1 in
    let r = diff ~equal:eq [|1;5;10|] [|2;5;11|] in
    assert_eq r.distance 0
  );

  (* ── Three-way merge ── *)
  Printf.printf "── Three-way Merge ──\n";

  test "clean merge no changes" (fun () ->
    let base = [|"a";"b";"c"|] in
    let r = merge3 base base base in
    assert_eq r.conflict_count 0;
    assert_true (r.merged <> None)
  );

  test "merge one-sided ours" (fun () ->
    let base = [|"a";"b";"c"|] in
    let ours = [|"a";"x";"c"|] in
    let r = merge3 base ours base in
    assert_eq r.conflict_count 0
  );

  test "merge one-sided theirs" (fun () ->
    let base = [|"a";"b";"c"|] in
    let theirs = [|"a";"y";"c"|] in
    let r = merge3 base base theirs in
    assert_eq r.conflict_count 0
  );

  test "merge conflict" (fun () ->
    let base = [|"a";"b";"c"|] in
    let ours = [|"a";"x";"c"|] in
    let theirs = [|"a";"y";"c"|] in
    let r = merge3 base ours theirs in
    assert_eq r.conflict_count 1;
    assert_true (r.merged = None)
  );

  test "merge conflict has chunks" (fun () ->
    let base = [|"a"|] in
    let ours = [|"b"|] in
    let theirs = [|"c"|] in
    let r = merge3 base ours theirs in
    assert_true (List.length r.chunks > 0)
  );

  (* ── Summary format ── *)
  Printf.printf "── Summary Format ──\n";

  test "format summary contains stats" (fun () ->
    let r = diff_lines "a\nb\nc" "a\nx\nc\nd" in
    let s = format_summary r in
    assert_true (String.length s > 50);
    (* Contains key labels *)
    let has sub = try
      let _ = Str.search_forward (Str.regexp_string sub) s 0 in true
      with _ ->
        (* Fallback: manual search *)
        let sl = String.length sub and ss = String.length s in
        let found = ref false in
        for i = 0 to ss - sl do
          if String.sub s i sl = sub then found := true
        done;
        !found
    in
    assert_true (has "Insertions");
    assert_true (has "Deletions");
    assert_true (has "Similarity")
  );

  (* ── Patience diff ── *)
  Printf.printf "── Patience Diff ──\n";

  test "patience diff identical" (fun () ->
    let a = [|"a";"b";"c"|] in
    let r = patience_diff a a in
    assert_eq r.distance 0
  );

  test "patience diff simple change" (fun () ->
    let r = patience_diff [|"a";"b";"c"|] [|"a";"x";"c"|] in
    assert_eq r.distance 2;
    assert_eq r.lcs ["a"; "c"]
  );

  test "patience diff uses unique anchors" (fun () ->
    (* Unique lines "header" and "footer" should anchor the diff *)
    let a = [|"header";"old1";"old2";"footer"|] in
    let b = [|"header";"new1";"footer"|] in
    let r = patience_diff a b in
    assert_true (List.mem "header" r.lcs);
    assert_true (List.mem "footer" r.lcs)
  );

  test "patience diff empty" (fun () ->
    let r = patience_diff [||] [||] in
    assert_eq r.distance 0
  );

  test "patience anchors finds unique matches" (fun () ->
    let a = [|"x";"unique_a";"y";"unique_b";"z"|] in
    let b = [|"w";"unique_a";"v";"unique_b";"u"|] in
    let anchors = patience_anchors a b in
    assert_eq (List.length anchors) 2
  );

  test "lis anchors preserves order" (fun () ->
    let anchors = [(0,2,"a"); (1,0,"b"); (2,3,"c")] in
    let lis = lis_anchors anchors in
    assert_eq (List.length lis) 2 (* (0,2) and (2,3) *)
  );

  (* ── Split lines ── *)
  Printf.printf "── Split Lines ──\n";

  test "split empty string" (fun () ->
    assert_eq (Array.to_list (split_lines "")) []
  );

  test "split single line" (fun () ->
    assert_eq (Array.to_list (split_lines "hello")) ["hello"]
  );

  test "split multiple lines" (fun () ->
    assert_eq (Array.to_list (split_lines "a\nb\nc")) ["a";"b";"c"]
  );

  test "split trailing newline" (fun () ->
    assert_eq (Array.to_list (split_lines "a\nb\n")) ["a";"b"]
  );

  (* ── Edge cases ── *)
  Printf.printf "── Edge Cases ──\n";

  test "single element same" (fun () ->
    let r = diff [|42|] [|42|] in
    assert_eq r.distance 0;
    assert_eq r.lcs [42]
  );

  test "single element different" (fun () ->
    let r = diff [|1|] [|2|] in
    assert_eq r.distance 2
  );

  test "long identical sequence" (fun () ->
    let a = Array.init 100 Fun.id in
    let r = diff a a in
    assert_eq r.distance 0;
    assert_true (r.similarity = 1.0)
  );

  test "large diff performance" (fun () ->
    let a = Array.init 200 Fun.id in
    let b = Array.init 200 (fun i -> i + 1) in
    let r = diff a b in
    assert_true (r.distance > 0);
    assert_true (r.similarity > 0.0)
  );

  test "repeated elements" (fun () ->
    let r = diff [|1;1;1|] [|1;1;1;1|] in
    assert_eq r.distance 1;
    assert_eq r.lcs [1;1;1]
  );

  test "reverse of diff" (fun () ->
    let a = [|"a";"b";"c"|] in
    let b = [|"c";"b";"a"|] in
    let r1 = diff a b in
    let r2 = diff b a in
    assert_eq r1.distance r2.distance
  );

  Printf.printf "\n═══ Results: %d passed, %d failed ═══\n" !passed !failed;
  if !failed > 0 then exit 1
