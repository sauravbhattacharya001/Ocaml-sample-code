(* ============================================================
   String Matching Algorithms
   
   A comprehensive collection of classic string matching algorithms:
   - Naive (brute force) O(nm)
   - Knuth-Morris-Pratt (KMP) O(n+m)
   - Boyer-Moore (bad character + good suffix) O(n/m) best case
   - Rabin-Karp with rolling hash O(n+m) expected
   - Aho-Corasick multi-pattern matching O(n + m + z)
   - Z-algorithm O(n+m)
   - Horspool (simplified Boyer-Moore) O(n/m) best case
   
   Plus utilities: count occurrences, find all with overlap,
   case-insensitive matching, wildcard matching.
   ============================================================ *)

(* ---- Result types ---- *)

type match_result = {
  position: int;     (* 0-based index in text *)
  length: int;       (* length of match *)
  pattern: string;   (* the pattern that matched *)
}

(* ---- Naive / Brute Force ---- *)

module Naive = struct
  let find_all ?(overlap=false) ~pattern text =
    let n = String.length text in
    let m = String.length pattern in
    if m = 0 then []
    else
      let results = ref [] in
      let i = ref 0 in
      while !i <= n - m do
        let j = ref 0 in
        while !j < m && text.[!i + !j] = pattern.[!j] do
          incr j
        done;
        if !j = m then begin
          results := { position = !i; length = m; pattern } :: !results;
          if overlap then incr i
          else i := !i + m
        end else
          incr i
      done;
      List.rev !results

  let find_first ~pattern text =
    match find_all ~pattern text with
    | x :: _ -> Some x
    | [] -> None

  let count ?(overlap=false) ~pattern text =
    List.length (find_all ~overlap ~pattern text)
end

(* ---- Knuth-Morris-Pratt ---- *)

module KMP = struct
  (* Build failure function / partial match table *)
  let build_failure pattern =
    let m = String.length pattern in
    let failure = Array.make m 0 in
    if m > 1 then begin
      let k = ref 0 in
      for i = 1 to m - 1 do
        while !k > 0 && pattern.[!k] <> pattern.[i] do
          k := failure.(!k - 1)
        done;
        if pattern.[!k] = pattern.[i] then incr k;
        failure.(i) <- !k
      done
    end;
    failure

  let find_all ?(overlap=false) ~pattern text =
    let n = String.length text in
    let m = String.length pattern in
    if m = 0 then []
    else
      let failure = build_failure pattern in
      let results = ref [] in
      let q = ref 0 in
      for i = 0 to n - 1 do
        while !q > 0 && pattern.[!q] <> text.[i] do
          q := failure.(!q - 1)
        done;
        if pattern.[!q] = text.[i] then incr q;
        if !q = m then begin
          results := { position = i - m + 1; length = m; pattern } :: !results;
          if overlap then q := failure.(!q - 1)
          else q := 0
        end
      done;
      List.rev !results

  let find_first ~pattern text =
    match find_all ~pattern text with
    | x :: _ -> Some x
    | [] -> None

  let count ?(overlap=false) ~pattern text =
    List.length (find_all ~overlap ~pattern text)

  (* Expose failure function for educational purposes *)
  let failure_function = build_failure
end

(* ---- Boyer-Moore ---- *)

module BoyerMoore = struct
  (* Bad character table: last occurrence of each char in pattern *)
  let bad_char_table pattern =
    let m = String.length pattern in
    let table = Hashtbl.create 256 in
    for i = 0 to m - 1 do
      Hashtbl.replace table pattern.[i] i
    done;
    table

  (* Good suffix table *)
  let good_suffix_table pattern =
    let m = String.length pattern in
    let shift = Array.make (m + 1) m in
    let border = Array.make (m + 1) 0 in
    (* Case 1: matching suffix occurs elsewhere in pattern *)
    let i = ref m and j = ref (m + 1) in
    border.(!i) <- !j;
    while !i > 0 do
      while !j <= m && pattern.[!i - 1] <> pattern.[!j - 1] do
        if shift.(!j) = m then
          shift.(!j) <- !j - !i;
        j := border.(!j)
      done;
      decr i; decr j;
      border.(!i) <- !j
    done;
    (* Case 2: part of matching suffix is a prefix of pattern *)
    let j = ref border.(0) in
    for i = 0 to m do
      if shift.(i) = m then
        shift.(i) <- !j;
      if i = !j then
        j := border.(!j)
    done;
    shift

  let find_all ?(overlap=false) ~pattern text =
    let n = String.length text in
    let m = String.length pattern in
    if m = 0 then []
    else
      let bc = bad_char_table pattern in
      let gs = good_suffix_table pattern in
      let results = ref [] in
      let i = ref 0 in
      while !i <= n - m do
        let j = ref (m - 1) in
        while !j >= 0 && pattern.[!j] = text.[!i + !j] do
          decr j
        done;
        if !j < 0 then begin
          results := { position = !i; length = m; pattern } :: !results;
          if overlap then incr i
          else i := !i + gs.(0)
        end else begin
          let bc_shift =
            match Hashtbl.find_opt bc text.[!i + !j] with
            | Some last -> !j - last
            | None -> !j + 1
          in
          let gs_shift = gs.(!j + 1) in
          i := !i + max bc_shift gs_shift
        end
      done;
      List.rev !results

  let find_first ~pattern text =
    match find_all ~pattern text with
    | x :: _ -> Some x
    | [] -> None

  let count ?(overlap=false) ~pattern text =
    List.length (find_all ~overlap ~pattern text)
end

(* ---- Horspool (Simplified Boyer-Moore) ---- *)

module Horspool = struct
  let bad_char_table pattern =
    let m = String.length pattern in
    let table = Hashtbl.create 256 in
    (* last char excluded from table *)
    for i = 0 to m - 2 do
      Hashtbl.replace table pattern.[i] (m - 1 - i)
    done;
    table

  let find_all ?(overlap=false) ~pattern text =
    let n = String.length text in
    let m = String.length pattern in
    if m = 0 then []
    else
      let table = bad_char_table pattern in
      let results = ref [] in
      let i = ref 0 in
      while !i <= n - m do
        let j = ref (m - 1) in
        while !j >= 0 && text.[!i + !j] = pattern.[!j] do
          decr j
        done;
        if !j < 0 then begin
          results := { position = !i; length = m; pattern } :: !results;
          if overlap then incr i
          else i := !i + m
        end else begin
          let skip =
            match Hashtbl.find_opt table text.[!i + m - 1] with
            | Some s -> s
            | None -> m
          in
          i := !i + (max 1 skip)
        end
      done;
      List.rev !results

  let find_first ~pattern text =
    match find_all ~pattern text with
    | x :: _ -> Some x
    | [] -> None

  let count ?(overlap=false) ~pattern text =
    List.length (find_all ~overlap ~pattern text)
end

(* ---- Rabin-Karp ---- *)

module RabinKarp = struct
  (* Rolling hash parameters *)
  let base = 256
  let prime = 101

  let find_all ?(overlap=false) ~pattern text =
    let n = String.length text in
    let m = String.length pattern in
    if m = 0 || m > n then []
    else
      (* Compute h = base^(m-1) mod prime *)
      let h = ref 1 in
      for _ = 1 to m - 1 do
        h := (!h * base) mod prime
      done;
      let h = !h in
      (* Initial hash values *)
      let p_hash = ref 0 in
      let t_hash = ref 0 in
      for i = 0 to m - 1 do
        p_hash := (!p_hash * base + Char.code pattern.[i]) mod prime;
        t_hash := (!t_hash * base + Char.code text.[i]) mod prime
      done;
      let results = ref [] in
      let i = ref 0 in
      let stop = ref false in
      while not !stop && !i <= n - m do
        if !p_hash = !t_hash then begin
          (* Verify character by character *)
          let j = ref 0 in
          while !j < m && pattern.[!j] = text.[!i + !j] do
            incr j
          done;
          if !j = m then begin
            results := { position = !i; length = m; pattern } :: !results;
            if not overlap then begin
              (* Skip forward past the match *)
              let next = !i + m in
              if next > n - m then
                stop := true
              else begin
                (* Recompute hash from next position *)
                t_hash := 0;
                for k = 0 to m - 1 do
                  t_hash := (!t_hash * base + Char.code text.[next + k]) mod prime
                done;
                i := next;
              end
            end else begin
              if !i < n - m then begin
                t_hash := ((!t_hash - Char.code text.[!i] * h) * base
                           + Char.code text.[!i + m]) mod prime;
                if !t_hash < 0 then t_hash := !t_hash + prime;
              end;
              incr i
            end
          end else begin
            if !i < n - m then begin
              t_hash := ((!t_hash - Char.code text.[!i] * h) * base
                         + Char.code text.[!i + m]) mod prime;
              if !t_hash < 0 then t_hash := !t_hash + prime;
            end;
            incr i
          end
        end else begin
          if !i < n - m then begin
            t_hash := ((!t_hash - Char.code text.[!i] * h) * base
                       + Char.code text.[!i + m]) mod prime;
            if !t_hash < 0 then t_hash := !t_hash + prime;
          end;
          incr i
        end
      done;
      List.rev !results

  let find_first ~pattern text =
    match find_all ~pattern text with
    | x :: _ -> Some x
    | [] -> None

  let count ?(overlap=false) ~pattern text =
    List.length (find_all ~overlap ~pattern text)

  (* Multi-pattern Rabin-Karp: search for multiple patterns of same length *)
  let find_all_multi ~patterns text =
    match patterns with
    | [] -> []
    | first :: _ ->
      let m = String.length first in
      let n = String.length text in
      if m = 0 || m > n then []
      else begin
        (* Compute hashes for all patterns *)
        let pat_hashes = Hashtbl.create (List.length patterns) in
        List.iter (fun p ->
          if String.length p = m then begin
            let h = ref 0 in
            for i = 0 to m - 1 do
              h := (!h * base + Char.code p.[i]) mod prime
            done;
            let existing =
              match Hashtbl.find_opt pat_hashes !h with
              | Some pats -> pats
              | None -> []
            in
            Hashtbl.replace pat_hashes !h (p :: existing)
          end
        ) patterns;
        let h_val = ref 1 in
        for _ = 1 to m - 1 do
          h_val := (!h_val * base) mod prime
        done;
        let h = !h_val in
        let t_hash = ref 0 in
        for i = 0 to m - 1 do
          t_hash := (!t_hash * base + Char.code text.[i]) mod prime
        done;
        let results = ref [] in
        for i = 0 to n - m do
          (match Hashtbl.find_opt pat_hashes !t_hash with
           | Some pats ->
             List.iter (fun p ->
               let j = ref 0 in
               while !j < m && p.[!j] = text.[i + !j] do incr j done;
               if !j = m then
                 results := { position = i; length = m; pattern = p } :: !results
             ) pats
           | None -> ());
          if i < n - m then begin
            t_hash := ((!t_hash - Char.code text.[i] * h) * base
                       + Char.code text.[i + m]) mod prime;
            if !t_hash < 0 then t_hash := !t_hash + prime
          end
        done;
        List.rev !results
      end
end

(* ---- Z-Algorithm ---- *)

module ZAlgorithm = struct
  (* Compute Z-array: z[i] = length of longest substring starting at i
     that is also a prefix of the string *)
  let z_array s =
    let n = String.length s in
    if n = 0 then [||]
    else
      let z = Array.make n 0 in
      z.(0) <- n;
      let l = ref 0 and r = ref 0 in
      for i = 1 to n - 1 do
        if i < !r then
          z.(i) <- min (z.(i - !l)) (!r - i);
        while i + z.(i) < n && s.[z.(i)] = s.[i + z.(i)] do
          z.(i) <- z.(i) + 1
        done;
        if i + z.(i) > !r then begin
          l := i;
          r := i + z.(i)
        end
      done;
      z

  let find_all ?(overlap=false) ~pattern text =
    let m = String.length pattern in
    let n = String.length text in
    if m = 0 then []
    else
      let concat = pattern ^ "$" ^ text in
      let z = z_array concat in
      let results = ref [] in
      let skip_until = ref 0 in
      for i = m + 1 to String.length concat - 1 do
        if z.(i) = m && i - m - 1 >= !skip_until then begin
          let pos = i - m - 1 in
          results := { position = pos; length = m; pattern } :: !results;
          if not overlap then
            skip_until := pos + m
        end
      done;
      List.rev !results

  let find_first ~pattern text =
    match find_all ~pattern text with
    | x :: _ -> Some x
    | [] -> None

  let count ?(overlap=false) ~pattern text =
    List.length (find_all ~overlap ~pattern text)

  (* Expose Z-array for educational use *)
  let compute_z = z_array
end

(* ---- Aho-Corasick (Multi-pattern matching) ---- *)

module AhoCorasick = struct
  type node = {
    mutable children: (char * int) list;  (* char -> node_id *)
    mutable fail: int;                     (* failure link *)
    mutable output: string list;           (* patterns ending here *)
    mutable dict_suffix: int;              (* dictionary suffix link *)
  }

  type automaton = {
    nodes: node array;
    mutable size: int;
  }

  let make_node () = {
    children = [];
    fail = 0;
    output = [];
    dict_suffix = -1;
  }

  let get_child node c =
    List.assoc_opt c node.children

  let add_child node c id =
    node.children <- (c, id) :: node.children

  let build patterns =
    let max_nodes = List.fold_left (fun acc p -> acc + String.length p) 1 patterns + 1 in
    let nodes = Array.init max_nodes (fun _ -> make_node ()) in
    let size = ref 1 in

    (* Build trie *)
    List.iter (fun pattern ->
      let cur = ref 0 in
      String.iter (fun c ->
        match get_child nodes.(!cur) c with
        | Some next -> cur := next
        | None ->
          let id = !size in
          incr size;
          add_child nodes.(!cur) c id;
          cur := id
      ) pattern;
      nodes.(!cur).output <- pattern :: nodes.(!cur).output
    ) patterns;

    (* Build failure links via BFS *)
    let queue = Queue.create () in
    (* Initialize depth-1 nodes *)
    List.iter (fun (_, child_id) ->
      nodes.(child_id).fail <- 0;
      Queue.push child_id queue
    ) nodes.(0).children;

    while not (Queue.is_empty queue) do
      let u = Queue.pop queue in
      List.iter (fun (c, v) ->
        Queue.push v queue;
        let f = ref (nodes.(u).fail) in
        while !f <> 0 && get_child nodes.(!f) c = None do
          f := nodes.(!f).fail
        done;
        nodes.(v).fail <- (
          match get_child nodes.(!f) c with
          | Some w when w <> v -> w
          | _ -> 0
        );
        (* Merge output *)
        nodes.(v).output <- nodes.(v).output @ nodes.(nodes.(v).fail).output;
        (* Dictionary suffix link *)
        nodes.(v).dict_suffix <-
          if nodes.(nodes.(v).fail).output <> [] then nodes.(v).fail
          else nodes.(nodes.(v).fail).dict_suffix
      ) nodes.(u).children
    done;

    { nodes; size = !size }

  let search automaton text =
    let n = String.length text in
    let results = ref [] in
    let state = ref 0 in
    for i = 0 to n - 1 do
      let c = text.[i] in
      while !state <> 0 && get_child automaton.nodes.(!state) c = None do
        state := automaton.nodes.(!state).fail
      done;
      (match get_child automaton.nodes.(!state) c with
       | Some next -> state := next
       | None -> ());
      List.iter (fun pat ->
        results := { position = i - String.length pat + 1;
                     length = String.length pat;
                     pattern = pat } :: !results
      ) automaton.nodes.(!state).output
    done;
    List.rev !results

  let find_all ~patterns text =
    let ac = build patterns in
    search ac text

  let count_all ~patterns text =
    List.length (find_all ~patterns text)
end

(* ---- Utilities ---- *)

module Util = struct
  let lowercase s = String.lowercase_ascii s

  (* Case-insensitive search using KMP *)
  let find_all_icase ~pattern text =
    let lp = lowercase pattern and lt = lowercase text in
    let results = KMP.find_all ~pattern:lp lt in
    List.map (fun r -> { r with pattern }) results

  (* Wildcard matching: '?' matches any single char, '*' matches any sequence *)
  let wildcard_match ~pattern text =
    let m = String.length pattern and n = String.length text in
    (* DP: dp.(i).(j) = pattern[0..i-1] matches text[0..j-1] *)
    let dp = Array.init (m + 1) (fun _ -> Array.make (n + 1) false) in
    dp.(0).(0) <- true;
    (* Leading '*' can match empty *)
    for i = 1 to m do
      if pattern.[i-1] = '*' then dp.(i).(0) <- dp.(i-1).(0)
    done;
    for i = 1 to m do
      for j = 1 to n do
        if pattern.[i-1] = '*' then
          dp.(i).(j) <- dp.(i-1).(j) || dp.(i).(j-1)
        else if pattern.[i-1] = '?' || pattern.[i-1] = text.[j-1] then
          dp.(i).(j) <- dp.(i-1).(j-1)
      done
    done;
    dp.(m).(n)

  (* Longest common substring using dynamic programming *)
  let longest_common_substring s1 s2 =
    let n = String.length s1 and m = String.length s2 in
    if n = 0 || m = 0 then ""
    else
      let prev = Array.make (m + 1) 0 in
      let curr = Array.make (m + 1) 0 in
      let max_len = ref 0 and end_pos = ref 0 in
      for i = 1 to n do
        Array.fill curr 0 (m + 1) 0;
        for j = 1 to m do
          if s1.[i-1] = s2.[j-1] then begin
            curr.(j) <- prev.(j-1) + 1;
            if curr.(j) > !max_len then begin
              max_len := curr.(j);
              end_pos := i
            end
          end
        done;
        Array.blit curr 0 prev 0 (m + 1)
      done;
      String.sub s1 (!end_pos - !max_len) !max_len

  (* Edit distance (Levenshtein) *)
  let edit_distance s1 s2 =
    let n = String.length s1 and m = String.length s2 in
    let dp = Array.init (n + 1) (fun i ->
      Array.init (m + 1) (fun j ->
        if i = 0 then j
        else if j = 0 then i
        else 0
      )
    ) in
    for i = 1 to n do
      for j = 1 to m do
        if s1.[i-1] = s2.[j-1] then
          dp.(i).(j) <- dp.(i-1).(j-1)
        else
          dp.(i).(j) <- 1 + min (min dp.(i-1).(j) dp.(i).(j-1)) dp.(i-1).(j-1)
      done
    done;
    dp.(n).(m)

  (* Hamming distance (same-length strings) *)
  let hamming_distance s1 s2 =
    let n = String.length s1 in
    if n <> String.length s2 then
      invalid_arg "hamming_distance: strings must have equal length"
    else
      let count = ref 0 in
      for i = 0 to n - 1 do
        if s1.[i] <> s2.[i] then incr count
      done;
      !count
end

(* ---- Algorithm comparison / benchmarking ---- *)

module Benchmark = struct
  type algo_result = {
    algo_name: string;
    matches_found: int;
    time_ns: int64;
  }

  let time_fn f =
    let t0 = Sys.time () in
    let result = f () in
    let t1 = Sys.time () in
    (result, Int64.of_float ((t1 -. t0) *. 1_000_000_000.0))

  let compare_algorithms ~pattern text =
    let run name f =
      let (results, time) = time_fn (fun () -> f ~pattern text) in
      { algo_name = name;
        matches_found = List.length results;
        time_ns = time }
    in
    [
      run "Naive" (Naive.find_all ~overlap:false);
      run "KMP" (KMP.find_all ~overlap:false);
      run "Boyer-Moore" (BoyerMoore.find_all ~overlap:false);
      run "Horspool" (Horspool.find_all ~overlap:false);
      run "Rabin-Karp" (RabinKarp.find_all ~overlap:false);
      run "Z-Algorithm" (ZAlgorithm.find_all ~overlap:false);
    ]

  let print_comparison results =
    Printf.printf "%-15s  %8s  %12s\n" "Algorithm" "Matches" "Time (ns)";
    Printf.printf "%s\n" (String.make 40 '-');
    List.iter (fun r ->
      Printf.printf "%-15s  %8d  %12Ld\n" r.algo_name r.matches_found r.time_ns
    ) results
end

(* ============================================================
   Tests
   ============================================================ *)

let tests_passed = ref 0
let tests_failed = ref 0

let assert_equal name expected actual =
  if expected = actual then begin
    incr tests_passed
  end else begin
    incr tests_failed;
    Printf.printf "FAIL: %s\nExpected: %s\nActual:   %s\n\n"
      name (expected) (actual)
  end

let assert_true name cond =
  if cond then incr tests_passed
  else begin
    incr tests_failed;
    Printf.printf "FAIL: %s\n" name
  end

let assert_int name expected actual =
  assert_equal name (string_of_int expected) (string_of_int actual)

let positions results = List.map (fun r -> r.position) results

let () =
  Printf.printf "String Matching Algorithms - Test Suite\n";
  Printf.printf "=======================================\n\n";

  (* ---- Naive tests ---- *)
  let module N = Naive in

  assert_equal "naive: simple find"
    "[1]" (positions (N.find_all ~pattern:"bc" "abcd") |> List.map string_of_int |> String.concat "," |> Printf.sprintf "[%s]");

  assert_equal "naive: no match"
    "[]" (positions (N.find_all ~pattern:"xyz" "abcd") |> List.map string_of_int |> String.concat "," |> Printf.sprintf "[%s]");

  assert_equal "naive: multiple matches"
    "[0,3]" (positions (N.find_all ~pattern:"ab" "ababab") |> List.map string_of_int |> String.concat "," |> Printf.sprintf "[%s]");

  assert_equal "naive: overlap"
    "[0,2,4]" (positions (N.find_all ~overlap:true ~pattern:"aba" "abababa") |> List.map string_of_int |> String.concat "," |> Printf.sprintf "[%s]");

  assert_int "naive: count" 3 (N.count ~pattern:"aa" ~overlap:true "aaaa");

  assert_true "naive: find_first" (N.find_first ~pattern:"cd" "abcdef" = Some { position = 2; length = 2; pattern = "cd" });

  assert_true "naive: find_first none" (N.find_first ~pattern:"zz" "abc" = None);

  assert_equal "naive: pattern at start"
    "[0]" (positions (N.find_all ~pattern:"abc" "abcdef") |> List.map string_of_int |> String.concat "," |> Printf.sprintf "[%s]");

  assert_equal "naive: pattern at end"
    "[3]" (positions (N.find_all ~pattern:"def" "abcdef") |> List.map string_of_int |> String.concat "," |> Printf.sprintf "[%s]");

  assert_equal "naive: single char"
    "[0,2,4]" (positions (N.find_all ~pattern:"a" "abaca") |> List.map string_of_int |> String.concat "," |> Printf.sprintf "[%s]");

  (* ---- KMP tests ---- *)
  let module K = KMP in

  assert_equal "kmp: simple find"
    "[1]" (positions (K.find_all ~pattern:"bc" "abcd") |> List.map string_of_int |> String.concat "," |> Printf.sprintf "[%s]");

  assert_equal "kmp: no match"
    "[]" (positions (K.find_all ~pattern:"xyz" "abcd") |> List.map string_of_int |> String.concat "," |> Printf.sprintf "[%s]");

  assert_equal "kmp: multiple"
    "[0,3]" (positions (K.find_all ~pattern:"ab" "ababab") |> List.map string_of_int |> String.concat "," |> Printf.sprintf "[%s]");

  assert_equal "kmp: overlap"
    "[0,2,4]" (positions (K.find_all ~overlap:true ~pattern:"aba" "abababa") |> List.map string_of_int |> String.concat "," |> Printf.sprintf "[%s]");

  assert_int "kmp: count" 3 (K.count ~pattern:"aa" ~overlap:true "aaaa");

  let f = K.failure_function "ababaca" in
  assert_equal "kmp: failure function"
    "[0,0,1,2,3,0,1]" (Array.to_list f |> List.map string_of_int |> String.concat "," |> Printf.sprintf "[%s]");

  let f2 = K.failure_function "aabaaab" in
  assert_equal "kmp: failure function 2"
    "[0,1,0,1,2,2,0]" (Array.to_list f2 |> List.map string_of_int |> String.concat "," |> Printf.sprintf "[%s]");

  assert_equal "kmp: repeated pattern"
    "[0,4,8]" (positions (K.find_all ~pattern:"abab" "abababababab") |> List.map string_of_int |> String.concat "," |> Printf.sprintf "[%s]");

  assert_equal "kmp: single char pattern"
    "[0,2,4]" (positions (K.find_all ~pattern:"a" "abaca") |> List.map string_of_int |> String.concat "," |> Printf.sprintf "[%s]");

  assert_equal "kmp: pattern equals text"
    "[0]" (positions (K.find_all ~pattern:"abc" "abc") |> List.map string_of_int |> String.concat "," |> Printf.sprintf "[%s]");

  (* ---- Boyer-Moore tests ---- *)
  let module BM = BoyerMoore in

  assert_equal "bm: simple find"
    "[1]" (positions (BM.find_all ~pattern:"bc" "abcd") |> List.map string_of_int |> String.concat "," |> Printf.sprintf "[%s]");

  assert_equal "bm: no match"
    "[]" (positions (BM.find_all ~pattern:"xyz" "abcd") |> List.map string_of_int |> String.concat "," |> Printf.sprintf "[%s]");

  assert_equal "bm: multiple"
    "[0,3]" (positions (BM.find_all ~pattern:"ab" "ababab") |> List.map string_of_int |> String.concat "," |> Printf.sprintf "[%s]");

  assert_equal "bm: overlap"
    "[0,2,4]" (positions (BM.find_all ~overlap:true ~pattern:"aba" "abababa") |> List.map string_of_int |> String.concat "," |> Printf.sprintf "[%s]");

  assert_int "bm: count" 3 (BM.count ~pattern:"aa" ~overlap:true "aaaa");

  assert_equal "bm: long pattern"
    "[4]" (positions (BM.find_all ~pattern:"efgh" "abcdefghij") |> List.map string_of_int |> String.concat "," |> Printf.sprintf "[%s]");

  assert_equal "bm: pattern at end"
    "[7]" (positions (BM.find_all ~pattern:"hij" "abcdefghij") |> List.map string_of_int |> String.concat "," |> Printf.sprintf "[%s]");

  (* ---- Horspool tests ---- *)
  let module H = Horspool in

  assert_equal "horspool: simple find"
    "[1]" (positions (H.find_all ~pattern:"bc" "abcd") |> List.map string_of_int |> String.concat "," |> Printf.sprintf "[%s]");

  assert_equal "horspool: no match"
    "[]" (positions (H.find_all ~pattern:"xyz" "abcd") |> List.map string_of_int |> String.concat "," |> Printf.sprintf "[%s]");

  assert_equal "horspool: multiple"
    "[0,3]" (positions (H.find_all ~pattern:"ab" "ababab") |> List.map string_of_int |> String.concat "," |> Printf.sprintf "[%s]");

  assert_int "horspool: count" 3 (H.count ~pattern:"aa" ~overlap:true "aaaa");

  (* ---- Rabin-Karp tests ---- *)
  let module RK = RabinKarp in

  assert_equal "rk: simple find"
    "[1]" (positions (RK.find_all ~pattern:"bc" "abcd") |> List.map string_of_int |> String.concat "," |> Printf.sprintf "[%s]");

  assert_equal "rk: no match"
    "[]" (positions (RK.find_all ~pattern:"xyz" "abcd") |> List.map string_of_int |> String.concat "," |> Printf.sprintf "[%s]");

  assert_equal "rk: multiple"
    "[0,3]" (positions (RK.find_all ~pattern:"ab" "ababab") |> List.map string_of_int |> String.concat "," |> Printf.sprintf "[%s]");

  assert_equal "rk: overlap"
    "[0,2,4]" (positions (RK.find_all ~overlap:true ~pattern:"aba" "abababa") |> List.map string_of_int |> String.concat "," |> Printf.sprintf "[%s]");

  assert_int "rk: count" 3 (RK.count ~pattern:"aa" ~overlap:true "aaaa");

  (* Multi-pattern Rabin-Karp *)
  let rk_multi = RK.find_all_multi ~patterns:["ab"; "cd"] "abcdef" in
  assert_int "rk: multi count" 2 (List.length rk_multi);

  let rk_multi2 = RK.find_all_multi ~patterns:["xx"; "yy"; "zz"] "abcdef" in
  assert_int "rk: multi no match" 0 (List.length rk_multi2);

  (* ---- Z-Algorithm tests ---- *)
  let module Z = ZAlgorithm in

  assert_equal "z: simple find"
    "[1]" (positions (Z.find_all ~pattern:"bc" "abcd") |> List.map string_of_int |> String.concat "," |> Printf.sprintf "[%s]");

  assert_equal "z: no match"
    "[]" (positions (Z.find_all ~pattern:"xyz" "abcd") |> List.map string_of_int |> String.concat "," |> Printf.sprintf "[%s]");

  assert_equal "z: multiple"
    "[0,3]" (positions (Z.find_all ~pattern:"ab" "ababab") |> List.map string_of_int |> String.concat "," |> Printf.sprintf "[%s]");

  assert_equal "z: overlap"
    "[0,2,4]" (positions (Z.find_all ~overlap:true ~pattern:"aba" "abababa") |> List.map string_of_int |> String.concat "," |> Printf.sprintf "[%s]");

  let za = Z.compute_z "aabxaab" in
  assert_equal "z: z-array"
    "[7,1,0,0,3,1,0]" (Array.to_list za |> List.map string_of_int |> String.concat "," |> Printf.sprintf "[%s]");

  assert_int "z: count" 3 (Z.count ~pattern:"aa" ~overlap:true "aaaa");

  (* ---- Aho-Corasick tests ---- *)
  let module AC = AhoCorasick in

  let ac1 = AC.find_all ~patterns:["he"; "she"; "his"; "hers"] "ahishers" in
  assert_true "ac: multi-pattern" (List.length ac1 >= 4);

  let ac2 = AC.find_all ~patterns:["abc"; "def"] "abcdefabc" in
  assert_int "ac: two patterns" 3 (List.length ac2);

  let ac3 = AC.find_all ~patterns:["a"; "ab"; "abc"] "abc" in
  assert_true "ac: overlapping patterns" (List.length ac3 >= 3);

  let ac4 = AC.find_all ~patterns:["xyz"] "abcdef" in
  assert_int "ac: no match" 0 (List.length ac4);

  let ac5 = AC.find_all ~patterns:["aa"] "aaaa" in
  assert_true "ac: overlapping occurrences" (List.length ac5 >= 3);

  let ac_count = AC.count_all ~patterns:["the"; "he"] "the theater" in
  assert_true "ac: count" (ac_count >= 3);

  (* ---- Utility tests ---- *)

  (* Case-insensitive *)
  let icase = Util.find_all_icase ~pattern:"Hello" "hello HELLO HeLLo" in
  assert_int "icase: count" 3 (List.length icase);

  (* Wildcard matching *)
  assert_true "wildcard: exact" (Util.wildcard_match ~pattern:"abc" "abc");
  assert_true "wildcard: ?" (Util.wildcard_match ~pattern:"a?c" "abc");
  assert_true "wildcard: *" (Util.wildcard_match ~pattern:"a*d" "abcd");
  assert_true "wildcard: * empty" (Util.wildcard_match ~pattern:"a*" "a");
  assert_true "wildcard: complex" (Util.wildcard_match ~pattern:"*a*b*" "xaybz" = false);
  assert_true "wildcard: all *" (Util.wildcard_match ~pattern:"***" "anything");
  assert_true "wildcard: no match" (not (Util.wildcard_match ~pattern:"abc" "abd"));

  (* Longest common substring *)
  assert_equal "lcs: basic" "abc" (Util.longest_common_substring "xabcy" "zabcw");
  assert_equal "lcs: empty" "" (Util.longest_common_substring "abc" "xyz");
  assert_equal "lcs: same" "hello" (Util.longest_common_substring "hello" "hello");

  (* Edit distance *)
  assert_int "edit: same" 0 (Util.edit_distance "abc" "abc");
  assert_int "edit: insert" 1 (Util.edit_distance "abc" "abcd");
  assert_int "edit: delete" 1 (Util.edit_distance "abcd" "abc");
  assert_int "edit: replace" 1 (Util.edit_distance "abc" "axc");
  assert_int "edit: kitten/sitting" 3 (Util.edit_distance "kitten" "sitting");
  assert_int "edit: empty" 5 (Util.edit_distance "" "hello");

  (* Hamming distance *)
  assert_int "hamming: same" 0 (Util.hamming_distance "abc" "abc");
  assert_int "hamming: one diff" 1 (Util.hamming_distance "abc" "axc");
  assert_int "hamming: all diff" 3 (Util.hamming_distance "abc" "xyz");

  (* ---- Cross-algorithm consistency tests ---- *)

  let text = "abababababab" in
  let pattern = "abab" in
  let naive_r = Naive.find_all ~pattern text in
  let kmp_r = KMP.find_all ~pattern text in
  let bm_r = BoyerMoore.find_all ~pattern text in
  let rk_r = RabinKarp.find_all ~pattern text in
  let z_r = ZAlgorithm.find_all ~pattern text in
  let h_r = Horspool.find_all ~pattern text in
  let naive_p = positions naive_r in
  assert_equal "consistency: all agree" "true"
    (string_of_bool (
      positions kmp_r = naive_p &&
      positions bm_r = naive_p &&
      positions rk_r = naive_p &&
      positions z_r = naive_p &&
      positions h_r = naive_p
    ));

  let text2 = "aaaaaa" in
  let pattern2 = "aaa" in
  let n2 = Naive.find_all ~overlap:true ~pattern:pattern2 text2 in
  let k2 = KMP.find_all ~overlap:true ~pattern:pattern2 text2 in
  let bm2 = BoyerMoore.find_all ~overlap:true ~pattern:pattern2 text2 in
  let rk2 = RabinKarp.find_all ~overlap:true ~pattern:pattern2 text2 in
  let z2 = ZAlgorithm.find_all ~overlap:true ~pattern:pattern2 text2 in
  let n2_p = positions n2 in
  assert_equal "consistency overlap: all agree" "true"
    (string_of_bool (
      positions k2 = n2_p &&
      positions bm2 = n2_p &&
      positions rk2 = n2_p &&
      positions z2 = n2_p
    ));

  (* Edge cases across all algorithms *)
  let algos = [
    ("Naive", fun p t -> Naive.find_all ~pattern:p t);
    ("KMP", fun p t -> KMP.find_all ~pattern:p t);
    ("BM", fun p t -> BoyerMoore.find_all ~pattern:p t);
    ("Horspool", fun p t -> Horspool.find_all ~pattern:p t);
    ("RK", fun p t -> RabinKarp.find_all ~pattern:p t);
    ("Z", fun p t -> ZAlgorithm.find_all ~pattern:p t);
  ] in
  List.iter (fun (name, f) ->
    assert_equal (name ^ ": pattern longer than text") "[]"
      (positions (f "abcdef" "abc") |> List.map string_of_int |> String.concat "," |> Printf.sprintf "[%s]");
    assert_equal (name ^ ": exact match") "[0]"
      (positions (f "hello" "hello") |> List.map string_of_int |> String.concat "," |> Printf.sprintf "[%s]");
    assert_equal (name ^ ": single char text") "[0]"
      (positions (f "a" "a") |> List.map string_of_int |> String.concat "," |> Printf.sprintf "[%s]");
  ) algos;

  (* ---- Benchmark ---- *)
  Printf.printf "\n--- Algorithm Comparison ---\n";
  let text3 = String.make 10000 'a' ^ "b" ^ String.make 10000 'a' in
  let results = Benchmark.compare_algorithms ~pattern:(String.make 100 'a' ^ "b") text3 in
  Benchmark.print_comparison results;

  Printf.printf "\n=======================================\n";
  Printf.printf "Results: %d passed, %d failed (total %d)\n"
    !tests_passed !tests_failed (!tests_passed + !tests_failed)
