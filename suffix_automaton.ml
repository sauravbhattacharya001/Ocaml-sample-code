(* ============================================================
   Suffix Automaton (SAM)
   
   A suffix automaton for a string of length n is the minimal
   DFA that recognizes exactly all suffixes of the string.
   It has at most 2n-1 states and at most 3n-4 transitions.
   
   Key operations:
   - Build SAM from a string in O(n) time
   - Check if a string is a substring in O(m) time
   - Count distinct substrings in O(n) time
   - Find longest common substring of two strings
   - Count occurrences of a pattern
   - Find shortest non-occurring substring
   
   Applications: text indexing, bioinformatics, competitive
   programming, data compression analysis.
   ============================================================ *)

(* A state in the suffix automaton *)
type state = {
  mutable len: int;           (* length of longest suffix in this class *)
  mutable link: int;          (* suffix link (-1 for initial) *)
  mutable transitions: (char * int) list;  (* char -> state_id *)
  mutable is_clone: bool;     (* whether this state was created by cloning *)
  mutable end_pos: int;       (* end position of first occurrence, -1 if clone *)
}

(* The suffix automaton *)
type t = {
  mutable states: state array;
  mutable size: int;          (* number of states used *)
  mutable last: int;          (* id of the state corresponding to the entire string *)
}

(* Create a new state *)
let make_state ?(len=0) ?(link=(-1)) ?(is_clone=false) ?(end_pos=(-1)) () =
  { len; link; transitions = []; is_clone; end_pos }

(* Create a new suffix automaton *)
let create ?(capacity=256) () =
  let states = Array.init (capacity * 2 + 2) (fun _ -> make_state ()) in
  (* State 0 is the initial state *)
  states.(0) <- make_state ~len:0 ~link:(-1) ();
  { states; size = 1; last = 0 }

(* Ensure capacity *)
let ensure_capacity sam needed =
  if needed >= Array.length sam.states then begin
    let new_cap = max needed (Array.length sam.states * 2) in
    let new_arr = Array.init new_cap (fun i ->
      if i < Array.length sam.states then sam.states.(i)
      else make_state ()
    ) in
    sam.states <- new_arr
  end

(* Get transition for a character *)
let get_trans st c =
  List.assoc_opt c st.transitions

(* Set transition for a character *)
let set_trans st c target =
  st.transitions <- (c, target) :: (List.remove_assoc c st.transitions)

(* Extend the automaton with one character *)
let extend sam c pos =
  let cur = sam.size in
  ensure_capacity sam (cur + 2);
  sam.states.(cur) <- make_state ~len:(sam.states.(sam.last).len + 1) ~end_pos:pos ();
  sam.size <- sam.size + 1;
  let p = ref sam.last in
  (* Walk up suffix links and add transitions *)
  while !p <> -1 && get_trans sam.states.(!p) c = None do
    set_trans sam.states.(!p) c cur;
    p := sam.states.(!p).link
  done;
  if !p = -1 then
    (* No state with transition c; link to initial *)
    sam.states.(cur).link <- 0
  else begin
    let q = match get_trans sam.states.(!p) c with
      | Some q -> q | None -> assert false
    in
    if sam.states.(!p).len + 1 = sam.states.(q).len then
      (* q is the correct suffix link *)
      sam.states.(cur).link <- q
    else begin
      (* Clone q *)
      let clone = sam.size in
      ensure_capacity sam (clone + 1);
      sam.states.(clone) <- {
        len = sam.states.(!p).len + 1;
        link = sam.states.(q).link;
        transitions = sam.states.(q).transitions;
        is_clone = true;
        end_pos = -1;
      };
      sam.size <- sam.size + 1;
      (* Redirect transitions *)
      while !p <> -1 && get_trans sam.states.(!p) c = Some q do
        set_trans sam.states.(!p) c clone;
        p := sam.states.(!p).link
      done;
      sam.states.(q).link <- clone;
      sam.states.(cur).link <- clone
    end
  end;
  sam.last <- cur

(* Build a suffix automaton from a string *)
let build s =
  let n = String.length s in
  let sam = create ~capacity:(max 1 n) () in
  for i = 0 to n - 1 do
    extend sam s.[i] i
  done;
  sam

(* Check if a pattern is a substring of the original string *)
let contains sam pattern =
  let m = String.length pattern in
  let rec walk st i =
    if i >= m then true
    else match get_trans sam.states.(st) pattern.[i] with
      | Some next -> walk next (i + 1)
      | None -> false
  in
  walk 0 0

(* Count distinct substrings (excluding empty string) *)
let count_distinct sam =
  let total = ref 0 in
  for i = 1 to sam.size - 1 do
    total := !total + sam.states.(i).len - sam.states.(sam.states.(i).link).len
  done;
  !total

(* Find the longest substring common to two strings *)
let longest_common_substring s1 s2 =
  let sam = build s1 in
  let n2 = String.length s2 in
  let best_len = ref 0 in
  let best_end = ref 0 in
  let cur = ref 0 in
  let cur_len = ref 0 in
  for i = 0 to n2 - 1 do
    let c = s2.[i] in
    (* Follow suffix links until we find a transition or reach initial *)
    while !cur <> 0 && get_trans sam.states.(!cur) c = None do
      cur := sam.states.(!cur).link;
      cur_len := sam.states.(!cur).len
    done;
    (match get_trans sam.states.(!cur) c with
     | Some next ->
       cur := next;
       cur_len := !cur_len + 1
     | None ->
       cur := 0;
       cur_len := 0);
    if !cur_len > !best_len then begin
      best_len := !cur_len;
      best_end := i
    end
  done;
  if !best_len = 0 then ""
  else String.sub s2 (!best_end - !best_len + 1) !best_len

(* Topological sort of SAM states (by decreasing len) *)
let topo_sort sam =
  let sorted = Array.init sam.size (fun i -> i) in
  (* Count sort by len *)
  let max_len = ref 0 in
  for i = 0 to sam.size - 1 do
    if sam.states.(i).len > !max_len then max_len := sam.states.(i).len
  done;
  let cnt = Array.make (!max_len + 1) 0 in
  for i = 0 to sam.size - 1 do
    cnt.(sam.states.(i).len) <- cnt.(sam.states.(i).len) + 1
  done;
  for i = 1 to !max_len do
    cnt.(i) <- cnt.(i) + cnt.(i - 1)
  done;
  let result = Array.make sam.size 0 in
  for i = sam.size - 1 downto 0 do
    let l = sam.states.(sorted.(i)).len in
    cnt.(l) <- cnt.(l) - 1;
    result.(cnt.(l)) <- sorted.(i)
  done;
  result

(* Count occurrences of each equivalence class *)
let count_occurrences sam =
  let occ = Array.make sam.size 0 in
  (* Non-clone states have occurrence 1 *)
  for i = 1 to sam.size - 1 do
    if not sam.states.(i).is_clone then occ.(i) <- 1
  done;
  (* Propagate in reverse topological order *)
  let sorted = topo_sort sam in
  for j = sam.size - 1 downto 1 do
    let v = sorted.(j) in
    let link = sam.states.(v).link in
    if link >= 0 then
      occ.(link) <- occ.(link) + occ.(v)
  done;
  occ

(* Count occurrences of a specific pattern *)
let count_pattern sam pattern =
  let m = String.length pattern in
  let rec walk st i =
    if i >= m then Some st
    else match get_trans sam.states.(st) pattern.[i] with
      | Some next -> walk next (i + 1)
      | None -> None
  in
  match walk 0 0 with
  | None -> 0
  | Some st ->
    let occ = count_occurrences sam in
    occ.(st)

(* Find the shortest string NOT occurring as a substring *)
let shortest_absent sam =
  (* BFS on the automaton looking for missing transitions *)
  let q = Queue.create () in
  Queue.push (0, "") q;
  let visited = Hashtbl.create (sam.size * 2) in
  Hashtbl.add visited 0 true;
  let result = ref None in
  while !result = None do
    let (st, path) = Queue.pop q in
    (* Try all lowercase letters *)
    let found = ref false in
    let c = ref 'a' in
    while !c <= 'z' && not !found do
      (match get_trans sam.states.(st) !c with
       | None ->
         result := Some (path ^ String.make 1 !c);
         found := true
       | Some next ->
         if not (Hashtbl.mem visited next) then begin
           Hashtbl.add visited next true;
           Queue.push (next, path ^ String.make 1 !c) q
         end);
      c := Char.chr (Char.code !c + 1)
    done
  done;
  match !result with Some s -> s | None -> failwith "unreachable"

(* Get all distinct substrings (for small strings only!) *)
let all_substrings sam =
  let result = ref [] in
  let rec dfs st path =
    if path <> "" then result := path :: !result;
    (* Sort transitions for deterministic order *)
    let trans = List.sort (fun (a, _) (b, _) -> Char.compare a b) sam.states.(st).transitions in
    List.iter (fun (c, next) ->
      dfs next (path ^ String.make 1 c)
    ) trans
  in
  dfs 0 "";
  List.rev !result

(* Pretty-print automaton info *)
let info sam =
  Printf.printf "Suffix Automaton:\n";
  Printf.printf "  States: %d\n" sam.size;
  let total_trans = ref 0 in
  for i = 0 to sam.size - 1 do
    total_trans := !total_trans + List.length sam.states.(i).transitions
  done;
  Printf.printf "  Transitions: %d\n" !total_trans;
  Printf.printf "  Distinct substrings: %d\n" (count_distinct sam)

(* ---- Demo ---- *)

let () =
  Printf.printf "=== Suffix Automaton Demo ===\n\n";

  (* Basic construction and queries *)
  let s = "abcbc" in
  Printf.printf "String: \"%s\"\n" s;
  let sam = build s in
  info sam;
  Printf.printf "\n";

  (* Substring checks *)
  let patterns = ["abc"; "bcb"; "cb"; "abd"; "abcbc"; "abcbcx"; ""; "c"] in
  Printf.printf "Substring checks:\n";
  List.iter (fun p ->
    Printf.printf "  \"%s\" -> %b\n" p (contains sam p)
  ) patterns;
  Printf.printf "\n";

  (* Pattern occurrence counting *)
  let s2 = "abababab" in
  Printf.printf "String: \"%s\"\n" s2;
  let sam2 = build s2 in
  let count_patterns = ["ab"; "aba"; "abab"; "b"; "x"] in
  Printf.printf "Occurrence counts:\n";
  List.iter (fun p ->
    Printf.printf "  \"%s\" -> %d\n" p (count_pattern sam2 p)
  ) count_patterns;
  Printf.printf "\n";

  (* Longest common substring *)
  let a = "abcdefg" and b = "xyzcdefpq" in
  Printf.printf "Longest common substring of \"%s\" and \"%s\":\n" a b;
  Printf.printf "  \"%s\"\n\n" (longest_common_substring a b);

  (* Shortest absent substring *)
  let s3 = "aab" in
  Printf.printf "String: \"%s\"\n" s3;
  let sam3 = build s3 in
  Printf.printf "Shortest absent substring: \"%s\"\n\n" (shortest_absent sam3);

  (* All distinct substrings (small string) *)
  let s4 = "aba" in
  Printf.printf "All distinct substrings of \"%s\":\n" s4;
  let sam4 = build s4 in
  let subs = all_substrings sam4 in
  Printf.printf "  Count: %d\n" (List.length subs);
  Printf.printf "  [%s]\n\n" (String.concat "; " (List.map (fun s -> "\"" ^ s ^ "\"") subs));

  Printf.printf "=== Demo complete ===\n"
