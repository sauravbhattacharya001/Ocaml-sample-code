(* Tests for Pairing Heap *)

(* We inline a minimal pairing heap here for test isolation,
   mirroring the module in pairing_heap.ml. *)

type 'a heap =
  | Empty
  | Node of 'a * 'a heap list

module Make (Ord : sig type t val compare : t -> t -> int end) = struct
  type t = Ord.t heap

  let empty = Empty
  let is_empty = function Empty -> true | _ -> false

  let merge h1 h2 = match h1, h2 with
    | Empty, h | h, Empty -> h
    | Node (x, xs), Node (y, ys) ->
      if Ord.compare x y <= 0 then Node (x, h2 :: xs)
      else Node (y, h1 :: ys)

  let insert x h = merge (Node (x, [])) h

  let find_min = function Empty -> None | Node (x, _) -> Some x
  let find_min_exn = function Empty -> failwith "empty" | Node (x, _) -> x

  let rec merge_pairs = function
    | [] -> Empty | [h] -> h
    | h1 :: h2 :: rest -> merge (merge h1 h2) (merge_pairs rest)

  let delete_min = function Empty -> Empty | Node (_, cs) -> merge_pairs cs

  let of_list xs = List.fold_left (fun h x -> insert x h) empty xs

  let to_sorted_list h =
    let rec aux acc = function
      | Empty -> List.rev acc
      | h -> aux (find_min_exn h :: acc) (delete_min h)
    in aux [] h

  let rec size = function
    | Empty -> 0
    | Node (_, cs) -> 1 + List.fold_left (fun a c -> a + size c) 0 cs
end

module H = Make (struct type t = int let compare = compare end)

let passed = ref 0
let failed = ref 0

let check name cond =
  if cond then (incr passed; Printf.printf "  PASS: %s\n" name)
  else (incr failed; Printf.printf "  FAIL: %s\n" name)

let () =
  print_endline "=== Pairing Heap Tests ===\n";

  (* Empty heap *)
  check "empty is_empty" (H.is_empty H.empty);
  check "empty find_min" (H.find_min H.empty = None);
  check "empty size" (H.size H.empty = 0);

  (* Single insert *)
  let h1 = H.insert 5 H.empty in
  check "single insert" (H.find_min h1 = Some 5);
  check "single size" (H.size h1 = 1);

  (* Multiple inserts *)
  let h2 = H.of_list [42; 17; 3; 99; 1; 28] in
  check "of_list min" (H.find_min h2 = Some 1);
  check "of_list size" (H.size h2 = 6);

  (* Sorted extraction *)
  let sorted = H.to_sorted_list h2 in
  check "sorted order" (sorted = [1; 3; 17; 28; 42; 99]);

  (* Delete min *)
  let h3 = H.delete_min h2 in
  check "delete_min new min" (H.find_min h3 = Some 3);
  check "delete_min size" (H.size h3 = 5);

  (* Merge *)
  let ha = H.of_list [10; 30; 50] in
  let hb = H.of_list [5; 25; 45] in
  let hm = H.merge ha hb in
  check "merge min" (H.find_min hm = Some 5);
  check "merge size" (H.size hm = 6);
  check "merge sorted" (H.to_sorted_list hm = [5; 10; 25; 30; 45; 50]);

  (* Persistence — originals unchanged *)
  check "persist ha" (H.find_min ha = Some 10);
  check "persist hb" (H.find_min hb = Some 5);

  (* Delete all *)
  let h4 = H.of_list [3; 1; 2] in
  let h4 = H.delete_min h4 in
  let h4 = H.delete_min h4 in
  let h4 = H.delete_min h4 in
  check "drain to empty" (H.is_empty h4);

  (* Duplicate elements *)
  let hd = H.of_list [5; 5; 5; 3; 3] in
  check "duplicates sorted" (H.to_sorted_list hd = [3; 3; 5; 5; 5]);

  (* Large heap *)
  let big = H.of_list (List.init 100 (fun i -> 100 - i)) in
  check "large min" (H.find_min big = Some 1);
  check "large size" (H.size big = 100);
  let big_sorted = H.to_sorted_list big in
  check "large sorted" (big_sorted = List.init 100 (fun i -> i + 1));

  Printf.printf "\n%d passed, %d failed\n" !passed !failed;
  if !failed > 0 then exit 1
