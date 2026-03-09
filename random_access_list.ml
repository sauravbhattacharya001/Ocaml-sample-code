(* ================================================================== *)
(*  Random Access List                                                *)
(*  Okasaki-style skew-binary random access list                      *)
(*  O(1) cons/head/tail, O(log n) lookup/update                      *)
(* ================================================================== *)

(* A complete binary tree of size 2^k - 1 *)
type 'a tree =
  | Leaf of 'a
  | Node of 'a * 'a tree * 'a tree

(* A random access list is a list of (size, tree) pairs
   where sizes follow a skew-binary number representation *)
type 'a t = (int * 'a tree) list

(* ---- Construction ---- *)

let empty : 'a t = []

let is_empty (l : 'a t) : bool = l = []

(* O(1) cons: prepend an element *)
let cons (x : 'a) (l : 'a t) : 'a t =
  match l with
  | (s1, t1) :: (s2, t2) :: rest when s1 = s2 ->
    (* Two trees of equal size: merge into a bigger tree *)
    (1 + s1 + s2, Node (x, t1, t2)) :: rest
  | _ ->
    (1, Leaf x) :: l

(* O(1) head: get the first element *)
let head (l : 'a t) : 'a =
  match l with
  | [] -> failwith "head: empty list"
  | (_, Leaf x) :: _ -> x
  | (_, Node (x, _, _)) :: _ -> x

let head_opt (l : 'a t) : 'a option =
  match l with
  | [] -> None
  | (_, Leaf x) :: _ -> Some x
  | (_, Node (x, _, _)) :: _ -> Some x

(* O(1) tail: remove the first element *)
let tail (l : 'a t) : 'a t =
  match l with
  | [] -> failwith "tail: empty list"
  | (_, Leaf _) :: rest -> rest
  | (s, Node (_, t1, t2)) :: rest ->
    let s' = s / 2 in
    (s', t1) :: (s', t2) :: rest

(* ---- Random Access ---- *)

(* Lookup in a tree of given size at index i *)
let rec lookup_tree (s : int) (i : int) (t : 'a tree) : 'a =
  match t with
  | Leaf x ->
    if i = 0 then x
    else failwith "lookup_tree: index out of bounds"
  | Node (x, t1, t2) ->
    if i = 0 then x
    else
      let s' = s / 2 in
      if i <= s' then lookup_tree s' (i - 1) t1
      else lookup_tree s' (i - 1 - s') t2

(* O(log n) lookup by index *)
let rec lookup (i : int) (l : 'a t) : 'a =
  match l with
  | [] -> failwith "lookup: index out of bounds"
  | (s, t) :: rest ->
    if i < s then lookup_tree s i t
    else lookup (i - s) rest

let lookup_opt (i : int) (l : 'a t) : 'a option =
  try Some (lookup i l) with _ -> None

(* Update in a tree of given size at index i *)
let rec update_tree (s : int) (i : int) (y : 'a) (t : 'a tree) : 'a tree =
  match t with
  | Leaf _ ->
    if i = 0 then Leaf y
    else failwith "update_tree: index out of bounds"
  | Node (x, t1, t2) ->
    if i = 0 then Node (y, t1, t2)
    else
      let s' = s / 2 in
      if i <= s' then Node (x, update_tree s' (i - 1) y t1, t2)
      else Node (x, t1, update_tree s' (i - 1 - s') y t2)

(* O(log n) functional update at index *)
let rec update (i : int) (y : 'a) (l : 'a t) : 'a t =
  match l with
  | [] -> failwith "update: index out of bounds"
  | (s, t) :: rest ->
    if i < s then (s, update_tree s i y t) :: rest
    else (s, t) :: update (i - s) y rest

(* ---- Derived Operations ---- *)

(* O(n) length *)
let length (l : 'a t) : int =
  List.fold_left (fun acc (s, _) -> acc + s) 0 l

(* Build from a regular list *)
let of_list (xs : 'a list) : 'a t =
  List.fold_right cons xs empty

(* Convert to a regular list *)
let to_list (l : 'a t) : 'a list =
  let rec tree_to_list acc = function
    | Leaf x -> x :: acc
    | Node (x, t1, t2) -> x :: tree_to_list (tree_to_list acc t2) t1
  in
  List.fold_right (fun (_, t) acc -> tree_to_list acc t) l []

(* O(n) map *)
let map (f : 'a -> 'b) (l : 'a t) : 'b t =
  let rec map_tree = function
    | Leaf x -> Leaf (f x)
    | Node (x, t1, t2) -> Node (f x, map_tree t1, map_tree t2)
  in
  List.map (fun (s, t) -> (s, map_tree t)) l

(* O(n) fold left (in index order) *)
let fold_left (f : 'a -> 'b -> 'a) (acc : 'a) (l : 'b t) : 'a =
  let rec fold_tree a = function
    | Leaf x -> f a x
    | Node (x, t1, t2) -> fold_tree (fold_tree (f a x) t1) t2
  in
  List.fold_left (fun a (_, t) -> fold_tree a t) acc l

(* O(n) fold right *)
let fold_right (f : 'a -> 'b -> 'b) (l : 'a t) (acc : 'b) : 'b =
  let rec fold_tree t a =
    match t with
    | Leaf x -> f x a
    | Node (x, t1, t2) -> f x (fold_tree t1 (fold_tree t2 a))
  in
  List.fold_right (fun (_, t) a -> fold_tree t a) l acc

(* O(n) iter *)
let iter (f : 'a -> unit) (l : 'a t) : unit =
  let rec iter_tree = function
    | Leaf x -> f x
    | Node (x, t1, t2) -> f x; iter_tree t1; iter_tree t2
  in
  List.iter (fun (_, t) -> iter_tree t) l

(* O(n) for_all *)
let for_all (p : 'a -> bool) (l : 'a t) : bool =
  fold_left (fun acc x -> acc && p x) true l

(* O(n) exists *)
let exists (p : 'a -> bool) (l : 'a t) : bool =
  fold_left (fun acc x -> acc || p x) false l

(* O(n) filter - rebuild, preserving order *)
let filter (p : 'a -> bool) (l : 'a t) : 'a t =
  of_list (List.filter p (to_list l))

(* O(n) find_opt *)
let find_opt (p : 'a -> bool) (l : 'a t) : 'a option =
  let exception Found of 'a in
  try
    iter (fun x -> if p x then raise (Found x)) l;
    None
  with Found x -> Some x

(* O(n) find index *)
let find_index (p : 'a -> bool) (l : 'a t) : int option =
  let exception Found of int in
  let i = ref 0 in
  try
    iter (fun x ->
      if p x then raise (Found !i);
      incr i
    ) l;
    None
  with Found idx -> Some idx

(* Append two lists *)
let append (l1 : 'a t) (l2 : 'a t) : 'a t =
  fold_right cons l1 l2

(* Reverse *)
let rev (l : 'a t) : 'a t =
  fold_left (fun acc x -> cons x acc) empty l

(* Take first n elements *)
let take (n : int) (l : 'a t) : 'a t =
  let xs = to_list l in
  let rec take_list n xs =
    if n <= 0 then []
    else match xs with
      | [] -> []
      | x :: rest -> x :: take_list (n - 1) rest
  in
  of_list (take_list n xs)

(* Drop first n elements *)
let drop (n : int) (l : 'a t) : 'a t =
  let rec go n l =
    if n <= 0 then l
    else match l with
      | [] -> []
      | _ -> go (n - 1) (tail l)
  in
  go n l

(* Split at index n *)
let split_at (n : int) (l : 'a t) : 'a t * 'a t =
  (take n l, drop n l)

(* Zip two lists *)
let zip (l1 : 'a t) (l2 : 'b t) : ('a * 'b) t =
  of_list (List.combine (to_list l1) (to_list l2))

(* Unzip *)
let unzip (l : ('a * 'b) t) : 'a t * 'b t =
  let pairs = to_list l in
  let a, b = List.split pairs in
  (of_list a, of_list b)

(* mapi: map with index *)
let mapi (f : int -> 'a -> 'b) (l : 'a t) : 'b t =
  let i = ref 0 in
  let xs = to_list l in
  of_list (List.map (fun x -> let r = f !i x in incr i; r) xs)

(* nth - alias for lookup *)
let nth (l : 'a t) (i : int) : 'a = lookup i l

(* Pretty print for debugging *)
let pp (show : 'a -> string) (l : 'a t) : string =
  let items = to_list l in
  "[" ^ String.concat "; " (List.map show items) ^ "]"

(* Internal structure info *)
let tree_sizes (l : 'a t) : int list =
  List.map fst l

(* Number of trees in the spine *)
let num_trees (l : 'a t) : int =
  List.length l


(* ================================================================== *)
(*  Tests                                                             *)
(* ================================================================== *)

let () =
  let pass = ref 0 in
  let fail = ref 0 in
  let test name f =
    try
      f ();
      incr pass;
      Printf.printf "  PASS: %s\n" name
    with e ->
      incr fail;
      Printf.printf "  FAIL: %s -- %s\n" name (Printexc.to_string e)
  in

  Printf.printf "\n=== Random Access List Tests ===\n\n";

  (* -- Construction -- *)
  test "empty is empty" (fun () ->
    assert (is_empty empty);
    assert (length empty = 0)
  );

  test "cons creates non-empty" (fun () ->
    let l = cons 42 empty in
    assert (not (is_empty l));
    assert (length l = 1)
  );

  test "head of singleton" (fun () ->
    let l = cons 7 empty in
    assert (head l = 7)
  );

  test "head_opt empty" (fun () ->
    assert (head_opt empty = None)
  );

  test "head_opt non-empty" (fun () ->
    assert (head_opt (cons 5 empty) = Some 5)
  );

  test "tail of singleton is empty" (fun () ->
    let l = cons 1 empty in
    assert (is_empty (tail l))
  );

  test "head raises on empty" (fun () ->
    let raised = try ignore (head empty); false with _ -> true in
    assert raised
  );

  test "tail raises on empty" (fun () ->
    let raised = try ignore (tail empty); false with _ -> true in
    assert raised
  );

  test "cons/head/tail sequence" (fun () ->
    let l = cons 1 (cons 2 (cons 3 empty)) in
    assert (head l = 1);
    assert (head (tail l) = 2);
    assert (head (tail (tail l)) = 3);
    assert (is_empty (tail (tail (tail l))))
  );

  test "length after multiple cons" (fun () ->
    let l = cons 'a' (cons 'b' (cons 'c' (cons 'd' empty))) in
    assert (length l = 4)
  );

  (* -- of_list / to_list roundtrip -- *)
  test "of_list empty" (fun () ->
    assert (is_empty (of_list []))
  );

  test "of_list/to_list roundtrip" (fun () ->
    let xs = [1; 2; 3; 4; 5] in
    assert (to_list (of_list xs) = xs)
  );

  test "of_list/to_list large" (fun () ->
    let xs = List.init 100 (fun i -> i) in
    assert (to_list (of_list xs) = xs)
  );

  (* -- Lookup -- *)
  test "lookup each element" (fun () ->
    let l = of_list [10; 20; 30; 40; 50] in
    assert (lookup 0 l = 10);
    assert (lookup 1 l = 20);
    assert (lookup 2 l = 30);
    assert (lookup 3 l = 40);
    assert (lookup 4 l = 50)
  );

  test "lookup out of bounds" (fun () ->
    let l = of_list [1; 2; 3] in
    let raised = try ignore (lookup 3 l); false with _ -> true in
    assert raised
  );

  test "lookup_opt" (fun () ->
    let l = of_list [10; 20; 30] in
    assert (lookup_opt 1 l = Some 20);
    assert (lookup_opt 5 l = None)
  );

  test "lookup negative index" (fun () ->
    let l = of_list [1; 2] in
    let raised = try ignore (lookup (-1) l); false with _ -> true in
    assert raised
  );

  (* -- Update -- *)
  test "update element" (fun () ->
    let l = of_list [1; 2; 3; 4; 5] in
    let l' = update 2 99 l in
    assert (to_list l' = [1; 2; 99; 4; 5])
  );

  test "update preserves other elements" (fun () ->
    let l = of_list [10; 20; 30] in
    let l' = update 0 100 l in
    assert (lookup 0 l' = 100);
    assert (lookup 1 l' = 20);
    assert (lookup 2 l' = 30)
  );

  test "update out of bounds" (fun () ->
    let l = of_list [1] in
    let raised = try ignore (update 1 99 l); false with _ -> true in
    assert raised
  );

  test "original unchanged after update" (fun () ->
    let l = of_list [1; 2; 3] in
    let _ = update 1 99 l in
    assert (lookup 1 l = 2)
  );

  (* -- Map -- *)
  test "map" (fun () ->
    let l = of_list [1; 2; 3] in
    let l' = map (fun x -> x * 2) l in
    assert (to_list l' = [2; 4; 6])
  );

  test "map empty" (fun () ->
    let l : int t = map (fun x -> x + 1) empty in
    assert (is_empty l)
  );

  (* -- Fold -- *)
  test "fold_left sum" (fun () ->
    let l = of_list [1; 2; 3; 4; 5] in
    assert (fold_left ( + ) 0 l = 15)
  );

  test "fold_left order" (fun () ->
    let l = of_list [1; 2; 3] in
    let s = fold_left (fun acc x -> acc ^ string_of_int x) "" l in
    assert (s = "123")
  );

  test "fold_right" (fun () ->
    let l = of_list [1; 2; 3] in
    let s = fold_right (fun x acc -> string_of_int x ^ acc) l "" in
    assert (s = "123")
  );

  (* -- Iter -- *)
  test "iter" (fun () ->
    let l = of_list [1; 2; 3] in
    let buf = Buffer.create 8 in
    iter (fun x -> Buffer.add_string buf (string_of_int x)) l;
    assert (Buffer.contents buf = "123")
  );

  (* -- for_all / exists -- *)
  test "for_all true" (fun () ->
    let l = of_list [2; 4; 6] in
    assert (for_all (fun x -> x mod 2 = 0) l)
  );

  test "for_all false" (fun () ->
    let l = of_list [2; 3; 6] in
    assert (not (for_all (fun x -> x mod 2 = 0) l))
  );

  test "exists true" (fun () ->
    let l = of_list [1; 3; 4] in
    assert (exists (fun x -> x mod 2 = 0) l)
  );

  test "exists false" (fun () ->
    let l = of_list [1; 3; 5] in
    assert (not (exists (fun x -> x mod 2 = 0) l))
  );

  (* -- Filter -- *)
  test "filter" (fun () ->
    let l = of_list [1; 2; 3; 4; 5; 6] in
    let l' = filter (fun x -> x mod 2 = 0) l in
    assert (to_list l' = [2; 4; 6])
  );

  (* -- Find -- *)
  test "find_opt found" (fun () ->
    let l = of_list [1; 2; 3] in
    assert (find_opt (fun x -> x > 1) l = Some 2)
  );

  test "find_opt not found" (fun () ->
    let l = of_list [1; 2; 3] in
    assert (find_opt (fun x -> x > 10) l = None)
  );

  test "find_index" (fun () ->
    let l = of_list [10; 20; 30; 40] in
    assert (find_index (fun x -> x = 30) l = Some 2);
    assert (find_index (fun x -> x = 99) l = None)
  );

  (* -- Append -- *)
  test "append" (fun () ->
    let l1 = of_list [1; 2; 3] in
    let l2 = of_list [4; 5; 6] in
    assert (to_list (append l1 l2) = [1; 2; 3; 4; 5; 6])
  );

  test "append empty" (fun () ->
    let l = of_list [1; 2] in
    assert (to_list (append empty l) = [1; 2]);
    assert (to_list (append l empty) = [1; 2])
  );

  (* -- Rev -- *)
  test "rev" (fun () ->
    let l = of_list [1; 2; 3; 4] in
    assert (to_list (rev l) = [4; 3; 2; 1])
  );

  test "rev empty" (fun () ->
    assert (is_empty (rev empty))
  );

  (* -- Take / Drop / Split -- *)
  test "take" (fun () ->
    let l = of_list [1; 2; 3; 4; 5] in
    assert (to_list (take 3 l) = [1; 2; 3])
  );

  test "take 0" (fun () ->
    let l = of_list [1; 2] in
    assert (is_empty (take 0 l))
  );

  test "take more than length" (fun () ->
    let l = of_list [1; 2] in
    assert (to_list (take 5 l) = [1; 2])
  );

  test "drop" (fun () ->
    let l = of_list [1; 2; 3; 4; 5] in
    assert (to_list (drop 2 l) = [3; 4; 5])
  );

  test "drop 0" (fun () ->
    let l = of_list [1; 2] in
    assert (to_list (drop 0 l) = [1; 2])
  );

  test "split_at" (fun () ->
    let l = of_list [1; 2; 3; 4; 5] in
    let (a, b) = split_at 3 l in
    assert (to_list a = [1; 2; 3]);
    assert (to_list b = [4; 5])
  );

  (* -- Zip / Unzip -- *)
  test "zip" (fun () ->
    let l1 = of_list [1; 2; 3] in
    let l2 = of_list ["a"; "b"; "c"] in
    assert (to_list (zip l1 l2) = [(1,"a"); (2,"b"); (3,"c")])
  );

  test "unzip" (fun () ->
    let l = of_list [(1, "a"); (2, "b")] in
    let (a, b) = unzip l in
    assert (to_list a = [1; 2]);
    assert (to_list b = ["a"; "b"])
  );

  (* -- Mapi -- *)
  test "mapi" (fun () ->
    let l = of_list [10; 20; 30] in
    let l' = mapi (fun i x -> (i, x)) l in
    assert (to_list l' = [(0,10); (1,20); (2,30)])
  );

  (* -- nth -- *)
  test "nth alias" (fun () ->
    let l = of_list [5; 10; 15] in
    assert (nth l 1 = 10)
  );

  (* -- pp -- *)
  test "pp" (fun () ->
    let l = of_list [1; 2; 3] in
    assert (pp string_of_int l = "[1; 2; 3]")
  );

  test "pp empty" (fun () ->
    assert (pp string_of_int empty = "[]")
  );

  (* -- Structural properties -- *)
  test "tree_sizes skew-binary" (fun () ->
    (* 1 element: [1] *)
    let l1 = of_list [1] in
    assert (tree_sizes l1 = [1]);
    (* 2 elements: [1; 1] *)
    let l2 = of_list [1; 2] in
    assert (tree_sizes l2 = [1; 1]);
    (* 3 elements: merged into [3] *)
    let l3 = of_list [1; 2; 3] in
    assert (tree_sizes l3 = [3]);
    (* 4 elements: [1; 3] *)
    let l4 = of_list [1; 2; 3; 4] in
    assert (tree_sizes l4 = [1; 3])
  );

  test "num_trees" (fun () ->
    assert (num_trees empty = 0);
    assert (num_trees (of_list [1]) = 1);
    assert (num_trees (of_list [1;2;3]) = 1);
    assert (num_trees (of_list [1;2;3;4]) = 2)
  );

  (* -- Stress / larger data -- *)
  test "1000 elements roundtrip" (fun () ->
    let xs = List.init 1000 (fun i -> i) in
    let l = of_list xs in
    assert (length l = 1000);
    assert (to_list l = xs)
  );

  test "1000 elements random access" (fun () ->
    let l = of_list (List.init 1000 (fun i -> i * 3)) in
    assert (lookup 0 l = 0);
    assert (lookup 500 l = 1500);
    assert (lookup 999 l = 2997)
  );

  test "sequential cons matches of_list" (fun () ->
    let xs = [5; 4; 3; 2; 1] in
    let l1 = of_list xs in
    let l2 = cons 5 (cons 4 (cons 3 (cons 2 (cons 1 empty)))) in
    assert (to_list l1 = to_list l2)
  );

  test "multiple updates" (fun () ->
    let l = of_list [0; 0; 0; 0; 0] in
    let l = update 0 10 l in
    let l = update 2 30 l in
    let l = update 4 50 l in
    assert (to_list l = [10; 0; 30; 0; 50])
  );

  Printf.printf "\n%d passed, %d failed (of %d)\n\n"
    !pass !fail (!pass + !fail)
