(* Tests for AA Tree *)

let () = Printf.printf "Running AA Tree tests...\n"

(* We'll inline the AA tree module for testing since OCaml files
   in this repo are standalone *)

type 'a tree =
  | Leaf
  | Node of { level: int; left: 'a tree; value: 'a; right: 'a tree }

let level = function
  | Leaf -> 0
  | Node n -> n.level

let skew = function
  | Node ({ left = Node l; _ } as t) when l.level = t.level ->
    Node { l with right = Node { t with left = l.right } }
  | t -> t

let split = function
  | Node ({ right = Node ({ right = Node rr; _ } as r); _ } as t)
    when t.level = rr.level ->
    Node { r with level = r.level + 1;
                  left = Node { t with right = r.left } }
  | t -> t

let rec insert x = function
  | Leaf -> Node { level = 1; left = Leaf; value = x; right = Leaf }
  | Node n ->
    let node =
      if x < n.value then Node { n with left = insert x n.left }
      else if x > n.value then Node { n with right = insert x n.right }
      else Node n
    in
    node |> skew |> split

let rec mem x = function
  | Leaf -> false
  | Node n ->
    if x < n.value then mem x n.left
    else if x > n.value then mem x n.right
    else true

let rec min_value = function
  | Leaf -> failwith "min_value: empty tree"
  | Node { left = Leaf; value; _ } -> value
  | Node { left; _ } -> min_value left

let rec max_value = function
  | Leaf -> failwith "max_value: empty tree"
  | Node { right = Leaf; value; _ } -> value
  | Node { right; _ } -> max_value right

let decrease_level = function
  | Node n ->
    let should_be = min (level n.left) (level n.right) + 1 in
    if should_be < n.level then
      let right' = match n.right with
        | Node r when should_be < r.level -> Node { r with level = should_be }
        | r -> r
      in
      Node { n with level = should_be; right = right' }
  | t -> t

let rec delete x = function
  | Leaf -> Leaf
  | Node n ->
    let node =
      if x < n.value then Node { n with left = delete x n.left }
      else if x > n.value then Node { n with right = delete x n.right }
      else
        match n.left, n.right with
        | Leaf, Leaf -> Leaf
        | Leaf, _ ->
          let s = min_value n.right in
          Node { n with value = s; right = delete s n.right }
        | _, _ ->
          let p = max_value n.left in
          Node { n with value = p; left = delete p n.left }
    in
    node |> decrease_level |> skew
    |> (function
      | Node n -> Node { n with right = skew n.right } |> (function
        | Node n -> Node { n with right = match n.right with
            | Node r -> Node { r with right = skew r.right } | t -> t }
        | t -> t)
      | t -> t)
    |> split
    |> (function
      | Node n -> Node { n with right = split n.right }
      | t -> t)

let rec to_list = function
  | Leaf -> []
  | Node n -> to_list n.left @ [n.value] @ to_list n.right

let of_list xs = List.fold_left (fun t x -> insert x t) Leaf xs

let rec size = function
  | Leaf -> 0
  | Node n -> 1 + size n.left + size n.right

let is_empty = function Leaf -> true | Node _ -> false

let rec validate = function
  | Leaf -> true
  | Node n ->
    level n.left = n.level - 1
    && (level n.right = n.level || level n.right = n.level - 1)
    && (match n.right with Node r -> level r.right < n.level | Leaf -> true)
    && validate n.left && validate n.right

(* Test helpers *)
let tests_passed = ref 0
let tests_failed = ref 0

let assert_true msg b =
  if b then (incr tests_passed; Printf.printf "  ✓ %s\n" msg)
  else (incr tests_failed; Printf.printf "  ✗ %s\n" msg)

let assert_equal msg expected actual =
  assert_true (Printf.sprintf "%s (expected %s)" msg expected) (expected = actual)

let () =
  Printf.printf "\n--- Empty tree ---\n";
  assert_true "empty tree is empty" (is_empty Leaf);
  assert_true "empty tree has size 0" (size Leaf = 0);
  assert_true "empty tree is valid" (validate Leaf);
  
  Printf.printf "\n--- Insertion ---\n";
  let t = of_list [5; 3; 7; 1; 4; 6; 8; 2; 9; 0] in
  assert_true "size is 10" (size t = 10);
  assert_true "valid after insertions" (validate t);
  assert_equal "sorted order" "0 1 2 3 4 5 6 7 8 9"
    (String.concat " " (List.map string_of_int (to_list t)));
  
  Printf.printf "\n--- Membership ---\n";
  List.iter (fun x ->
    assert_true (Printf.sprintf "contains %d" x) (mem x t)
  ) [0; 1; 2; 3; 4; 5; 6; 7; 8; 9];
  assert_true "does not contain 10" (not (mem 10 t));
  assert_true "does not contain -1" (not (mem (-1) t));
  
  Printf.printf "\n--- Min/Max ---\n";
  assert_true "min is 0" (min_value t = 0);
  assert_true "max is 9" (max_value t = 9);
  
  Printf.printf "\n--- Deletion ---\n";
  let t2 = delete 5 t in
  assert_true "size after deleting 5" (size t2 = 9);
  assert_true "5 not present" (not (mem 5 t2));
  assert_true "valid after delete 5" (validate t2);
  
  let t3 = t2 |> delete 0 |> delete 9 in
  assert_true "size after deleting min+max" (size t3 = 7);
  assert_true "valid after deleting min+max" (validate t3);
  
  (* Delete all *)
  let t4 = List.fold_left (fun t x -> delete x t) t [0;1;2;3;4;5;6;7;8;9] in
  assert_true "empty after deleting all" (is_empty t4);
  
  Printf.printf "\n--- Duplicates ---\n";
  let t5 = of_list [3; 3; 3; 1; 1] in
  assert_true "duplicates ignored, size=2" (size t5 = 2);
  
  Printf.printf "\n--- Large tree ---\n";
  let big = of_list (List.init 100 (fun i -> i)) in
  assert_true "100-element tree valid" (validate big);
  assert_true "100-element tree size" (size big = 100);
  
  let big2 = List.fold_left (fun t i -> if i mod 2 = 0 then delete i t else t) big (List.init 100 (fun i -> i)) in
  assert_true "after deleting evens, valid" (validate big2);
  assert_true "after deleting evens, size=50" (size big2 = 50);
  
  Printf.printf "\n=== Results: %d passed, %d failed ===\n" !tests_passed !tests_failed;
  if !tests_failed > 0 then exit 1
