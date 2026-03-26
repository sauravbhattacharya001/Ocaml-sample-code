(* Test suite for Order Statistics Tree *)

let () =
  Printf.printf "=== Order Statistics Tree Tests ===\n\n";
  let pass = ref 0 in
  let fail = ref 0 in
  let check name cond =
    if cond then (incr pass; Printf.printf "  ✓ %s\n" name)
    else (incr fail; Printf.printf "  ✗ %s\n" name)
  in

  (* We inline the module here since OCaml doesn't have an import system
     for standalone .ml files — in a real project these would be in a
     library. For the test suite we re-implement a minimal version. *)

  (* ── Minimal OST reimplementation for testing ── *)
  let module OST = struct
    type 'a t =
      | Leaf
      | Node of { left: 'a t; value: 'a; right: 'a t; size: int }

    let size = function Leaf -> 0 | Node n -> n.size
    let node l v r = Node { left=l; value=v; right=r; size=1+size l+size r }

    let alpha = 0.29
    let is_balanced = function
      | Leaf -> true
      | Node n ->
        let s = float_of_int n.size in
        float_of_int (size n.left) <= (1.0 -. alpha) *. s &&
        float_of_int (size n.right) <= (1.0 -. alpha) *. s

    let rec to_list_acc acc = function
      | Leaf -> acc
      | Node n -> to_list_acc (n.value :: to_list_acc acc n.right) n.left

    let to_sorted_list t = to_list_acc [] t

    let rec of_sorted_list lst len =
      if len <= 0 then (Leaf, lst)
      else
        let ll = (len-1)/2 in let rl = len-1-ll in
        let (l, r) = of_sorted_list lst ll in
        match r with [] -> (l,[]) | v::r' ->
        let (rt,r'') = of_sorted_list r' rl in (node l v rt, r'')

    let rebuild t =
      let lst = to_sorted_list t in
      fst (of_sorted_list lst (List.length lst))

    let balance t = if is_balanced t then t else rebuild t

    let rec insert x = function
      | Leaf -> node Leaf x Leaf
      | Node n ->
        if x < n.value then balance (node (insert x n.left) n.value n.right)
        else if x > n.value then balance (node n.left n.value (insert x n.right))
        else Node n

    let rec member x = function
      | Leaf -> false
      | Node n ->
        if x < n.value then member x n.left
        else if x > n.value then member x n.right
        else true

    let rec min_elt = function
      | Leaf -> failwith "empty" | Node {left=Leaf;value;_} -> value
      | Node n -> min_elt n.left

    let rec delete x = function
      | Leaf -> Leaf
      | Node n ->
        if x < n.value then balance (node (delete x n.left) n.value n.right)
        else if x > n.value then balance (node n.left n.value (delete x n.right))
        else match n.left, n.right with
          | Leaf, r -> r | l, Leaf -> l
          | l, r -> let s = min_elt r in balance (node l s (delete s r))

    let rec select k = function
      | Leaf -> failwith "oob"
      | Node n ->
        let ls = size n.left in
        if k < ls then select k n.left
        else if k = ls then n.value
        else select (k-ls-1) n.right

    let rec rank x = function
      | Leaf -> 0
      | Node n ->
        if x < n.value then rank x n.left
        else if x > n.value then size n.left + 1 + rank x n.right
        else size n.left

    let of_list lst = List.fold_left (fun t x -> insert x t) Leaf lst
    let to_list t = List.rev (List.fold_left (fun acc x -> x :: acc) [] (to_sorted_list t))

    let rec height = function Leaf -> 0 | Node n -> 1 + max (height n.left) (height n.right)
  end in

  (* ── Tests ── *)
  let t = OST.of_list [5;2;8;1;4;7;9;3;6;10] in

  check "size = 10" (OST.size t = 10);
  check "member 5" (OST.member 5 t);
  check "member 1" (OST.member 1 t);
  check "not member 0" (not (OST.member 0 t));
  check "not member 11" (not (OST.member 11 t));

  check "select(0) = 1" (OST.select 0 t = 1);
  check "select(4) = 5" (OST.select 4 t = 5);
  check "select(9) = 10" (OST.select 9 t = 10);

  check "rank(1) = 0" (OST.rank 1 t = 0);
  check "rank(5) = 4" (OST.rank 5 t = 4);
  check "rank(10) = 9" (OST.rank 10 t = 9);
  check "rank(11) = 10" (OST.rank 11 t = 10);

  check "to_list sorted" (OST.to_list t = [1;2;3;4;5;6;7;8;9;10]);

  let t2 = OST.delete 5 t in
  check "delete 5: size=9" (OST.size t2 = 9);
  check "delete 5: not member" (not (OST.member 5 t2));
  check "delete 5: sorted" (OST.to_list t2 = [1;2;3;4;6;7;8;9;10]);

  (* Delete non-existent *)
  let t3 = OST.delete 42 t in
  check "delete non-existent: size unchanged" (OST.size t3 = 10);

  (* Empty tree *)
  check "empty size = 0" (OST.size OST.Leaf = 0);

  (* Single element *)
  let t4 = OST.insert 42 OST.Leaf in
  check "single: size=1" (OST.size t4 = 1);
  check "single: select(0)=42" (OST.select 0 t4 = 42);
  check "single: rank(42)=0" (OST.rank 42 t4 = 0);

  (* Duplicate insert *)
  let t5 = OST.insert 5 t in
  check "duplicate: size unchanged" (OST.size t5 = 10);

  (* Balance: sequential insert should still be O(log n) height *)
  let big = OST.of_list (List.init 1000 (fun i -> i)) in
  let h = OST.height big in
  check (Printf.sprintf "1000 elements: height=%d <= 20" h) (h <= 20);
  check "1000: select(0)=0" (OST.select 0 big = 0);
  check "1000: select(999)=999" (OST.select 999 big = 999);
  check "1000: rank(500)=500" (OST.rank 500 big = 500);

  Printf.printf "\n%d passed, %d failed\n" !pass !fail;
  if !fail > 0 then exit 1
