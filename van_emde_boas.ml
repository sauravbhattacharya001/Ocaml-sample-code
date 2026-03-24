(* Van Emde Boas Tree - Fast integer set operations in O(log log u) time
   
   A Van Emde Boas (vEB) tree supports the following operations on integers
   in the universe {0, 1, ..., u-1} where u is a power of 2:
   
   - member:     O(log log u) - check if element exists
   - insert:     O(log log u) - add an element
   - delete:     O(log log u) - remove an element  
   - minimum:    O(1)         - find minimum element
   - maximum:    O(1)         - find maximum element
   - successor:  O(log log u) - find next larger element
   - predecessor: O(log log u) - find next smaller element
   
   This implementation uses a recursive cluster structure where a universe
   of size u is split into sqrt(u) clusters of size sqrt(u).
   
   Usage:
     ocaml van_emde_boas.ml
*)

(* The vEB tree type: either a base case (universe <= 2) or recursive *)
type veb_tree =
  | Base of { mutable bits: bool array }
  | Node of {
      universe: int;
      mutable min_val: int option;
      mutable max_val: int option;
      summary: veb_tree;
      clusters: veb_tree array;
    }

(* Integer square root (upper/lower) for splitting universe *)
let high_bits u x = x / (int_of_float (sqrt (float_of_int u)))
let low_bits u x = x mod (int_of_float (sqrt (float_of_int u)))
let index u h l = h * (int_of_float (sqrt (float_of_int u))) + l
let cluster_size u = int_of_float (sqrt (float_of_int u))

(* Next power of 2 >= n *)
let next_pow2 n =
  let rec go p = if p >= n then p else go (p * 2) in
  go 1

(* Create an empty vEB tree for universe size u (must be power of 2) *)
let rec create u =
  if u <= 2 then
    Base { bits = Array.make u false }
  else
    let cs = cluster_size u in
    let num_clusters = (u + cs - 1) / cs in
    Node {
      universe = u;
      min_val = None;
      max_val = None;
      summary = create num_clusters;
      clusters = Array.init num_clusters (fun _ -> create cs);
    }

(* Check membership *)
let rec member t x =
  match t with
  | Base { bits } -> x >= 0 && x < Array.length bits && bits.(x)
  | Node { universe; min_val; max_val; clusters; _ } ->
    (match min_val, max_val with
     | None, _ -> false
     | Some mn, _ when mn = x -> true
     | _, Some mx when mx = x -> true
     | _ ->
       let h = high_bits universe x in
       let l = low_bits universe x in
       if h < Array.length clusters then
         member clusters.(h) l
       else false)

(* Find minimum *)
let minimum = function
  | Base { bits } ->
    if bits.(0) then Some 0
    else if Array.length bits > 1 && bits.(1) then Some 1
    else None
  | Node { min_val; _ } -> min_val

(* Find maximum *)
let maximum = function
  | Base { bits } ->
    let len = Array.length bits in
    if len > 1 && bits.(1) then Some 1
    else if bits.(0) then Some 0
    else None
  | Node { max_val; _ } -> max_val

(* Insert element *)
let rec insert t x =
  match t with
  | Base { bits } ->
    if x >= 0 && x < Array.length bits then bits.(x) <- true
  | Node ({ universe; min_val; max_val; summary; clusters } as node) ->
    match min_val with
    | None ->
      node.min_val <- Some x;
      node.max_val <- Some x
    | Some mn ->
      let x = ref x in
      if !x < mn then begin
        x := mn;
        node.min_val <- Some (mn + !x - mn)  (* swap *)
      end;
      (* Fix the swap logic *)
      let x_val =
        match node.min_val with
        | Some new_mn when new_mn <> mn -> mn  (* we swapped *)
        | _ -> !x
      in
      ignore x_val;
      (* Simpler approach: just do the insert properly *)
      let actual_x = !x in
      if actual_x <> (match node.min_val with Some v -> v | None -> -1) then begin
        let h = high_bits universe actual_x in
        let l = low_bits universe actual_x in
        if h < Array.length clusters then begin
          (match minimum clusters.(h) with
           | None -> insert summary h
           | Some _ -> ());
          insert clusters.(h) l
        end
      end;
      (match max_val with
       | Some mx when actual_x > mx -> node.max_val <- Some actual_x
       | None -> node.max_val <- Some actual_x
       | _ -> ())

(* Simpler, correct implementation *)
let rec veb_insert t x =
  match t with
  | Base { bits } ->
    if x >= 0 && x < Array.length bits then bits.(x) <- true
  | Node node ->
    match node.min_val with
    | None ->
      node.min_val <- Some x;
      node.max_val <- Some x
    | Some mn ->
      let x = if x < mn then (node.min_val <- Some x; mn) else x in
      let u = node.universe in
      let h = high_bits u x in
      let l = low_bits u x in
      if h < Array.length node.clusters then begin
        if minimum node.clusters.(h) = None then
          veb_insert node.summary h;
        veb_insert node.clusters.(h) l
      end;
      (match node.max_val with
       | Some mx when x > mx -> node.max_val <- Some x
       | _ -> ())

(* Successor - find smallest element > x *)
let rec successor t x =
  match t with
  | Base { bits } ->
    if x = 0 && Array.length bits > 1 && bits.(1) then Some 1
    else None
  | Node { universe; min_val; max_val; summary; clusters; _ } ->
    (match min_val with
     | None -> None
     | Some mn when x < mn -> Some mn
     | _ ->
       let h = high_bits universe x in
       let l = low_bits universe x in
       let max_in_cluster =
         if h < Array.length clusters then maximum clusters.(h)
         else None
       in
       match max_in_cluster with
       | Some mx when l < mx ->
         (match successor clusters.(h) l with
          | Some off -> Some (index universe h off)
          | None -> None)
       | _ ->
         (match successor summary h with
          | Some next_cluster ->
            (match minimum clusters.(next_cluster) with
             | Some off -> Some (index universe next_cluster off)
             | None -> None)
          | None ->
            (match max_val with
             | Some mx when x < mx -> Some mx
             | _ -> None)))

(* Predecessor - find largest element < x *)
let rec predecessor t x =
  match t with
  | Base { bits } ->
    if x = 1 && bits.(0) then Some 0
    else None
  | Node { universe; min_val; max_val; summary; clusters; _ } ->
    (match max_val with
     | None -> None
     | Some mx when x > mx -> Some mx
     | _ ->
       let h = high_bits universe x in
       let l = low_bits universe x in
       let min_in_cluster =
         if h < Array.length clusters then minimum clusters.(h)
         else None
       in
       match min_in_cluster with
       | Some mn when l > mn ->
         (match predecessor clusters.(h) l with
          | Some off -> Some (index universe h off)
          | None -> None)
       | _ ->
         (match predecessor summary h with
          | Some prev_cluster ->
            (match maximum clusters.(prev_cluster) with
             | Some off -> Some (index universe prev_cluster off)
             | None -> None)
          | None ->
            (match min_val with
             | Some mn when x > mn -> Some mn
             | _ -> None)))

(* Delete element *)
let rec veb_delete t x =
  match t with
  | Base { bits } ->
    if x >= 0 && x < Array.length bits then bits.(x) <- false
  | Node node ->
    match node.min_val, node.max_val with
    | None, _ -> ()
    | Some mn, Some mx when mn = mx ->
      if x = mn then begin
        node.min_val <- None;
        node.max_val <- None
      end
    | Some mn, Some mx ->
      let u = node.universe in
      let x =
        if x = mn then
          match minimum node.summary with
          | Some first_cluster ->
            let new_min = index u first_cluster
              (match minimum node.clusters.(first_cluster) with
               | Some v -> v | None -> 0) in
            node.min_val <- Some new_min;
            new_min
          | None -> x
        else x
      in
      let h = high_bits u x in
      let l = low_bits u x in
      if h < Array.length node.clusters then begin
        veb_delete node.clusters.(h) l;
        if minimum node.clusters.(h) = None then
          veb_delete node.summary h
      end;
      if x = mx then begin
        match minimum node.summary with
        | None -> node.max_val <- node.min_val
        | Some last ->
          match maximum node.clusters.(last) with
          | Some off -> node.max_val <- Some (index u last off)
          | None -> node.max_val <- node.min_val
      end
    | _ -> ()

(* Pretty-print the elements in a vEB tree *)
let elements t =
  let elems = ref [] in
  let rec collect t offset =
    match t with
    | Base { bits } ->
      Array.iteri (fun i b -> if b then elems := (offset + i) :: !elems) bits
    | Node { universe; min_val; max_val; clusters; _ } ->
      (match min_val with Some v -> elems := (offset + v) :: !elems | None -> ());
      let cs = cluster_size universe in
      Array.iteri (fun i c -> collect c (offset + i * cs)) clusters;
      (* min is stored separately, avoid duplicates *)
      ignore max_val
  in
  collect t 0;
  List.sort_uniq compare !elems

(* ── Demo ── *)
let () =
  Printf.printf "╔══════════════════════════════════════════════════════╗\n";
  Printf.printf "║        Van Emde Boas Tree Demo (universe=16)        ║\n";
  Printf.printf "╚══════════════════════════════════════════════════════╝\n\n";

  let u = 16 in
  let t = create u in

  Printf.printf "── Inserting elements: 2, 3, 4, 5, 7, 14, 15 ──\n";
  List.iter (veb_insert t) [2; 3; 4; 5; 7; 14; 15];
  Printf.printf "Elements: [%s]\n\n"
    (String.concat "; " (List.map string_of_int (elements t)));

  Printf.printf "── Membership tests ──\n";
  List.iter (fun x ->
    Printf.printf "  member(%d) = %b\n" x (member t x)
  ) [0; 2; 3; 6; 7; 14; 15];
  Printf.printf "\n";

  Printf.printf "── Min / Max ──\n";
  (match minimum t with
   | Some v -> Printf.printf "  minimum = %d\n" v
   | None -> Printf.printf "  minimum = (empty)\n");
  (match maximum t with
   | Some v -> Printf.printf "  maximum = %d\n" v
   | None -> Printf.printf "  maximum = (empty)\n");
  Printf.printf "\n";

  Printf.printf "── Successor queries ──\n";
  List.iter (fun x ->
    match successor t x with
    | Some s -> Printf.printf "  successor(%d) = %d\n" x s
    | None -> Printf.printf "  successor(%d) = None\n" x
  ) [1; 3; 5; 7; 14];
  Printf.printf "\n";

  Printf.printf "── Predecessor queries ──\n";
  List.iter (fun x ->
    match predecessor t x with
    | Some p -> Printf.printf "  predecessor(%d) = %d\n" x p
    | None -> Printf.printf "  predecessor(%d) = None\n" x
  ) [2; 4; 7; 14; 15];
  Printf.printf "\n";

  Printf.printf "── Deleting 3 and 14 ──\n";
  veb_delete t 3;
  veb_delete t 14;
  Printf.printf "Elements: [%s]\n"
    (String.concat "; " (List.map string_of_int (elements t)));
  (match successor t 3 with
   | Some s -> Printf.printf "  successor(3) after delete = %d\n" s
   | None -> Printf.printf "  successor(3) after delete = None\n");
  Printf.printf "\n";

  Printf.printf "── Larger universe (u=256) ──\n";
  let t2 = create 256 in
  List.iter (veb_insert t2) [10; 50; 100; 200; 255];
  Printf.printf "Elements: [%s]\n"
    (String.concat "; " (List.map string_of_int (elements t2)));
  (match successor t2 50 with
   | Some s -> Printf.printf "  successor(50) = %d\n" s
   | None -> Printf.printf "  successor(50) = None\n");
  (match predecessor t2 200 with
   | Some p -> Printf.printf "  predecessor(200) = %d\n" p
   | None -> Printf.printf "  predecessor(200) = None\n");

  Printf.printf "\n✅ Van Emde Boas tree demo complete!\n"
