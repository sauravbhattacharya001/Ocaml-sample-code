(* Quadtree — spatial partitioning for 2D point data          *)
(* Supports insert, search, range query, k-nearest-neighbors *)
(* Demonstrates: algebraic data types, recursive subdivision, *)
(* spatial indexing, and functional data structure design      *)

(* ── Point and bounding box types ────────────────────────── *)

type point = { x: float; y: float }

type bounds = {
  cx: float;   (* center x *)
  cy: float;   (* center y *)
  half: float; (* half-width/height (square region) *)
}

let point x y = { x; y }

let bounds cx cy half = { cx; cy; half }

let contains b p =
  p.x >= b.cx -. b.half && p.x < b.cx +. b.half &&
  p.y >= b.cy -. b.half && p.y < b.cy +. b.half

let intersects b1 b2 =
  not (b1.cx -. b1.half >= b2.cx +. b2.half ||
       b1.cx +. b1.half <= b2.cx -. b2.half ||
       b1.cy -. b1.half >= b2.cy +. b2.half ||
       b1.cy +. b1.half <= b2.cy -. b2.half)

let distance_sq p1 p2 =
  let dx = p1.x -. p2.x in
  let dy = p1.y -. p2.y in
  dx *. dx +. dy *. dy

(* ── Quadtree type ───────────────────────────────────────── *)

type 'a entry = { pt: point; data: 'a }

type 'a t =
  | Empty of bounds
  | Leaf of bounds * 'a entry list
  | Node of bounds * 'a t * 'a t * 'a t * 'a t  (* NW, NE, SW, SE *)

let capacity = 4  (* max entries per leaf before splitting *)

let create b = Empty b

(* ── Subdivision ─────────────────────────────────────────── *)

let subdivide b =
  let q = b.half /. 2.0 in
  let nw = { cx = b.cx -. q; cy = b.cy -. q; half = q } in
  let ne = { cx = b.cx +. q; cy = b.cy -. q; half = q } in
  let sw = { cx = b.cx -. q; cy = b.cy +. q; half = q } in
  let se = { cx = b.cx +. q; cy = b.cy +. q; half = q } in
  (nw, ne, sw, se)

(* ── Insert ──────────────────────────────────────────────── *)

let rec insert t entry =
  let b = get_bounds t in
  if not (contains b entry.pt) then t  (* point outside bounds *)
  else match t with
  | Empty b ->
    Leaf (b, [entry])
  | Leaf (b, entries) when List.length entries < capacity ->
    Leaf (b, entry :: entries)
  | Leaf (b, entries) ->
    (* Split and redistribute *)
    let (nw, ne, sw, se) = subdivide b in
    let node = Node (b, Empty nw, Empty ne, Empty sw, Empty se) in
    List.fold_left (fun acc e -> insert acc e) (insert node entry) entries
  | Node (b, nw, ne, sw, se) ->
    let (bnw, bne, bsw, bse) = subdivide b in
    if contains bnw entry.pt then Node (b, insert nw entry, ne, sw, se)
    else if contains bne entry.pt then Node (b, nw, insert ne entry, sw, se)
    else if contains bsw entry.pt then Node (b, nw, ne, insert sw entry, se)
    else Node (b, nw, ne, sw, insert se entry)

and get_bounds = function
  | Empty b | Leaf (b, _) | Node (b, _, _, _, _) -> b

(* ── Convenience insert ──────────────────────────────────── *)

let insert_point t x y data =
  insert t { pt = point x y; data }

(* ── Range query: find all points within a rectangular area  *)

let rec query_range t range acc =
  let b = get_bounds t in
  if not (intersects b range) then acc
  else match t with
  | Empty _ -> acc
  | Leaf (_, entries) ->
    List.fold_left (fun acc e ->
      if contains range e.pt then e :: acc else acc
    ) acc entries
  | Node (_, nw, ne, sw, se) ->
    acc
    |> query_range nw range
    |> query_range ne range
    |> query_range sw range
    |> query_range se range

let find_in_range t range =
  query_range t range [] |> List.rev

(* ── Count points in range ───────────────────────────────── *)

let rec count_range t range =
  let b = get_bounds t in
  if not (intersects b range) then 0
  else match t with
  | Empty _ -> 0
  | Leaf (_, entries) ->
    List.fold_left (fun n e ->
      if contains range e.pt then n + 1 else n
    ) 0 entries
  | Node (_, nw, ne, sw, se) ->
    count_range nw range + count_range ne range +
    count_range sw range + count_range se range

(* ── Find nearest neighbor ───────────────────────────────── *)

let nearest_neighbor t target =
  let best = ref None in
  let best_dist = ref infinity in
  let rec search = function
    | Empty _ -> ()
    | Leaf (_, entries) ->
      List.iter (fun e ->
        let d = distance_sq target e.pt in
        if d < !best_dist then begin
          best_dist := d;
          best := Some e
        end
      ) entries
    | Node (b, nw, ne, sw, se) ->
      (* Prune: closest possible point in this quad *)
      let clamped_x = max (b.cx -. b.half) (min (b.cx +. b.half) target.x) in
      let clamped_y = max (b.cy -. b.half) (min (b.cy +. b.half) target.y) in
      let min_dist = distance_sq target { x = clamped_x; y = clamped_y } in
      if min_dist < !best_dist then begin
        search nw; search ne; search sw; search se
      end
  in
  search t;
  !best

(* ── K-nearest neighbors ────────────────────────────────── *)

(* Simple sorted-list based KNN; practical for moderate k *)
let k_nearest t target k =
  let all = query_range t (get_bounds t) [] in
  let with_dist = List.map (fun e -> (distance_sq target e.pt, e)) all in
  let sorted = List.sort (fun (d1, _) (d2, _) -> compare d1 d2) with_dist in
  let rec take n = function
    | [] -> []
    | _ when n = 0 -> []
    | (_, e) :: rest -> e :: take (n - 1) rest
  in
  take k sorted

(* ── Total size ──────────────────────────────────────────── *)

let rec size = function
  | Empty _ -> 0
  | Leaf (_, entries) -> List.length entries
  | Node (_, nw, ne, sw, se) ->
    size nw + size ne + size sw + size se

(* ── Depth ───────────────────────────────────────────────── *)

let rec depth = function
  | Empty _ -> 0
  | Leaf _ -> 1
  | Node (_, nw, ne, sw, se) ->
    1 + max (max (depth nw) (depth ne)) (max (depth sw) (depth se))

(* ── Fold over all entries ───────────────────────────────── *)

let rec fold f acc = function
  | Empty _ -> acc
  | Leaf (_, entries) -> List.fold_left (fun a e -> f a e) acc entries
  | Node (_, nw, ne, sw, se) ->
    acc |> fold f |> (fun a -> fold f a nw)
        |> (fun a -> fold f a ne)
        |> (fun a -> fold f a sw)
        |> (fun a -> fold f a se)

(* Correct fold that actually visits entries *)
let fold f acc t =
  let rec go acc = function
    | Empty _ -> acc
    | Leaf (_, entries) -> List.fold_left (fun a e -> f a e) acc entries
    | Node (_, nw, ne, sw, se) ->
      acc |> (fun a -> go a nw) |> (fun a -> go a ne)
          |> (fun a -> go a sw) |> (fun a -> go a se)
  in
  go acc t

(* ── To list ─────────────────────────────────────────────── *)

let to_list t =
  fold (fun acc e -> e :: acc) [] t |> List.rev

(* ── Remove point ────────────────────────────────────────── *)

let rec remove t target =
  match t with
  | Empty b -> Empty b
  | Leaf (b, entries) ->
    let entries' = List.filter (fun e ->
      not (e.pt.x = target.x && e.pt.y = target.y)
    ) entries in
    if entries' = [] then Empty b else Leaf (b, entries')
  | Node (b, nw, ne, sw, se) ->
    let nw' = remove nw target in
    let ne' = remove ne target in
    let sw' = remove sw target in
    let se' = remove se target in
    (* Collapse to leaf or empty if children are all small *)
    let total = size nw' + size ne' + size sw' + size se' in
    if total = 0 then Empty b
    else if total <= capacity then
      let entries = to_list (Node (b, nw', ne', sw', se')) in
      Leaf (b, entries)
    else Node (b, nw', ne', sw', se')

(* ── Pretty-print for debugging ──────────────────────────── *)

let rec pp_tree indent = function
  | Empty b ->
    Printf.printf "%sEmpty [%.1f,%.1f ±%.1f]\n" indent b.cx b.cy b.half
  | Leaf (b, entries) ->
    Printf.printf "%sLeaf [%.1f,%.1f ±%.1f] (%d pts)\n"
      indent b.cx b.cy b.half (List.length entries);
    List.iter (fun e ->
      Printf.printf "%s  (%.2f, %.2f)\n" indent e.pt.x e.pt.y
    ) entries
  | Node (b, nw, ne, sw, se) ->
    Printf.printf "%sNode [%.1f,%.1f ±%.1f]\n" indent b.cx b.cy b.half;
    let ind = indent ^ "  " in
    pp_tree ind nw; pp_tree ind ne; pp_tree ind sw; pp_tree ind se

let print t = pp_tree "" t

(* ── Demo ────────────────────────────────────────────────── *)

let () =
  Printf.printf "=== Quadtree Demo ===\n\n";

  (* Create a quadtree covering [0,100] x [0,100] *)
  let world = bounds 50.0 50.0 50.0 in
  let qt = create world in

  (* Insert some cities (approximate coordinates) *)
  let cities = [
    (47.6, 22.4, "Seattle");
    (37.8, 27.6, "San Francisco");
    (34.1, 31.7, "Los Angeles");
    (40.7, 25.9, "New York");
    (41.9, 12.5, "Rome");
    (48.9, 2.3, "Paris");
    (51.5, 0.1, "London");
    (35.7, 39.8, "Tokyo");
    (55.8, 37.6, "Moscow");
    (22.3, 14.1, "Mumbai");
  ] in

  let qt = List.fold_left (fun t (x, y, name) ->
    insert_point t x y name
  ) qt cities in

  Printf.printf "Inserted %d cities\n" (size qt);
  Printf.printf "Tree depth: %d\n\n" (depth qt);

  (* Range query: find cities in a region *)
  let search_area = bounds 42.0 20.0 12.0 in
  let found = find_in_range qt search_area in
  Printf.printf "Cities in range [%.0f-%.0f, %.0f-%.0f]:\n"
    (search_area.cx -. search_area.half) (search_area.cx +. search_area.half)
    (search_area.cy -. search_area.half) (search_area.cy +. search_area.half);
  List.iter (fun e ->
    Printf.printf "  %s (%.1f, %.1f)\n" e.data e.pt.x e.pt.y
  ) found;

  (* Nearest neighbor *)
  let target = point 45.0 20.0 in
  Printf.printf "\nNearest city to (%.1f, %.1f): " target.x target.y;
  (match nearest_neighbor qt target with
   | Some e -> Printf.printf "%s (%.1f, %.1f)\n" e.data e.pt.x e.pt.y
   | None -> Printf.printf "none\n");

  (* K-nearest *)
  let k3 = k_nearest qt target 3 in
  Printf.printf "\n3 nearest cities to (%.1f, %.1f):\n" target.x target.y;
  List.iter (fun e ->
    Printf.printf "  %s (%.1f, %.1f) dist=%.2f\n"
      e.data e.pt.x e.pt.y (sqrt (distance_sq target e.pt))
  ) k3;

  (* Count in range *)
  let full_range = bounds 50.0 50.0 50.0 in
  Printf.printf "\nTotal points in world: %d\n" (count_range qt full_range);

  (* Remove a point *)
  let qt' = remove qt (point 41.9 12.5) in
  Printf.printf "After removing Rome: %d cities\n" (size qt');

  (* Print tree structure *)
  Printf.printf "\nTree structure:\n";
  print qt';

  Printf.printf "\n=== Quadtree demo complete ===\n"
