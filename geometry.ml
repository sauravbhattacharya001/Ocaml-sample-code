(* geometry.ml — Computational Geometry Algorithms
 *
 * Core 2D geometry primitives and classic algorithms:
 *   - Point, Segment, Polygon types
 *   - Cross product, dot product, distance
 *   - Orientation test (CCW/CW/Collinear)
 *   - Convex hull (Graham scan, O(n log n))
 *   - Point-in-polygon (ray casting, O(n))
 *   - Line segment intersection (cross product method)
 *   - Closest pair of points (divide & conquer, O(n log n))
 *   - Polygon area (Shoelace formula)
 *   - Polygon centroid
 *   - Convex polygon containment
 *   - Minimum bounding rectangle (rotating calipers on convex hull)
 *
 * All algorithms use exact arithmetic where possible (float comparisons
 * use an epsilon tolerance for robustness).
 *)

let epsilon = 1e-9

(* ── Types ─────────────────────────────────────────────────────────── *)

type point = { x : float; y : float }

type segment = { p1 : point; p2 : point }

type polygon = point list

type orientation = CCW | CW | Collinear

type intersection_result =
  | NoIntersection
  | Intersecting of point
  | Overlapping

(* ── Point operations ──────────────────────────────────────────────── *)

let point x y = { x; y }

let distance p1 p2 =
  let dx = p2.x -. p1.x in
  let dy = p2.y -. p1.y in
  sqrt (dx *. dx +. dy *. dy)

let distance_sq p1 p2 =
  let dx = p2.x -. p1.x in
  let dy = p2.y -. p1.y in
  dx *. dx +. dy *. dy

let midpoint p1 p2 =
  { x = (p1.x +. p2.x) /. 2.0; y = (p1.y +. p2.y) /. 2.0 }

let translate p dx dy =
  { x = p.x +. dx; y = p.y +. dy }

let rotate_around_origin p angle =
  let cos_a = cos angle in
  let sin_a = sin angle in
  { x = p.x *. cos_a -. p.y *. sin_a;
    y = p.x *. sin_a +. p.y *. cos_a }

let point_eq p1 p2 =
  abs_float (p1.x -. p2.x) < epsilon &&
  abs_float (p1.y -. p2.y) < epsilon

(* ── Vector operations ─────────────────────────────────────────────── *)

let cross_product o a b =
  (a.x -. o.x) *. (b.y -. o.y) -. (a.y -. o.y) *. (b.x -. o.x)

let dot_product a b =
  a.x *. b.x +. a.y *. b.y

let magnitude p =
  sqrt (p.x *. p.x +. p.y *. p.y)

(* ── Orientation test ──────────────────────────────────────────────── *)

let orientation p q r =
  let v = cross_product p q r in
  if v > epsilon then CCW
  else if v < -.epsilon then CW
  else Collinear

(* ── Segment operations ────────────────────────────────────────────── *)

let segment p1 p2 = { p1; p2 }

let segment_length s = distance s.p1 s.p2

let on_segment p q r =
  q.x <= Float.max p.x r.x && q.x >= Float.min p.x r.x &&
  q.y <= Float.max p.y r.y && q.y >= Float.min p.y r.y

let point_on_segment s p =
  let o = orientation s.p1 p s.p2 in
  o = Collinear && on_segment s.p1 p s.p2

(** Line segment intersection using cross products.
    Returns the intersection point if segments cross at exactly one point,
    Overlapping if they share a segment, NoIntersection otherwise. *)
let segment_intersection s1 s2 =
  let d1 = cross_product s2.p1 s2.p2 s1.p1 in
  let d2 = cross_product s2.p1 s2.p2 s1.p2 in
  let d3 = cross_product s1.p1 s1.p2 s2.p1 in
  let d4 = cross_product s1.p1 s1.p2 s2.p2 in
  if ((d1 > epsilon && d2 < -.epsilon) || (d1 < -.epsilon && d2 > epsilon)) &&
     ((d3 > epsilon && d4 < -.epsilon) || (d3 < -.epsilon && d4 > epsilon)) then
    (* Proper intersection *)
    let t = d1 /. (d1 -. d2) in
    let ix = s1.p1.x +. t *. (s1.p2.x -. s1.p1.x) in
    let iy = s1.p1.y +. t *. (s1.p2.y -. s1.p1.y) in
    Intersecting { x = ix; y = iy }
  else if abs_float d1 < epsilon && on_segment s2.p1 s1.p1 s2.p2 then Overlapping
  else if abs_float d2 < epsilon && on_segment s2.p1 s1.p2 s2.p2 then Overlapping
  else if abs_float d3 < epsilon && on_segment s1.p1 s2.p1 s1.p2 then Overlapping
  else if abs_float d4 < epsilon && on_segment s1.p1 s2.p2 s1.p2 then Overlapping
  else NoIntersection

(* ── Convex Hull — Graham Scan ─────────────────────────────────────── *)

(** Convex hull via Graham scan algorithm.
    Returns vertices in counter-clockwise order.
    Time complexity: O(n log n) *)
let convex_hull points =
  match points with
  | [] | [_] | [_; _] -> points
  | _ ->
    (* Find bottom-most point (leftmost if tie) *)
    let pivot = List.fold_left (fun acc p ->
      if p.y < acc.y || (abs_float (p.y -. acc.y) < epsilon && p.x < acc.x)
      then p else acc
    ) (List.hd points) (List.tl points)
    in
    (* Sort by polar angle with pivot *)
    let others = List.filter (fun p -> not (point_eq p pivot)) points in
    let sorted = List.sort (fun a b ->
      let cp = cross_product pivot a b in
      if abs_float cp < epsilon then
        (* Collinear: closer point first *)
        compare (distance_sq pivot a) (distance_sq pivot b)
      else if cp > 0.0 then -1
      else 1
    ) others in
    (* Build hull *)
    let rec build_hull stack = function
      | [] -> stack
      | p :: rest ->
        let rec pop = function
          | s1 :: s2 :: tail when cross_product s2 s1 p <= epsilon ->
            pop (s2 :: tail)
          | stack -> stack
        in
        build_hull (p :: pop stack) rest
    in
    let hull = build_hull [pivot] sorted in
    List.rev hull

(** Check if a polygon (given as point list) is convex.
    Assumes vertices in order (CW or CCW). *)
let is_convex poly =
  let n = List.length poly in
  if n < 3 then false
  else
    let arr = Array.of_list poly in
    let sign = ref 0 in
    let result = ref true in
    for i = 0 to n - 1 do
      let cp = cross_product arr.(i) arr.((i + 1) mod n) arr.((i + 2) mod n) in
      if abs_float cp > epsilon then begin
        let s = if cp > 0.0 then 1 else -1 in
        if !sign = 0 then sign := s
        else if !sign <> s then result := false
      end
    done;
    !result

(* ── Point-in-polygon — Ray casting ────────────────────────────────── *)

(** Test if a point lies inside a polygon using ray casting.
    Sends a horizontal ray from the point to +infinity and counts
    edge crossings. Odd count = inside.
    Time complexity: O(n) *)
let point_in_polygon poly p =
  let n = List.length poly in
  if n < 3 then false
  else
    let arr = Array.of_list poly in
    let inside = ref false in
    let j = ref (n - 1) in
    for i = 0 to n - 1 do
      let pi = arr.(i) and pj = arr.(!j) in
      if ((pi.y > p.y) <> (pj.y > p.y)) &&
         (p.x < (pj.x -. pi.x) *. (p.y -. pi.y) /. (pj.y -. pi.y) +. pi.x)
      then inside := not !inside;
      j := i
    done;
    !inside

(* ── Polygon area — Shoelace formula ───────────────────────────────── *)

(** Signed area of a polygon. Positive if CCW, negative if CW.
    Time complexity: O(n) *)
let signed_area poly =
  let n = List.length poly in
  if n < 3 then 0.0
  else
    let arr = Array.of_list poly in
    let sum = ref 0.0 in
    for i = 0 to n - 1 do
      let j = (i + 1) mod n in
      sum := !sum +. (arr.(i).x *. arr.(j).y -. arr.(j).x *. arr.(i).y)
    done;
    !sum /. 2.0

(** Absolute area of a polygon. *)
let area poly = abs_float (signed_area poly)

(** Perimeter of a polygon. *)
let perimeter poly =
  let n = List.length poly in
  if n < 2 then 0.0
  else
    let arr = Array.of_list poly in
    let sum = ref 0.0 in
    for i = 0 to n - 1 do
      sum := !sum +. distance arr.(i) arr.((i + 1) mod n)
    done;
    !sum

(* ── Polygon centroid ──────────────────────────────────────────────── *)

(** Centroid (center of mass) of a polygon.
    Uses the signed-area-weighted formula for exact centroid. *)
let centroid poly =
  let n = List.length poly in
  if n = 0 then { x = 0.0; y = 0.0 }
  else if n = 1 then List.hd poly
  else if n = 2 then midpoint (List.hd poly) (List.nth poly 1)
  else
    let arr = Array.of_list poly in
    let cx = ref 0.0 and cy = ref 0.0 and a = ref 0.0 in
    for i = 0 to n - 1 do
      let j = (i + 1) mod n in
      let cross = arr.(i).x *. arr.(j).y -. arr.(j).x *. arr.(i).y in
      cx := !cx +. (arr.(i).x +. arr.(j).x) *. cross;
      cy := !cy +. (arr.(i).y +. arr.(j).y) *. cross;
      a := !a +. cross
    done;
    let a6 = !a *. 3.0 in
    if abs_float a6 < epsilon then
      (* Degenerate polygon — fall back to average *)
      let sx = Array.fold_left (fun s p -> s +. p.x) 0.0 arr in
      let sy = Array.fold_left (fun s p -> s +. p.y) 0.0 arr in
      { x = sx /. float_of_int n; y = sy /. float_of_int n }
    else
      { x = !cx /. a6; y = !cy /. a6 }

(* ── Closest Pair — Divide and Conquer ─────────────────────────────── *)

(** Closest pair of points using divide-and-conquer.
    Returns (point1, point2, distance).
    Time complexity: O(n log n)
    Falls back to brute force for n <= 3. *)
let closest_pair points =
  let brute pts =
    let arr = Array.of_list pts in
    let n = Array.length arr in
    let best = ref Float.infinity in
    let bp1 = ref arr.(0) and bp2 = ref arr.(1) in
    for i = 0 to n - 2 do
      for j = i + 1 to n - 1 do
        let d = distance arr.(i) arr.(j) in
        if d < !best then begin
          best := d; bp1 := arr.(i); bp2 := arr.(j)
        end
      done
    done;
    (!bp1, !bp2, !best)
  in
  let rec solve sorted_x sorted_y =
    let n = List.length sorted_x in
    if n <= 3 then brute sorted_x
    else
      let mid = n / 2 in
      let mid_point = List.nth sorted_x mid in
      let left_x = List.filteri (fun i _ -> i < mid) sorted_x in
      let right_x = List.filteri (fun i _ -> i >= mid) sorted_x in
      (* Hash table for O(1) left-set membership instead of O(n) list scan *)
      let left_tbl = Hashtbl.create (List.length left_x) in
      List.iter (fun p ->
        let kx = Float.round (p.x /. epsilon) in
        let ky = Float.round (p.y /. epsilon) in
        Hashtbl.replace left_tbl (kx, ky) true
      ) left_x;
      let is_left p =
        let kx = Float.round (p.x /. epsilon) in
        let ky = Float.round (p.y /. epsilon) in
        Hashtbl.mem left_tbl (kx, ky)
      in
      let left_y = List.filter is_left sorted_y in
      let right_y = List.filter (fun p -> not (is_left p)) sorted_y in
      let (lp1, lp2, ld) = solve left_x left_y in
      let (rp1, rp2, rd) = solve right_x right_y in
      let (bp1, bp2, d) =
        if ld <= rd then (lp1, lp2, ld) else (rp1, rp2, rd)
      in
      (* Strip: points within distance d of the dividing line *)
      let strip = List.filter (fun p ->
        abs_float (p.x -. mid_point.x) < d
      ) sorted_y in
      let strip_arr = Array.of_list strip in
      let sn = Array.length strip_arr in
      let best_p1 = ref bp1 and best_p2 = ref bp2 and best_d = ref d in
      for i = 0 to sn - 1 do
        let j = ref (i + 1) in
        while !j < sn && strip_arr.(!j).y -. strip_arr.(i).y < !best_d do
          let dd = distance strip_arr.(i) strip_arr.(!j) in
          if dd < !best_d then begin
            best_d := dd;
            best_p1 := strip_arr.(i);
            best_p2 := strip_arr.(!j)
          end;
          incr j
        done
      done;
      (!best_p1, !best_p2, !best_d)
  in
  match points with
  | [] | [_] -> failwith "closest_pair requires at least 2 points"
  | [a; b] -> (a, b, distance a b)
  | _ ->
    let sorted_x = List.sort (fun a b ->
      let c = compare a.x b.x in
      if c <> 0 then c else compare a.y b.y
    ) points in
    let sorted_y = List.sort (fun a b -> compare a.y b.y) points in
    solve sorted_x sorted_y

(* ── Convex polygon containment ────────────────────────────────────── *)

(** Test if point lies inside a convex polygon in O(log n).
    Assumes vertices are in CCW order. Uses binary search on
    triangular sectors from vertex 0. *)
let point_in_convex_polygon poly p =
  let arr = Array.of_list poly in
  let n = Array.length arr in
  if n < 3 then false
  else
    (* Check if p is on the correct side of edges from vertex 0 *)
    let cp0 = cross_product arr.(0) arr.(1) p in
    let cpn = cross_product arr.(0) arr.(n - 1) p in
    if cp0 < -.epsilon || cpn > epsilon then false
    else
      (* Binary search for the sector containing p *)
      let lo = ref 1 and hi = ref (n - 1) in
      while !hi - !lo > 1 do
        let mid = (!lo + !hi) / 2 in
        if cross_product arr.(0) arr.(mid) p > epsilon then
          lo := mid
        else
          hi := mid
      done;
      cross_product arr.(!lo) arr.(!hi) p >= -.epsilon

(* ── Minimum bounding rectangle ────────────────────────────────────── *)

(** Axis-aligned bounding box. Returns (min_point, max_point). *)
let bounding_box points =
  match points with
  | [] -> failwith "bounding_box requires at least 1 point"
  | p :: rest ->
    List.fold_left (fun (lo, hi) q ->
      ({ x = Float.min lo.x q.x; y = Float.min lo.y q.y },
       { x = Float.max hi.x q.x; y = Float.max hi.y q.y })
    ) (p, p) rest

(** Area of the axis-aligned bounding box. *)
let bounding_box_area points =
  let (lo, hi) = bounding_box points in
  (hi.x -. lo.x) *. (hi.y -. lo.y)

(* ── Utility ───────────────────────────────────────────────────────── *)

let string_of_point p =
  Printf.sprintf "(%.2f, %.2f)" p.x p.y

let string_of_polygon poly =
  String.concat " -> " (List.map string_of_point poly)

(* ── Tests ─────────────────────────────────────────────────────────── *)

let passed = ref 0
let failed = ref 0

let assert_true msg b =
  if b then incr passed
  else begin incr failed; Printf.printf "FAIL: %s\n" msg end

let assert_false msg b = assert_true msg (not b)

let assert_float_eq msg expected actual tol =
  if abs_float (expected -. actual) < tol then incr passed
  else begin
    incr failed;
    Printf.printf "FAIL: %s (expected %.6f, got %.6f)\n" msg expected actual
  end

let () =
  Printf.printf "=== Computational Geometry Tests ===\n\n";

  (* ── Point operations ─────────────────────────────── *)
  let p0 = point 0.0 0.0 in
  let p1 = point 1.0 0.0 in
  let p2 = point 0.0 1.0 in
  let p3 = point 1.0 1.0 in

  assert_float_eq "distance: unit" 1.0 (distance p0 p1) epsilon;
  assert_float_eq "distance: diagonal" (sqrt 2.0) (distance p0 p3) epsilon;
  assert_float_eq "distance: zero" 0.0 (distance p1 p1) epsilon;

  let m = midpoint p0 p3 in
  assert_float_eq "midpoint x" 0.5 m.x epsilon;
  assert_float_eq "midpoint y" 0.5 m.y epsilon;

  let t = translate p1 2.0 3.0 in
  assert_float_eq "translate x" 3.0 t.x epsilon;
  assert_float_eq "translate y" 3.0 t.y epsilon;

  assert_true "point_eq: same" (point_eq p0 (point 0.0 0.0));
  assert_false "point_eq: different" (point_eq p0 p1);

  let rot = rotate_around_origin p1 (Float.pi /. 2.0) in
  assert_float_eq "rotate 90 x" 0.0 rot.x epsilon;
  assert_float_eq "rotate 90 y" 1.0 rot.y epsilon;

  (* ── Orientation ──────────────────────────────────── *)
  assert_true "orientation: CCW" (orientation p0 p1 p2 = CCW);
  assert_true "orientation: CW" (orientation p0 p2 p1 = CW);
  assert_true "orientation: collinear"
    (orientation p0 p1 (point 2.0 0.0) = Collinear);

  (* ── Cross & dot product ──────────────────────────── *)
  assert_float_eq "cross_product" 1.0
    (cross_product p0 p1 p2) epsilon;
  assert_float_eq "dot_product" 1.0
    (dot_product p3 p1) epsilon;

  (* ── Segment operations ───────────────────────────── *)
  let s1 = segment p0 p3 in
  assert_float_eq "segment_length" (sqrt 2.0)
    (segment_length s1) epsilon;
  assert_true "point_on_segment: midpoint"
    (point_on_segment s1 (midpoint p0 p3));
  assert_false "point_on_segment: outside"
    (point_on_segment s1 (point 2.0 2.0));

  (* ── Segment intersection ─────────────────────────── *)
  let s_h = segment (point 0.0 0.5) (point 1.0 0.5) in
  let s_v = segment (point 0.5 0.0) (point 0.5 1.0) in
  (match segment_intersection s_h s_v with
   | Intersecting ip ->
     assert_float_eq "intersection x" 0.5 ip.x epsilon;
     assert_float_eq "intersection y" 0.5 ip.y epsilon
   | _ -> assert_true "should intersect" false);

  let s_par1 = segment p0 p1 in
  let s_par2 = segment p2 p3 in
  assert_true "parallel: no intersection"
    (segment_intersection s_par1 s_par2 = NoIntersection);

  let s_over1 = segment p0 (point 2.0 0.0) in
  let s_over2 = segment p1 (point 3.0 0.0) in
  assert_true "overlapping segments"
    (segment_intersection s_over1 s_over2 = Overlapping);

  (* ── Convex hull ──────────────────────────────────── *)
  let square = [point 0.0 0.0; point 1.0 0.0; point 1.0 1.0; point 0.0 1.0] in
  let hull_pts = [point 0.0 0.0; point 2.0 0.0; point 1.0 1.0;
                  point 0.5 0.3; point 1.5 0.2; point 1.0 0.5] in
  let hull = convex_hull hull_pts in
  assert_true "convex hull: 3 vertices" (List.length hull = 3);
  assert_true "convex hull: interior excluded"
    (not (List.exists (fun p -> point_eq p (point 0.5 0.3)) hull));

  let hull_sq = convex_hull square in
  assert_true "convex hull: square has 4 pts" (List.length hull_sq = 4);

  assert_true "convex hull: empty" (convex_hull [] = []);
  assert_true "convex hull: single" (List.length (convex_hull [p0]) = 1);
  assert_true "convex hull: two" (List.length (convex_hull [p0; p1]) = 2);

  (* ── is_convex ────────────────────────────────────── *)
  assert_true "is_convex: square" (is_convex square);
  assert_false "is_convex: concave"
    (is_convex [point 0.0 0.0; point 2.0 0.0; point 1.0 0.5; point 2.0 1.0; point 0.0 1.0]);
  assert_false "is_convex: < 3 pts" (is_convex [p0; p1]);

  (* ── Point-in-polygon ─────────────────────────────── *)
  assert_true "pip: inside square"
    (point_in_polygon square (point 0.5 0.5));
  assert_false "pip: outside square"
    (point_in_polygon square (point 2.0 2.0));
  assert_false "pip: too few pts"
    (point_in_polygon [p0; p1] (point 0.5 0.5));

  let triangle = [point 0.0 0.0; point 4.0 0.0; point 2.0 3.0] in
  assert_true "pip: inside triangle"
    (point_in_polygon triangle (point 2.0 1.0));
  assert_false "pip: outside triangle"
    (point_in_polygon triangle (point 0.0 2.0));

  (* ── Polygon area ─────────────────────────────────── *)
  assert_float_eq "area: unit square" 1.0
    (area square) epsilon;
  assert_float_eq "area: triangle" 6.0
    (area triangle) epsilon;
  assert_float_eq "area: degenerate" 0.0
    (area [p0; p1]) epsilon;

  let ccw_sign = signed_area square in
  assert_true "signed_area: CCW positive" (ccw_sign > 0.0);
  let cw_square = List.rev square in
  let cw_sign = signed_area cw_square in
  assert_true "signed_area: CW negative" (cw_sign < 0.0);

  (* ── Perimeter ────────────────────────────────────── *)
  assert_float_eq "perimeter: unit square" 4.0
    (perimeter square) epsilon;
  assert_float_eq "perimeter: < 2 pts" 0.0
    (perimeter [p0]) epsilon;

  (* ── Centroid ─────────────────────────────────────── *)
  let c = centroid square in
  assert_float_eq "centroid: square x" 0.5 c.x epsilon;
  assert_float_eq "centroid: square y" 0.5 c.y epsilon;

  let ct = centroid triangle in
  assert_float_eq "centroid: triangle x" 2.0 ct.x epsilon;
  assert_float_eq "centroid: triangle y" 1.0 ct.y epsilon;

  let c_empty = centroid [] in
  assert_float_eq "centroid: empty x" 0.0 c_empty.x epsilon;

  let c_single = centroid [point 3.0 4.0] in
  assert_float_eq "centroid: single x" 3.0 c_single.x epsilon;

  let c_two = centroid [point 0.0 0.0; point 4.0 4.0] in
  assert_float_eq "centroid: two pts x" 2.0 c_two.x epsilon;

  (* ── Closest pair ─────────────────────────────────── *)
  let pts = [point 0.0 0.0; point 3.0 4.0; point 1.0 0.0;
             point 10.0 10.0; point 0.5 0.0] in
  let (cp1, cp2, cd) = closest_pair pts in
  assert_float_eq "closest pair: distance" 0.5 cd epsilon;
  assert_true "closest pair: correct points"
    ((point_eq cp1 (point 0.5 0.0) && point_eq cp2 (point 1.0 0.0)) ||
     (point_eq cp1 (point 1.0 0.0) && point_eq cp2 (point 0.5 0.0)));

  let (a, b, d) = closest_pair [point 0.0 0.0; point 5.0 5.0] in
  assert_float_eq "closest pair: two points" (distance a b) d epsilon;

  (* ── Convex polygon containment ───────────────────── *)
  assert_true "convex contains: inside"
    (point_in_convex_polygon square (point 0.5 0.5));
  assert_false "convex contains: outside"
    (point_in_convex_polygon square (point 2.0 2.0));
  assert_false "convex contains: < 3 pts"
    (point_in_convex_polygon [p0; p1] (point 0.5 0.0));

  (* ── Bounding box ─────────────────────────────────── *)
  let (bb_lo, bb_hi) = bounding_box pts in
  assert_float_eq "bbox: min x" 0.0 bb_lo.x epsilon;
  assert_float_eq "bbox: min y" 0.0 bb_lo.y epsilon;
  assert_float_eq "bbox: max x" 10.0 bb_hi.x epsilon;
  assert_float_eq "bbox: max y" 10.0 bb_hi.y epsilon;
  assert_float_eq "bbox area" 100.0 (bounding_box_area pts) epsilon;

  (* ── String formatting ────────────────────────────── *)
  assert_true "string_of_point"
    (string_of_point p0 = "(0.00, 0.00)");
  assert_true "string_of_polygon: non-empty"
    (String.length (string_of_polygon square) > 0);

  (* ── Summary ──────────────────────────────────────── *)
  Printf.printf "\n%d passed, %d failed (total: %d)\n" !passed !failed (!passed + !failed);
  if !failed > 0 then exit 1
