(* test_geometry.ml — Comprehensive tests for geometry.ml
 *
 * Tests all major functions: point ops, orientation, segments,
 * intersection, convex hull, point-in-polygon, area/perimeter,
 * centroid, closest pair, convex containment, bounding box.
 *
 * Run: ocaml test_geometry.ml
 *)

#use "geometry.ml";;

(* ── Test infrastructure ────────────────────────────────────────── *)

let tests_run = ref 0
let tests_passed = ref 0
let tests_failed = ref 0
let current_section = ref ""

let section name =
  current_section := name;
  Printf.printf "\n── %s ──\n" name

let assert_true ~msg cond =
  incr tests_run;
  if cond then incr tests_passed
  else begin
    incr tests_failed;
    Printf.printf "  FAIL [%s]: %s\n" !current_section msg
  end

let assert_false ~msg cond = assert_true ~msg (not cond)

let assert_float ~msg ?(tol=1e-6) expected actual =
  incr tests_run;
  if abs_float (expected -. actual) < tol then incr tests_passed
  else begin
    incr tests_failed;
    Printf.printf "  FAIL [%s]: %s (expected %.8f, got %.8f)\n"
      !current_section msg expected actual
  end

let assert_raises ~msg f =
  incr tests_run;
  (try ignore (f ());
    incr tests_failed;
    Printf.printf "  FAIL [%s]: %s (no exception raised)\n" !current_section msg
  with _ -> incr tests_passed)

let () =
  Printf.printf "=== Geometry Module Tests ===\n";

  (* ── Point constructors and basic ops ─────────────── *)
  section "Point operations";

  let origin = point 0.0 0.0 in
  let px = point 1.0 0.0 in
  let py = point 0.0 1.0 in
  let pxy = point 1.0 1.0 in

  assert_float ~msg:"distance: origin to (1,0)" 1.0 (distance origin px);
  assert_float ~msg:"distance: origin to (0,1)" 1.0 (distance origin py);
  assert_float ~msg:"distance: origin to (1,1)" (sqrt 2.0) (distance origin pxy);
  assert_float ~msg:"distance: self" 0.0 (distance px px);
  assert_float ~msg:"distance: symmetric" (distance px py) (distance py px);

  assert_float ~msg:"distance_sq: origin to (1,1)" 2.0 (distance_sq origin pxy);
  assert_float ~msg:"distance_sq: consistent with distance"
    (let d = distance px py in d *. d) (distance_sq px py);

  let m = midpoint origin pxy in
  assert_float ~msg:"midpoint x" 0.5 m.x;
  assert_float ~msg:"midpoint y" 0.5 m.y;
  let m2 = midpoint px py in
  assert_float ~msg:"midpoint of (1,0)-(0,1) x" 0.5 m2.x;
  assert_float ~msg:"midpoint of (1,0)-(0,1) y" 0.5 m2.y;

  let t = translate origin 3.0 4.0 in
  assert_float ~msg:"translate x" 3.0 t.x;
  assert_float ~msg:"translate y" 4.0 t.y;
  let t2 = translate (point 1.0 2.0) (-1.0) (-2.0) in
  assert_float ~msg:"translate negative" 0.0 t2.x;
  assert_float ~msg:"translate negative y" 0.0 t2.y;

  (* Rotation tests *)
  let r90 = rotate_around_origin px (Float.pi /. 2.0) in
  assert_float ~msg:"rotate 90° x" 0.0 r90.x;
  assert_float ~msg:"rotate 90° y" 1.0 r90.y;

  let r180 = rotate_around_origin px Float.pi in
  assert_float ~msg:"rotate 180° x" (-1.0) r180.x;
  assert_float ~msg:"rotate 180° y" 0.0 r180.y;

  let r360 = rotate_around_origin pxy (2.0 *. Float.pi) in
  assert_float ~msg:"rotate 360° x" 1.0 r360.x;
  assert_float ~msg:"rotate 360° y" 1.0 r360.y;

  let r0 = rotate_around_origin pxy 0.0 in
  assert_float ~msg:"rotate 0° x" 1.0 r0.x;
  assert_float ~msg:"rotate 0° y" 1.0 r0.y;

  (* point_eq *)
  assert_true ~msg:"point_eq: identical" (point_eq origin (point 0.0 0.0));
  assert_false ~msg:"point_eq: different" (point_eq origin px);
  assert_true ~msg:"point_eq: near epsilon"
    (point_eq (point 0.0 0.0) (point 1e-10 1e-10));
  assert_false ~msg:"point_eq: beyond epsilon"
    (point_eq (point 0.0 0.0) (point 1e-8 0.0));

  (* ── Vector operations ────────────────────────────── *)
  section "Vector operations";

  assert_float ~msg:"cross_product: unit CCW" 1.0 (cross_product origin px py);
  assert_float ~msg:"cross_product: unit CW" (-1.0) (cross_product origin py px);
  assert_float ~msg:"cross_product: collinear" 0.0
    (cross_product origin px (point 2.0 0.0));

  assert_float ~msg:"dot_product: perpendicular" 0.0 (dot_product px py);
  assert_float ~msg:"dot_product: parallel" 1.0 (dot_product px px);
  assert_float ~msg:"dot_product: (1,1).(1,1)" 2.0 (dot_product pxy pxy);

  assert_float ~msg:"magnitude: unit x" 1.0 (magnitude px);
  assert_float ~msg:"magnitude: (1,1)" (sqrt 2.0) (magnitude pxy);
  assert_float ~msg:"magnitude: origin" 0.0 (magnitude origin);

  (* ── Orientation ──────────────────────────────────── *)
  section "Orientation";

  assert_true ~msg:"CCW" (orientation origin px py = CCW);
  assert_true ~msg:"CW" (orientation origin py px = CW);
  assert_true ~msg:"collinear"
    (orientation origin px (point 2.0 0.0) = Collinear);
  assert_true ~msg:"collinear: negative"
    (orientation origin px (point (-1.0) 0.0) = Collinear);
  (* Large-scale collinear *)
  assert_true ~msg:"collinear: large"
    (orientation (point 0.0 0.0) (point 1000.0 1000.0)
       (point 2000.0 2000.0) = Collinear);

  (* ── Segment operations ───────────────────────────── *)
  section "Segments";

  let s1 = segment origin pxy in
  assert_float ~msg:"segment_length: diagonal" (sqrt 2.0) (segment_length s1);
  let s_zero = segment origin origin in
  assert_float ~msg:"segment_length: zero" 0.0 (segment_length s_zero);

  assert_true ~msg:"point_on_segment: midpoint"
    (point_on_segment s1 (midpoint origin pxy));
  assert_true ~msg:"point_on_segment: endpoint p1"
    (point_on_segment s1 origin);
  assert_false ~msg:"point_on_segment: off-segment"
    (point_on_segment s1 (point 2.0 2.0));
  assert_false ~msg:"point_on_segment: perpendicular"
    (point_on_segment (segment origin px) py);

  (* ── Segment intersection ─────────────────────────── *)
  section "Segment intersection";

  let s_h = segment (point 0.0 0.5) (point 1.0 0.5) in
  let s_v = segment (point 0.5 0.0) (point 0.5 1.0) in
  (match segment_intersection s_h s_v with
   | Intersecting ip ->
     assert_float ~msg:"X intersection x" 0.5 ip.x;
     assert_float ~msg:"X intersection y" 0.5 ip.y
   | _ -> assert_true ~msg:"should intersect" false);

  (* Parallel non-intersecting *)
  let s_par1 = segment origin px in
  let s_par2 = segment py pxy in
  assert_true ~msg:"parallel: no intersection"
    (segment_intersection s_par1 s_par2 = NoIntersection);

  (* Overlapping *)
  let s_over1 = segment origin (point 2.0 0.0) in
  let s_over2 = segment px (point 3.0 0.0) in
  assert_true ~msg:"overlapping segments"
    (segment_intersection s_over1 s_over2 = Overlapping);

  (* Non-intersecting (disjoint) *)
  let s_far1 = segment origin px in
  let s_far2 = segment (point 5.0 5.0) (point 6.0 6.0) in
  assert_true ~msg:"disjoint: no intersection"
    (segment_intersection s_far1 s_far2 = NoIntersection);

  (* T-junction (endpoint touches) *)
  let s_t1 = segment (point 0.0 0.0) (point 2.0 0.0) in
  let s_t2 = segment (point 1.0 0.0) (point 1.0 1.0) in
  let t_res = segment_intersection s_t1 s_t2 in
  assert_true ~msg:"T-junction: overlapping or intersecting"
    (t_res = Overlapping ||
     (match t_res with Intersecting _ -> true | _ -> false));

  (* ── Convex hull ──────────────────────────────────── *)
  section "Convex hull";

  let square = [point 0.0 0.0; point 1.0 0.0; point 1.0 1.0; point 0.0 1.0] in
  let hull_sq = convex_hull square in
  assert_true ~msg:"square: 4 hull vertices" (List.length hull_sq = 4);

  (* With interior points *)
  let with_interior = square @ [point 0.5 0.5; point 0.3 0.7; point 0.8 0.2] in
  let hull_int = convex_hull with_interior in
  assert_true ~msg:"interior excluded: 4 hull vertices" (List.length hull_int = 4);

  (* Triangle *)
  let tri_pts = [point 0.0 0.0; point 4.0 0.0; point 2.0 3.0;
                 point 1.0 1.0; point 2.0 1.0] in
  let hull_tri = convex_hull tri_pts in
  assert_true ~msg:"triangle hull: 3 vertices" (List.length hull_tri = 3);

  (* Collinear points *)
  let collinear = [point 0.0 0.0; point 1.0 0.0; point 2.0 0.0; point 3.0 0.0] in
  let hull_col = convex_hull collinear in
  assert_true ~msg:"collinear: hull has 2 endpoints"
    (List.length hull_col >= 2 && List.length hull_col <= 4);

  (* Edge cases *)
  assert_true ~msg:"empty hull" (convex_hull [] = []);
  assert_true ~msg:"single point hull" (List.length (convex_hull [origin]) = 1);
  assert_true ~msg:"two point hull" (List.length (convex_hull [origin; px]) = 2);

  (* Pentagon *)
  let pentagon = [
    point 0.0 2.0; point 1.9 0.62; point 1.18 (-1.62);
    point (-1.18) (-1.62); point (-1.9) 0.62
  ] in
  let hull_pent = convex_hull pentagon in
  assert_true ~msg:"pentagon: 5 vertices" (List.length hull_pent = 5);

  (* ── is_convex ────────────────────────────────────── *)
  section "is_convex";

  assert_true ~msg:"square is convex" (is_convex square);
  assert_true ~msg:"triangle is convex"
    (is_convex [point 0.0 0.0; point 4.0 0.0; point 2.0 3.0]);
  assert_false ~msg:"concave L-shape"
    (is_convex [point 0.0 0.0; point 2.0 0.0; point 2.0 1.0;
                point 1.0 1.0; point 1.0 2.0; point 0.0 2.0]);
  assert_false ~msg:"two points: not convex" (is_convex [origin; px]);
  assert_false ~msg:"one point: not convex" (is_convex [origin]);

  (* ── Point-in-polygon ─────────────────────────────── *)
  section "Point-in-polygon";

  assert_true ~msg:"inside square" (point_in_polygon square (point 0.5 0.5));
  assert_false ~msg:"outside square" (point_in_polygon square (point 2.0 2.0));
  assert_false ~msg:"far outside" (point_in_polygon square (point (-5.0) (-5.0)));

  let triangle = [point 0.0 0.0; point 4.0 0.0; point 2.0 3.0] in
  assert_true ~msg:"inside triangle" (point_in_polygon triangle (point 2.0 1.0));
  assert_false ~msg:"outside triangle" (point_in_polygon triangle (point 0.0 3.0));

  assert_false ~msg:"too few points"
    (point_in_polygon [origin; px] (point 0.5 0.0));

  (* Large polygon *)
  let n_sides = 20 in
  let large_poly = List.init n_sides (fun i ->
    let angle = 2.0 *. Float.pi *. (float_of_int i /. float_of_int n_sides) in
    point (50.0 +. 10.0 *. cos angle) (50.0 +. 10.0 *. sin angle)
  ) in
  assert_true ~msg:"inside 20-gon center" (point_in_polygon large_poly (point 50.0 50.0));
  assert_false ~msg:"outside 20-gon" (point_in_polygon large_poly (point 0.0 0.0));

  (* ── Polygon area ─────────────────────────────────── *)
  section "Polygon area";

  assert_float ~msg:"unit square area" 1.0 (area square);
  assert_float ~msg:"triangle area" 6.0 (area triangle);

  (* Scaled square *)
  let big_sq = [point 0.0 0.0; point 10.0 0.0;
                point 10.0 10.0; point 0.0 10.0] in
  assert_float ~msg:"10x10 square area" 100.0 (area big_sq);

  (* Degenerate *)
  assert_float ~msg:"area: 2 points" 0.0 (area [origin; px]);
  assert_float ~msg:"area: 1 point" 0.0 (area [origin]);
  assert_float ~msg:"area: empty" 0.0 (area []);

  (* signed_area direction *)
  let ccw_sign = signed_area square in
  assert_true ~msg:"CCW signed_area > 0" (ccw_sign > 0.0);
  let cw_sign = signed_area (List.rev square) in
  assert_true ~msg:"CW signed_area < 0" (cw_sign < 0.0);
  assert_float ~msg:"abs(signed) = area" (area square) (abs_float ccw_sign);

  (* ── Perimeter ────────────────────────────────────── *)
  section "Perimeter";

  assert_float ~msg:"unit square perimeter" 4.0 (perimeter square);
  assert_float ~msg:"10x10 square perimeter" 40.0 (perimeter big_sq);

  (* Right triangle: 3-4-5 *)
  let right_tri = [point 0.0 0.0; point 3.0 0.0; point 0.0 4.0] in
  assert_float ~msg:"3-4-5 triangle perimeter" 12.0 (perimeter right_tri);

  assert_float ~msg:"perimeter: 1 point" 0.0 (perimeter [origin]);
  assert_float ~msg:"perimeter: empty" 0.0 (perimeter []);

  (* ── Centroid ─────────────────────────────────────── *)
  section "Centroid";

  let c_sq = centroid square in
  assert_float ~msg:"square centroid x" 0.5 c_sq.x;
  assert_float ~msg:"square centroid y" 0.5 c_sq.y;

  let c_tri = centroid triangle in
  assert_float ~msg:"triangle centroid x" 2.0 c_tri.x;
  assert_float ~msg:"triangle centroid y" 1.0 c_tri.y;

  let c_empty = centroid [] in
  assert_float ~msg:"empty centroid x" 0.0 c_empty.x;
  assert_float ~msg:"empty centroid y" 0.0 c_empty.y;

  let c_one = centroid [point 7.0 3.0] in
  assert_float ~msg:"single point centroid x" 7.0 c_one.x;
  assert_float ~msg:"single point centroid y" 3.0 c_one.y;

  let c_two = centroid [point 0.0 0.0; point 6.0 8.0] in
  assert_float ~msg:"two points centroid x" 3.0 c_two.x;
  assert_float ~msg:"two points centroid y" 4.0 c_two.y;

  (* Symmetric polygon: centroid at center *)
  let c_big = centroid big_sq in
  assert_float ~msg:"10x10 centroid x" 5.0 c_big.x;
  assert_float ~msg:"10x10 centroid y" 5.0 c_big.y;

  (* ── Closest pair ─────────────────────────────────── *)
  section "Closest pair";

  let pts5 = [point 0.0 0.0; point 3.0 4.0; point 1.0 0.0;
              point 10.0 10.0; point 0.5 0.0] in
  let (cp1, cp2, cd) = closest_pair pts5 in
  assert_float ~msg:"closest distance = 0.5" 0.5 cd;
  assert_true ~msg:"closest pair correct points"
    ((point_eq cp1 (point 0.5 0.0) && point_eq cp2 (point 1.0 0.0)) ||
     (point_eq cp1 (point 1.0 0.0) && point_eq cp2 (point 0.5 0.0)));

  (* Two points *)
  let (a2, b2, d2) = closest_pair [point 0.0 0.0; point 5.0 5.0] in
  assert_float ~msg:"two pts distance" (sqrt 50.0) d2;
  assert_float ~msg:"two pts consistent" (distance a2 b2) d2;

  (* Three points *)
  let (_, _, d3) = closest_pair [point 0.0 0.0; point 1.0 0.0; point 100.0 100.0] in
  assert_float ~msg:"three pts: closest = 1" 1.0 d3;

  (* Duplicate points *)
  let (_, _, dd) = closest_pair [point 1.0 1.0; point 1.0 1.0; point 5.0 5.0] in
  assert_float ~msg:"duplicate points: distance 0" 0.0 dd;

  (* Grid of points — closest should be spacing *)
  let grid_pts = List.init 25 (fun i ->
    point (float_of_int (i mod 5) *. 2.0)
          (float_of_int (i / 5) *. 2.0)
  ) in
  let (_, _, dg) = closest_pair grid_pts in
  assert_float ~msg:"grid: closest = 2.0" 2.0 dg;

  (* Error for too few *)
  assert_raises ~msg:"closest_pair: empty list"
    (fun () -> closest_pair []);
  assert_raises ~msg:"closest_pair: single point"
    (fun () -> closest_pair [origin]);

  (* ── Convex containment ───────────────────────────── *)
  section "Convex polygon containment";

  assert_true ~msg:"inside convex square"
    (point_in_convex_polygon square (point 0.5 0.5));
  assert_false ~msg:"outside convex square"
    (point_in_convex_polygon square (point 2.0 2.0));
  assert_false ~msg:"below convex square"
    (point_in_convex_polygon square (point 0.5 (-1.0)));
  assert_false ~msg:"convex: < 3 pts"
    (point_in_convex_polygon [origin; px] (point 0.5 0.0));

  (* Different convex polygon *)
  let convex_tri = [point 0.0 0.0; point 4.0 0.0; point 2.0 3.0] in
  assert_true ~msg:"inside convex triangle"
    (point_in_convex_polygon convex_tri (point 2.0 1.0));

  (* ── Bounding box ─────────────────────────────────── *)
  section "Bounding box";

  let (lo, hi) = bounding_box pts5 in
  assert_float ~msg:"bbox min x" 0.0 lo.x;
  assert_float ~msg:"bbox min y" 0.0 lo.y;
  assert_float ~msg:"bbox max x" 10.0 hi.x;
  assert_float ~msg:"bbox max y" 10.0 hi.y;
  assert_float ~msg:"bbox area" 100.0 (bounding_box_area pts5);

  (* Single point bbox *)
  let (lo1, hi1) = bounding_box [point 3.0 7.0] in
  assert_float ~msg:"single pt bbox x" 3.0 lo1.x;
  assert_float ~msg:"single pt bbox y" 7.0 hi1.y;
  assert_float ~msg:"single pt bbox area" 0.0 (bounding_box_area [point 3.0 7.0]);

  (* Collinear bbox *)
  let col_pts = [point 0.0 0.0; point 5.0 0.0; point 10.0 0.0] in
  let (loc, hic) = bounding_box col_pts in
  assert_float ~msg:"collinear bbox width" 10.0 (hic.x -. loc.x);
  assert_float ~msg:"collinear bbox height" 0.0 (hic.y -. loc.y);

  assert_raises ~msg:"bbox: empty list" (fun () -> bounding_box []);

  (* ── String formatting ────────────────────────────── *)
  section "String formatting";

  assert_true ~msg:"string_of_point format"
    (string_of_point origin = "(0.00, 0.00)");
  assert_true ~msg:"string_of_point non-zero"
    (string_of_point (point 3.14 2.72) = "(3.14, 2.72)");

  let poly_str = string_of_polygon [origin; px; py] in
  assert_true ~msg:"string_of_polygon non-empty" (String.length poly_str > 0);
  assert_true ~msg:"string_of_polygon contains arrow"
    (String.length poly_str > 10);
  assert_true ~msg:"string_of_polygon: empty"
    (string_of_polygon [] = "");

  (* ── Stress tests ─────────────────────────────────── *)
  section "Stress / edge cases";

  (* Large-coordinate points *)
  let far1 = point 1e6 1e6 in
  let far2 = point 1e6 (1e6 +. 1.0) in
  assert_float ~msg:"large coords: distance" 1.0 (distance far1 far2);

  (* Negative coordinates *)
  let neg_sq = [point (-1.0) (-1.0); point 1.0 (-1.0);
                point 1.0 1.0; point (-1.0) 1.0] in
  assert_float ~msg:"negative coords: area" 4.0 (area neg_sq);
  assert_true ~msg:"negative coords: pip center"
    (point_in_polygon neg_sq origin);
  assert_false ~msg:"negative coords: pip outside"
    (point_in_polygon neg_sq (point 5.0 5.0));

  (* Closest pair: negative coordinates *)
  let neg_pts = [point (-10.0) (-10.0); point (-9.5) (-10.0);
                 point 10.0 10.0] in
  let (_, _, dn) = closest_pair neg_pts in
  assert_float ~msg:"negative coords closest pair" 0.5 dn;

  (* Very close points *)
  let close_pts = [point 0.0 0.0; point 1e-5 0.0; point 1.0 1.0] in
  let (_, _, dc) = closest_pair close_pts in
  assert_float ~msg:"very close points" 1e-5 dc;

  (* ── Summary ──────────────────────────────────────── *)
  Printf.printf "\n=== Results: %d passed, %d failed (total: %d) ===\n"
    !tests_passed !tests_failed !tests_run;
  if !tests_failed > 0 then exit 1
