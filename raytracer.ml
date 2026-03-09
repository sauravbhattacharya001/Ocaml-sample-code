(* ========================================================================= *)
(*  Raytracer                                                                *)
(*  A functional raytracer in OCaml: spheres, planes, point lights,          *)
(*  shadows, reflections, anti-aliasing, and PPM output.                     *)
(* ========================================================================= *)

(* ---- Vector3 ----------------------------------------------------------- *)
module Vec3 = struct
  type t = { x : float; y : float; z : float }

  let create x y z = { x; y; z }
  let zero = { x = 0.0; y = 0.0; z = 0.0 }
  let add a b = { x = a.x +. b.x; y = a.y +. b.y; z = a.z +. b.z }
  let sub a b = { x = a.x -. b.x; y = a.y -. b.y; z = a.z -. b.z }
  let mul a s = { x = a.x *. s; y = a.y *. s; z = a.z *. s }
  let neg a = { x = -. a.x; y = -. a.y; z = -. a.z }
  let dot a b = a.x *. b.x +. a.y *. b.y +. a.z *. b.z
  let cross a b =
    { x = a.y *. b.z -. a.z *. b.y;
      y = a.z *. b.x -. a.x *. b.z;
      z = a.x *. b.y -. a.y *. b.x }
  let length_sq a = dot a a
  let length a = sqrt (length_sq a)
  let normalize a =
    let len = length a in
    if len > 1e-10 then mul a (1.0 /. len) else zero
  let reflect v n = sub v (mul n (2.0 *. dot v n))
  let hadamard a b = { x = a.x *. b.x; y = a.y *. b.y; z = a.z *. b.z }
  let clamp01 a =
    let c v = Float.max 0.0 (Float.min 1.0 v) in
    { x = c a.x; y = c a.y; z = c a.z }
  let lerp a b t = add (mul a (1.0 -. t)) (mul b t)
  let equal ?(eps=1e-9) a b =
    Float.abs (a.x -. b.x) < eps &&
    Float.abs (a.y -. b.y) < eps &&
    Float.abs (a.z -. b.z) < eps
end

(* ---- Color = Vec3 (r, g, b in [0,1]) ----------------------------------- *)
module Color = struct
  include Vec3
  let black = zero
  let white = create 1.0 1.0 1.0
  let red = create 1.0 0.0 0.0
  let green = create 0.0 1.0 0.0
  let blue = create 0.0 0.0 1.0
  let to_rgb c =
    let f v = int_of_float (Float.min 255.0 (Float.max 0.0 (v *. 255.0 +. 0.5))) in
    (f c.x, f c.y, f c.z)
end

(* ---- Ray ---------------------------------------------------------------- *)
module Ray = struct
  type t = { origin : Vec3.t; direction : Vec3.t }
  let create origin direction = { origin; direction = Vec3.normalize direction }
  let point_at ray t = Vec3.add ray.origin (Vec3.mul ray.direction t)
end

(* ---- Material ----------------------------------------------------------- *)
type material = {
  color : Color.t;
  ambient : float;
  diffuse : float;
  specular : float;
  shininess : float;
  reflectivity : float;
}

let default_material = {
  color = Color.create 0.8 0.8 0.8;
  ambient = 0.1;
  diffuse = 0.7;
  specular = 0.3;
  shininess = 50.0;
  reflectivity = 0.0;
}

(* ---- Shapes ------------------------------------------------------------- *)
type shape =
  | Sphere of { center : Vec3.t; radius : float; material : material }
  | Plane  of { point : Vec3.t; normal : Vec3.t; material : material }

type hit = {
  t : float;
  point : Vec3.t;
  normal : Vec3.t;
  material : material;
}

let intersect_sphere ray center radius =
  let oc = Vec3.sub ray.Ray.origin center in
  let a = Vec3.dot ray.direction ray.direction in
  let b = 2.0 *. Vec3.dot oc ray.direction in
  let c = Vec3.dot oc oc -. radius *. radius in
  let disc = b *. b -. 4.0 *. a *. c in
  if disc < 0.0 then None
  else
    let sqrt_disc = sqrt disc in
    let t1 = (-. b -. sqrt_disc) /. (2.0 *. a) in
    let t2 = (-. b +. sqrt_disc) /. (2.0 *. a) in
    let eps = 1e-4 in
    if t1 > eps then Some t1
    else if t2 > eps then Some t2
    else None

let intersect_plane ray point normal =
  let denom = Vec3.dot normal ray.Ray.direction in
  if Float.abs denom < 1e-6 then None
  else
    let t = Vec3.dot (Vec3.sub point ray.origin) normal /. denom in
    if t > 1e-4 then Some t else None

let intersect_shape ray shape =
  match shape with
  | Sphere { center; radius; material } ->
    (match intersect_sphere ray center radius with
     | Some t ->
       let p = Ray.point_at ray t in
       let n = Vec3.normalize (Vec3.sub p center) in
       Some { t; point = p; normal = n; material }
     | None -> None)
  | Plane { point; normal; material } ->
    (match intersect_plane ray point normal with
     | Some t ->
       let p = Ray.point_at ray t in
       Some { t; point = p; normal; material }
     | None -> None)

(* ---- Light -------------------------------------------------------------- *)
type light = {
  position : Vec3.t;
  intensity : Color.t;
}

(* ---- Scene -------------------------------------------------------------- *)
type scene = {
  shapes : shape list;
  lights : light list;
  background : Color.t;
  max_depth : int;
}

let closest_hit ray shapes =
  List.fold_left (fun best shape ->
    match intersect_shape ray shape with
    | Some h ->
      (match best with
       | None -> Some h
       | Some b -> if h.t < b.t then Some h else best)
    | None -> best
  ) None shapes

let is_shadowed scene light_pos hit_point =
  let dir = Vec3.sub light_pos hit_point in
  let dist = Vec3.length dir in
  let shadow_ray = Ray.create hit_point dir in
  match closest_hit shadow_ray scene.shapes with
  | Some h -> h.t < dist
  | None -> false

(* ---- Phong shading ------------------------------------------------------ *)
let shade scene ray hit =
  let mat = hit.material in
  (* Ambient *)
  let ambient = Vec3.mul mat.color mat.ambient in
  (* Accumulate light contributions *)
  List.fold_left (fun acc light ->
    if is_shadowed scene light.position hit.point then acc
    else
      let light_dir = Vec3.normalize (Vec3.sub light.position hit.point) in
      (* Diffuse *)
      let dot_ln = Float.max 0.0 (Vec3.dot hit.normal light_dir) in
      let diff = Vec3.mul (Vec3.hadamard mat.color light.intensity) (mat.diffuse *. dot_ln) in
      (* Specular (Blinn-Phong) *)
      let view_dir = Vec3.normalize (Vec3.neg ray.Ray.direction) in
      let half_dir = Vec3.normalize (Vec3.add light_dir view_dir) in
      let dot_nh = Float.max 0.0 (Vec3.dot hit.normal half_dir) in
      let spec_val = mat.specular *. (dot_nh ** mat.shininess) in
      let spec = Vec3.mul light.intensity spec_val in
      Vec3.add acc (Vec3.add diff spec)
  ) ambient scene.lights

(* ---- Trace -------------------------------------------------------------- *)
let rec trace scene ray depth =
  if depth >= scene.max_depth then scene.background
  else
    match closest_hit ray scene.shapes with
    | None -> scene.background
    | Some hit ->
      let local_color = shade scene ray hit in
      if hit.material.reflectivity > 1e-6 then
        let reflect_dir = Vec3.reflect ray.direction hit.normal in
        let reflect_ray = Ray.create hit.point reflect_dir in
        let reflected = trace scene reflect_ray (depth + 1) in
        Vec3.add
          (Vec3.mul local_color (1.0 -. hit.material.reflectivity))
          (Vec3.mul reflected hit.material.reflectivity)
      else
        local_color

(* ---- Camera ------------------------------------------------------------- *)
module Camera = struct
  type t = {
    origin : Vec3.t;
    lower_left : Vec3.t;
    horizontal : Vec3.t;
    vertical : Vec3.t;
  }

  let create ~lookfrom ~lookat ~vup ~vfov ~aspect =
    let theta = vfov *. Float.pi /. 180.0 in
    let half_h = Float.tan (theta /. 2.0) in
    let half_w = aspect *. half_h in
    let w = Vec3.normalize (Vec3.sub lookfrom lookat) in
    let u = Vec3.normalize (Vec3.cross vup w) in
    let v = Vec3.cross w u in
    let lower_left = Vec3.(sub (sub (sub lookfrom (mul u half_w)) (mul v half_h)) w) in
    let horizontal = Vec3.mul u (2.0 *. half_w) in
    let vertical = Vec3.mul v (2.0 *. half_h) in
    { origin = lookfrom; lower_left; horizontal; vertical }

  let get_ray cam s t =
    let dir = Vec3.(sub (add (add cam.lower_left (mul cam.horizontal s)) (mul cam.vertical t)) cam.origin) in
    Ray.create cam.origin dir
end

(* ---- Render ------------------------------------------------------------- *)
let render ~width ~height ~samples scene camera =
  let pixels = Array.init height (fun _ -> Array.make width Color.black) in
  for j = 0 to height - 1 do
    for i = 0 to width - 1 do
      let color = ref Vec3.zero in
      for s = 0 to samples - 1 do
        for t = 0 to samples - 1 do
          let u = (Float.of_int i +. (Float.of_int s +. 0.5) /. Float.of_int samples) /. Float.of_int width in
          let v = (Float.of_int (height - 1 - j) +. (Float.of_int t +. 0.5) /. Float.of_int samples) /. Float.of_int height in
          let ray = Camera.get_ray camera u v in
          color := Vec3.add !color (trace scene ray 0)
        done
      done;
      let n = Float.of_int (samples * samples) in
      pixels.(j).(i) <- Vec3.clamp01 (Vec3.mul !color (1.0 /. n))
    done
  done;
  pixels

(* ---- PPM Output --------------------------------------------------------- *)
let write_ppm filename pixels =
  let h = Array.length pixels in
  let w = Array.length pixels.(0) in
  let oc = open_out filename in
  Printf.fprintf oc "P3\n%d %d\n255\n" w h;
  Array.iter (fun row ->
    Array.iter (fun c ->
      let (r, g, b) = Color.to_rgb c in
      Printf.fprintf oc "%d %d %d " r g b
    ) row;
    Printf.fprintf oc "\n"
  ) pixels;
  close_out oc

(* ---- Checkerboard pattern ----------------------------------------------- *)
let checkerboard_color p c1 c2 scale =
  let f v = int_of_float (Float.round (v *. scale)) in
  let s = (f p.Vec3.x + f p.y + f p.z) mod 2 in
  if s = 0 then c1 else c2

(* ---- Demo scene builder ------------------------------------------------- *)
let demo_scene () =
  let mat_red = { default_material with color = Color.create 0.9 0.1 0.1; diffuse = 0.8 } in
  let mat_green = { default_material with color = Color.create 0.1 0.8 0.2; diffuse = 0.7; specular = 0.5; shininess = 100.0 } in
  let mat_blue = { default_material with color = Color.create 0.2 0.3 0.9; diffuse = 0.6; reflectivity = 0.3 } in
  let mat_mirror = { default_material with color = Color.white; diffuse = 0.1; specular = 0.9; shininess = 200.0; reflectivity = 0.8 } in
  let mat_floor = { default_material with color = Color.create 0.6 0.6 0.6; diffuse = 0.8; specular = 0.1; reflectivity = 0.15 } in
  {
    shapes = [
      Sphere { center = Vec3.create 0.0 1.0 0.0; radius = 1.0; material = mat_red };
      Sphere { center = Vec3.create (-2.5) 0.7 1.5; radius = 0.7; material = mat_green };
      Sphere { center = Vec3.create 2.0 0.5 1.0; radius = 0.5; material = mat_blue };
      Sphere { center = Vec3.create (-0.5) 0.4 3.0; radius = 0.4; material = mat_mirror };
      Plane { point = Vec3.zero; normal = Vec3.create 0.0 1.0 0.0; material = mat_floor };
    ];
    lights = [
      { position = Vec3.create (-5.0) 8.0 5.0; intensity = Color.create 0.9 0.9 0.9 };
      { position = Vec3.create 5.0 6.0 (-3.0); intensity = Color.create 0.4 0.4 0.6 };
    ];
    background = Color.create 0.2 0.3 0.5;
    max_depth = 5;
  }

(* ========================================================================= *)
(*  Tests                                                                    *)
(* ========================================================================= *)
let tests_passed = ref 0
let tests_failed = ref 0

let assert_true name cond =
  if cond then (incr tests_passed; Printf.printf "  ✓ %s\n" name)
  else (incr tests_failed; Printf.printf "  ✗ FAIL: %s\n" name)

let assert_float name ?(eps=1e-6) expected actual =
  assert_true name (Float.abs (expected -. actual) < eps)

let assert_vec3 name ?(eps=1e-6) expected actual =
  assert_true name (Vec3.equal ~eps expected actual)

let () =
  Printf.printf "\n=== Raytracer Tests ===\n\n";

  (* -- Vec3 tests -- *)
  Printf.printf "Vec3:\n";
  let a = Vec3.create 1.0 2.0 3.0 in
  let b = Vec3.create 4.0 5.0 6.0 in
  assert_vec3 "add" (Vec3.create 5.0 7.0 9.0) (Vec3.add a b);
  assert_vec3 "sub" (Vec3.create (-3.0) (-3.0) (-3.0)) (Vec3.sub a b);
  assert_vec3 "mul" (Vec3.create 2.0 4.0 6.0) (Vec3.mul a 2.0);
  assert_vec3 "neg" (Vec3.create (-1.0) (-2.0) (-3.0)) (Vec3.neg a);
  assert_float "dot" 32.0 (Vec3.dot a b);
  assert_vec3 "cross" (Vec3.create (-3.0) 6.0 (-3.0)) (Vec3.cross a b);
  assert_float "length" (sqrt 14.0) (Vec3.length a);
  let n = Vec3.normalize a in
  assert_float "normalize length" 1.0 (Vec3.length n);
  assert_vec3 "zero" Vec3.zero (Vec3.create 0.0 0.0 0.0);
  let r = Vec3.reflect (Vec3.create 1.0 (-1.0) 0.0) (Vec3.create 0.0 1.0 0.0) in
  assert_vec3 "reflect" (Vec3.create 1.0 1.0 0.0) r;
  assert_vec3 "hadamard" (Vec3.create 4.0 10.0 18.0) (Vec3.hadamard a b);
  assert_vec3 "clamp01" (Vec3.create 0.0 0.5 1.0) (Vec3.clamp01 (Vec3.create (-0.5) 0.5 1.5));
  assert_vec3 "lerp" (Vec3.create 2.5 3.5 4.5) (Vec3.lerp a b 0.5);

  (* -- Color tests -- *)
  Printf.printf "Color:\n";
  let (r, g, b) = Color.to_rgb (Color.create 1.0 0.5 0.0) in
  assert_true "to_rgb red" (r = 255);
  assert_true "to_rgb green" (g = 128);
  assert_true "to_rgb blue" (b = 0);
  assert_true "to_rgb clamp high" (let (r,_,_) = Color.to_rgb (Color.create 2.0 0.0 0.0) in r = 255);
  assert_true "to_rgb clamp low" (let (r,_,_) = Color.to_rgb (Color.create (-1.0) 0.0 0.0) in r = 0);

  (* -- Ray tests -- *)
  Printf.printf "Ray:\n";
  let ray = Ray.create (Vec3.create 0.0 0.0 0.0) (Vec3.create 1.0 0.0 0.0) in
  assert_vec3 "point_at" (Vec3.create 5.0 0.0 0.0) (Ray.point_at ray 5.0);
  assert_float "direction normalized" 1.0 (Vec3.length ray.direction);

  (* -- Sphere intersection tests -- *)
  Printf.printf "Sphere intersection:\n";
  let ray_z = Ray.create (Vec3.create 0.0 0.0 5.0) (Vec3.create 0.0 0.0 (-1.0)) in
  let sphere_center = Vec3.create 0.0 0.0 0.0 in
  (match intersect_sphere ray_z sphere_center 1.0 with
   | Some t -> assert_float "hit sphere front" 4.0 t
   | None -> assert_true "hit sphere front" false);
  let ray_miss = Ray.create (Vec3.create 0.0 10.0 5.0) (Vec3.create 0.0 0.0 (-1.0)) in
  assert_true "miss sphere" (intersect_sphere ray_miss sphere_center 1.0 = None);
  let ray_inside = Ray.create Vec3.zero (Vec3.create 0.0 0.0 1.0) in
  (match intersect_sphere ray_inside sphere_center 5.0 with
   | Some t -> assert_true "inside sphere hits exit" (t > 0.0)
   | None -> assert_true "inside sphere hits exit" false);
  let ray_behind = Ray.create (Vec3.create 0.0 0.0 5.0) (Vec3.create 0.0 0.0 1.0) in
  assert_true "sphere behind" (intersect_sphere ray_behind sphere_center 1.0 = None);

  (* -- Plane intersection tests -- *)
  Printf.printf "Plane intersection:\n";
  let floor_pt = Vec3.zero in
  let floor_n = Vec3.create 0.0 1.0 0.0 in
  let ray_down = Ray.create (Vec3.create 0.0 5.0 0.0) (Vec3.create 0.0 (-1.0) 0.0) in
  (match intersect_plane ray_down floor_pt floor_n with
   | Some t -> assert_float "hit plane" 5.0 t
   | None -> assert_true "hit plane" false);
  let ray_parallel = Ray.create (Vec3.create 0.0 5.0 0.0) (Vec3.create 1.0 0.0 0.0) in
  assert_true "parallel to plane" (intersect_plane ray_parallel floor_pt floor_n = None);
  let ray_away = Ray.create (Vec3.create 0.0 5.0 0.0) (Vec3.create 0.0 1.0 0.0) in
  assert_true "plane behind" (intersect_plane ray_away floor_pt floor_n = None);

  (* -- Shape intersection tests -- *)
  Printf.printf "Shape intersection:\n";
  let s = Sphere { center = Vec3.create 0.0 0.0 (-5.0); radius = 1.0; material = default_material } in
  let ray_s = Ray.create Vec3.zero (Vec3.create 0.0 0.0 (-1.0)) in
  (match intersect_shape ray_s s with
   | Some h ->
     assert_float "shape sphere t" 4.0 h.t;
     assert_vec3 "shape sphere normal" (Vec3.create 0.0 0.0 1.0) h.normal
   | None -> assert_true "shape sphere hit" false);

  (* -- closest_hit tests -- *)
  Printf.printf "Scene closest_hit:\n";
  let s1 = Sphere { center = Vec3.create 0.0 0.0 (-3.0); radius = 1.0; material = default_material } in
  let s2 = Sphere { center = Vec3.create 0.0 0.0 (-7.0); radius = 1.0; material = default_material } in
  let ray_f = Ray.create Vec3.zero (Vec3.create 0.0 0.0 (-1.0)) in
  (match closest_hit ray_f [s1; s2] with
   | Some h -> assert_float "closest is nearer" 2.0 h.t
   | None -> assert_true "closest found" false);
  assert_true "no hit" (closest_hit (Ray.create Vec3.zero (Vec3.create 0.0 1.0 0.0)) [s1; s2] = None);

  (* -- Shadow tests -- *)
  Printf.printf "Shadows:\n";
  let scene = {
    shapes = [
      Sphere { center = Vec3.create 0.0 2.0 0.0; radius = 0.5; material = default_material };
    ];
    lights = [{ position = Vec3.create 0.0 10.0 0.0; intensity = Color.white }];
    background = Color.black;
    max_depth = 1;
  } in
  assert_true "point in shadow" (is_shadowed scene (Vec3.create 0.0 10.0 0.0) (Vec3.create 0.0 0.0 0.0));
  assert_true "point not in shadow" (not (is_shadowed scene (Vec3.create 0.0 10.0 0.0) (Vec3.create 5.0 0.0 0.0)));

  (* -- Camera tests -- *)
  Printf.printf "Camera:\n";
  let cam = Camera.create
    ~lookfrom:(Vec3.create 0.0 0.0 5.0)
    ~lookat:Vec3.zero
    ~vup:(Vec3.create 0.0 1.0 0.0)
    ~vfov:90.0
    ~aspect:1.0 in
  let center_ray = Camera.get_ray cam 0.5 0.5 in
  assert_float "center ray direction z" (-1.0) center_ray.direction.z ~eps:0.01;
  assert_float "center ray direction x" 0.0 center_ray.direction.x ~eps:0.01;
  assert_float "center ray direction y" 0.0 center_ray.direction.y ~eps:0.01;

  (* -- Trace tests -- *)
  Printf.printf "Trace:\n";
  let empty_scene = { shapes = []; lights = []; background = Color.create 0.5 0.5 0.5; max_depth = 1 } in
  let bg = trace empty_scene (Ray.create Vec3.zero (Vec3.create 0.0 0.0 (-1.0))) 0 in
  assert_vec3 "background color" (Color.create 0.5 0.5 0.5) bg;

  let lit_scene = {
    shapes = [Sphere { center = Vec3.create 0.0 0.0 (-5.0); radius = 1.0; material = default_material }];
    lights = [{ position = Vec3.create 0.0 5.0 0.0; intensity = Color.white }];
    background = Color.black;
    max_depth = 1;
  } in
  let c = trace lit_scene (Ray.create Vec3.zero (Vec3.create 0.0 0.0 (-1.0))) 0 in
  assert_true "lit sphere not black" (c.x > 0.0 || c.y > 0.0 || c.z > 0.0);

  (* depth limit *)
  let c_max = trace { lit_scene with max_depth = 0 } (Ray.create Vec3.zero (Vec3.create 0.0 0.0 (-1.0))) 0 in
  assert_vec3 "depth limit returns bg" Color.black c_max;

  (* reflection *)
  let mirror_mat = { default_material with reflectivity = 0.9; diffuse = 0.1 } in
  let refl_scene = {
    shapes = [
      Sphere { center = Vec3.create 0.0 0.0 (-3.0); radius = 1.0; material = mirror_mat };
      Sphere { center = Vec3.create 0.0 0.0 (-8.0); radius = 1.0;
               material = { default_material with color = Color.red } };
    ];
    lights = [{ position = Vec3.create 0.0 10.0 0.0; intensity = Color.white }];
    background = Color.black;
    max_depth = 3;
  } in
  let rc = trace refl_scene (Ray.create Vec3.zero (Vec3.create 0.0 0.0 (-1.0))) 0 in
  assert_true "reflection picks up color" (rc.x > 0.01);

  (* -- Render tests -- *)
  Printf.printf "Render:\n";
  let tiny_scene = {
    shapes = [Sphere { center = Vec3.create 0.0 0.0 (-3.0); radius = 1.0; material = default_material }];
    lights = [{ position = Vec3.create 0.0 5.0 5.0; intensity = Color.white }];
    background = Color.create 0.1 0.1 0.2;
    max_depth = 2;
  } in
  let tiny_cam = Camera.create ~lookfrom:(Vec3.create 0.0 0.0 0.0) ~lookat:(Vec3.create 0.0 0.0 (-1.0))
    ~vup:(Vec3.create 0.0 1.0 0.0) ~vfov:60.0 ~aspect:1.0 in
  let pixels = render ~width:4 ~height:4 ~samples:1 tiny_scene tiny_cam in
  assert_true "render height" (Array.length pixels = 4);
  assert_true "render width" (Array.length pixels.(0) = 4);
  (* center pixel should hit sphere *)
  let cp = pixels.(2).(2) in
  assert_true "center pixel not background" (not (Vec3.equal cp (Color.create 0.1 0.1 0.2) ~eps:0.05));

  (* -- Material tests -- *)
  Printf.printf "Material:\n";
  assert_float "default ambient" 0.1 default_material.ambient;
  assert_float "default diffuse" 0.7 default_material.diffuse;
  assert_float "default reflectivity" 0.0 default_material.reflectivity;

  (* -- Checkerboard tests -- *)
  Printf.printf "Checkerboard:\n";
  let c1 = Color.white in
  let c2 = Color.black in
  let cb1 = checkerboard_color (Vec3.create 0.0 0.0 0.0) c1 c2 1.0 in
  let cb2 = checkerboard_color (Vec3.create 1.0 0.0 0.0) c1 c2 1.0 in
  assert_true "checkerboard alternates" (not (Vec3.equal cb1 cb2));

  (* -- Demo scene tests -- *)
  Printf.printf "Demo scene:\n";
  let ds = demo_scene () in
  assert_true "5 shapes" (List.length ds.shapes = 5);
  assert_true "2 lights" (List.length ds.lights = 2);
  assert_true "max depth 5" (ds.max_depth = 5);

  (* -- PPM output test -- *)
  Printf.printf "PPM output:\n";
  let test_pixels = [|
    [| Color.red; Color.green |];
    [| Color.blue; Color.white |];
  |] in
  let tmpfile = "_test_output.ppm" in
  write_ppm tmpfile test_pixels;
  let ic = open_in tmpfile in
  let header = input_line ic in
  let dims = input_line ic in
  let maxval = input_line ic in
  close_in ic;
  assert_true "ppm header" (header = "P3");
  assert_true "ppm dimensions" (dims = "2 2");
  assert_true "ppm maxval" (maxval = "255");
  Sys.remove tmpfile;

  (* -- Integration: small render + write -- *)
  Printf.printf "Integration:\n";
  let int_pixels = render ~width:8 ~height:6 ~samples:1 (demo_scene ())
    (Camera.create ~lookfrom:(Vec3.create 3.0 3.0 5.0) ~lookat:(Vec3.create 0.0 0.7 0.0)
       ~vup:(Vec3.create 0.0 1.0 0.0) ~vfov:50.0 ~aspect:(8.0 /. 6.0)) in
  assert_true "integration render dims" (Array.length int_pixels = 6 && Array.length int_pixels.(0) = 8);
  let intfile = "_test_integration.ppm" in
  write_ppm intfile int_pixels;
  assert_true "integration file exists" (Sys.file_exists intfile);
  Sys.remove intfile;

  (* -- Summary -- *)
  Printf.printf "\n--- Results: %d passed, %d failed ---\n" !tests_passed !tests_failed;
  if !tests_failed > 0 then exit 1
