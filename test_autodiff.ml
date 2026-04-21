(* test_autodiff.ml — Unit tests for the autodiff Forward-mode AD module *)
(* Tests: arithmetic derivatives, elementary functions, chain rule,       *)
(* higher-order derivatives, gradient, Jacobian, Hessian, activations.   *)

#use "autodiff.ml"

let passed = ref 0
let failed = ref 0
let total  = ref 0

let approx_eq ?(eps=1e-8) a b =
  Float.abs (a -. b) < eps ||
  Float.abs (a -. b) < eps *. Float.abs (Float.max (Float.abs a) (Float.abs b))

let test name f =
  incr total;
  try
    f ();
    incr passed;
    Printf.printf "  ✓ %s\n" name
  with ex ->
    incr failed;
    Printf.printf "  ✗ %s: %s\n" name (Printexc.to_string ex)

let assert_approx ?(eps=1e-6) expected actual msg =
  if not (approx_eq ~eps expected actual) then
    failwith (Printf.sprintf "%s: expected %.10g, got %.10g" msg expected actual)

let () =
  Printf.printf "\n══════════════════════════════════════════\n";
  Printf.printf "  Autodiff — Forward Mode Tests\n";
  Printf.printf "══════════════════════════════════════════\n\n";

  (* ── §1 Basic arithmetic derivatives ── *)
  Printf.printf "§1 Arithmetic\n";

  test "d/dx(x) = 1" (fun () ->
    let d = Forward.diff (fun x -> x) 3.0 in
    assert_approx 1.0 d "identity"
  );

  test "d/dx(x + 5) = 1" (fun () ->
    let open Forward in
    let d = diff (fun x -> x + const 5.0) 2.0 in
    assert_approx 1.0 d "add const"
  );

  test "d/dx(3x) = 3" (fun () ->
    let open Forward in
    let d = diff (fun x -> const 3.0 * x) 7.0 in
    assert_approx 3.0 d "scalar mul"
  );

  test "d/dx(x^2) = 2x at x=4" (fun () ->
    let open Forward in
    let d = diff (fun x -> x * x) 4.0 in
    assert_approx 8.0 d "x^2"
  );

  test "d/dx(x^3) = 3x^2 at x=2" (fun () ->
    let open Forward in
    let d = diff (fun x -> x * x * x) 2.0 in
    assert_approx 12.0 d "x^3"
  );

  test "d/dx(1/x) = -1/x^2 at x=3" (fun () ->
    let open Forward in
    let d = diff (fun x -> const 1.0 / x) 3.0 in
    assert_approx (-1.0 /. 9.0) d "reciprocal"
  );

  test "negation derivative" (fun () ->
    let open Forward in
    let d = diff (fun x -> neg x) 5.0 in
    assert_approx (-1.0) d "neg"
  );

  (* ── §2 Elementary functions ── *)
  Printf.printf "\n§2 Elementary functions\n";

  test "d/dx(sin x) = cos x at x=π/4" (fun () ->
    let x = Float.pi /. 4.0 in
    let d = Forward.diff Forward.sin x in
    assert_approx (cos x) d "sin'"
  );

  test "d/dx(cos x) = -sin x at x=π/3" (fun () ->
    let x = Float.pi /. 3.0 in
    let d = Forward.diff Forward.cos x in
    assert_approx (-. sin x) d "cos'"
  );

  test "d/dx(tan x) = sec^2 x at x=0.5" (fun () ->
    let x = 0.5 in
    let c = cos x in
    let d = Forward.diff Forward.tan x in
    assert_approx (1.0 /. (c *. c)) d "tan'"
  );

  test "d/dx(exp x) = exp x at x=1" (fun () ->
    let d = Forward.diff Forward.exp 1.0 in
    assert_approx (exp 1.0) d "exp'"
  );

  test "d/dx(log x) = 1/x at x=2" (fun () ->
    let d = Forward.diff Forward.log 2.0 in
    assert_approx 0.5 d "log'"
  );

  test "d/dx(sqrt x) = 1/(2√x) at x=9" (fun () ->
    let d = Forward.diff Forward.sqrt 9.0 in
    assert_approx (1.0 /. 6.0) d "sqrt'"
  );

  test "d/dx(x^3.5) = 3.5 x^2.5 at x=2" (fun () ->
    let open Forward in
    let d = diff (fun x -> pow x 3.5) 2.0 in
    assert_approx (3.5 *. (2.0 ** 2.5)) d "pow'"
  );

  (* ── §3 Hyperbolic & inverse trig ── *)
  Printf.printf "\n§3 Hyperbolic & inverse trig\n";

  test "d/dx(sinh x) = cosh x" (fun () ->
    let x = 1.5 in
    let d = Forward.diff Forward.sinh x in
    assert_approx (cosh x) d "sinh'"
  );

  test "d/dx(cosh x) = sinh x" (fun () ->
    let x = 1.5 in
    let d = Forward.diff Forward.cosh x in
    assert_approx (sinh x) d "cosh'"
  );

  test "d/dx(tanh x) = 1 - tanh^2 x" (fun () ->
    let x = 0.8 in
    let t = tanh x in
    let d = Forward.diff Forward.tanh x in
    assert_approx (1.0 -. t *. t) d "tanh'"
  );

  test "d/dx(asin x) = 1/√(1-x²) at x=0.5" (fun () ->
    let x = 0.5 in
    let d = Forward.diff Forward.asin x in
    assert_approx (1.0 /. sqrt (1.0 -. x *. x)) d "asin'"
  );

  test "d/dx(atan x) = 1/(1+x²) at x=1" (fun () ->
    let d = Forward.diff Forward.atan 1.0 in
    assert_approx 0.5 d "atan'"
  );

  (* ── §4 Chain rule / composition ── *)
  Printf.printf "\n§4 Chain rule\n";

  test "d/dx(sin(x^2)) = 2x cos(x^2) at x=1" (fun () ->
    let open Forward in
    let d = diff (fun x -> sin (x * x)) 1.0 in
    assert_approx (2.0 *. Stdlib.cos 1.0) d "sin(x^2)"
  );

  test "d/dx(exp(sin x)) at x=0" (fun () ->
    let open Forward in
    let d = diff (fun x -> exp (sin x)) 0.0 in
    (* exp(sin 0) * cos 0 = exp(0) * 1 = 1 *)
    assert_approx 1.0 d "exp(sin x)"
  );

  test "d/dx(log(x^2 + 1)) at x=1" (fun () ->
    let open Forward in
    let d = diff (fun x -> log (x * x + const 1.0)) 1.0 in
    (* 2x/(x^2+1) = 2/2 = 1 *)
    assert_approx 1.0 d "log(x^2+1)"
  );

  (* ── §5 Activation functions ── *)
  Printf.printf "\n§5 Activation functions\n";

  test "sigmoid(0) = 0.5, sigmoid'(0) = 0.25" (fun () ->
    let open Forward in
    let r = sigmoid (var 0.0) in
    assert_approx 0.5 (value r) "sig(0)";
    assert_approx 0.25 (deriv r) "sig'(0)"
  );

  test "relu(x) derivative positive region" (fun () ->
    let d = Forward.diff Forward.relu 3.0 in
    assert_approx 1.0 d "relu'(3)"
  );

  test "relu(x) derivative negative region" (fun () ->
    let d = Forward.diff Forward.relu (-2.0) in
    assert_approx 0.0 d "relu'(-2)"
  );

  test "softplus'(x) ≈ sigmoid(x)" (fun () ->
    let x = 1.5 in
    let d = Forward.diff Forward.softplus x in
    let sig_x = 1.0 /. (1.0 +. exp (-. x)) in
    assert_approx sig_x d "softplus'"
  );

  (* ── §6 Higher-order derivatives ── *)
  Printf.printf "\n§6 Higher-order derivatives\n";

  test "d²/dx²(x^3) = 6x at x=2 → 12" (fun () ->
    let open Forward in
    let f x = x *. x *. x in
    let d2 = nth_diff 2 f 2.0 in
    assert_approx ~eps:1e-4 12.0 d2 "d²(x³)"
  );

  test "d³/dx³(sin x) = -cos x at x=0 → -1" (fun () ->
    let open Forward in
    let f x = Stdlib.sin x in
    let d3 = nth_diff 3 f 0.0 in
    assert_approx ~eps:1e-3 (-1.0) d3 "d³(sin)"
  );

  (* ── §7 Gradient ── *)
  Printf.printf "\n§7 Gradient\n";

  test "∇(x² + y²) at (3,4) = (6, 8)" (fun () ->
    let open Forward in
    let f xs = xs.(0) * xs.(0) + xs.(1) * xs.(1) in
    let g = gradient f [|3.0; 4.0|] in
    assert_approx 6.0 g.(0) "∂/∂x";
    assert_approx 8.0 g.(1) "∂/∂y"
  );

  test "∇(x*y + y*z) at (1,2,3) = (2, 4, 2)" (fun () ->
    let open Forward in
    let f xs = xs.(0) * xs.(1) + xs.(1) * xs.(2) in
    let g = gradient f [|1.0; 2.0; 3.0|] in
    assert_approx 2.0 g.(0) "∂/∂x";
    assert_approx 4.0 g.(1) "∂/∂y";
    assert_approx 2.0 g.(2) "∂/∂z"
  );

  (* ── §8 Jacobian ── *)
  Printf.printf "\n§8 Jacobian\n";

  test "Jacobian of (x+y, x*y) at (2,3)" (fun () ->
    let open Forward in
    let f xs = [| xs.(0) + xs.(1); xs.(0) * xs.(1) |] in
    let j = jacobian f [|2.0; 3.0|] in
    (* Row 0: [1, 1], Row 1: [3, 2] *)
    assert_approx 1.0 j.(0).(0) "J[0,0]";
    assert_approx 1.0 j.(0).(1) "J[0,1]";
    assert_approx 3.0 j.(1).(0) "J[1,0]";
    assert_approx 2.0 j.(1).(1) "J[1,1]"
  );

  (* ── §9 Hessian ── *)
  Printf.printf "\n§9 Hessian\n";

  test "Hessian of x² + xy + y² at (1,1)" (fun () ->
    let open Forward in
    let f xs = xs.(0) * xs.(0) + xs.(0) * xs.(1) + xs.(1) * xs.(1) in
    let h = hessian f [|1.0; 1.0|] in
    (* H = [[2, 1], [1, 2]] *)
    assert_approx ~eps:1e-4 2.0 h.(0).(0) "H[0,0]";
    assert_approx ~eps:1e-4 1.0 h.(0).(1) "H[0,1]";
    assert_approx ~eps:1e-4 1.0 h.(1).(0) "H[1,0]";
    assert_approx ~eps:1e-4 2.0 h.(1).(1) "H[1,1]"
  );

  (* ── §10 Directional derivative ── *)
  Printf.printf "\n§10 Directional derivative\n";

  test "directional deriv of x²+y² at (1,2) in dir (1,0) = 2" (fun () ->
    let open Forward in
    let f xs = xs.(0) * xs.(0) + xs.(1) * xs.(1) in
    let dd = directional_deriv f [|1.0; 2.0|] [|1.0; 0.0|] in
    assert_approx 2.0 dd "dir_x"
  );

  test "directional deriv of x²+y² at (1,2) in dir (0,1) = 4" (fun () ->
    let open Forward in
    let f xs = xs.(0) * xs.(0) + xs.(1) * xs.(1) in
    let dd = directional_deriv f [|1.0; 2.0|] [|0.0; 1.0|] in
    assert_approx 4.0 dd "dir_y"
  );

  (* ── Summary ── *)
  Printf.printf "\n══════════════════════════════════════════\n";
  Printf.printf "  Results: %d passed, %d failed (of %d)\n" !passed !failed !total;
  Printf.printf "══════════════════════════════════════════\n";
  if !failed > 0 then exit 1
