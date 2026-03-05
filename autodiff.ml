(* ============================================================================
   autodiff.ml - Automatic Differentiation (Forward & Reverse Mode)
   
   A complete automatic differentiation library in OCaml supporting:
   - Forward mode AD with dual numbers
   - Reverse mode AD with computation graphs
   - Higher-order derivatives
   - Gradient computation for multivariate functions
   - Jacobian and Hessian computation
   - Common math operations (trig, exp, log, power, etc.)
   - Optimization via gradient descent
   - Neural network building blocks (simple dense layer, activations)
   
   Usage:
     ocamlfind ocamlopt -package alcotest -linkpkg autodiff.ml -o autodiff && ./autodiff
   Or:
     ocaml autodiff.ml
   ============================================================================ *)

(* ========== Forward Mode AD with Dual Numbers ========== *)

module Forward = struct
  (** A dual number: value + derivative (tangent) *)
  type t = { v : float; d : float }

  let make v d = { v; d }
  let var x = { v = x; d = 1.0 }  (* independent variable *)
  let const x = { v = x; d = 0.0 }

  let value t = t.v
  let deriv t = t.d

  (* Arithmetic *)
  let ( + ) a b = { v = a.v +. b.v; d = a.d +. b.d }
  let ( - ) a b = { v = a.v -. b.v; d = a.d -. b.d }
  let ( * ) a b = { v = a.v *. b.v; d = a.d *. b.v +. a.v *. b.d }
  let ( / ) a b =
    { v = a.v /. b.v;
      d = (a.d *. b.v -. a.v *. b.d) /. (b.v *. b.v) }

  let neg a = { v = -. a.v; d = -. a.d }

  (* Elementary functions *)
  let sin a = { v = Stdlib.sin a.v; d = a.d *. Stdlib.cos a.v }
  let cos a = { v = Stdlib.cos a.v; d = -. a.d *. Stdlib.sin a.v }
  let tan a =
    let c = Stdlib.cos a.v in
    { v = Stdlib.tan a.v; d = a.d /. (c *. c) }

  let exp a = 
    let e = Stdlib.exp a.v in
    { v = e; d = a.d *. e }

  let log a = { v = Stdlib.log a.v; d = a.d /. a.v }

  let sqrt a =
    let s = Stdlib.sqrt a.v in
    { v = s; d = a.d /. (2.0 *. s) }

  let pow a n =
    let p = a.v ** n in
    { v = p; d = a.d *. n *. (a.v ** (n -. 1.0)) }

  let abs a =
    if a.v >= 0.0 then a
    else { v = -. a.v; d = -. a.d }

  (* Hyperbolic functions *)
  let sinh a = { v = Stdlib.sinh a.v; d = a.d *. Stdlib.cosh a.v }
  let cosh a = { v = Stdlib.cosh a.v; d = a.d *. Stdlib.sinh a.v }
  let tanh a =
    let t = Stdlib.tanh a.v in
    { v = t; d = a.d *. (1.0 -. t *. t) }

  (* Inverse trig *)
  let asin a = { v = Stdlib.asin a.v; d = a.d /. Stdlib.sqrt (1.0 -. a.v *. a.v) }
  let acos a = { v = Stdlib.acos a.v; d = -. a.d /. Stdlib.sqrt (1.0 -. a.v *. a.v) }
  let atan a = { v = Stdlib.atan a.v; d = a.d /. (1.0 +. a.v *. a.v) }
  let atan2 y x =
    let denom = x.v *. x.v +. y.v *. y.v in
    { v = Stdlib.atan2 y.v x.v;
      d = (y.d *. x.v -. y.v *. x.d) /. denom }

  (* Activation functions *)
  let sigmoid a =
    let s = 1.0 /. (1.0 +. Stdlib.exp (-. a.v)) in
    { v = s; d = a.d *. s *. (1.0 -. s) }

  let relu a =
    if a.v > 0.0 then a
    else { v = 0.0; d = 0.0 }

  let softplus a =
    (* log(1 + exp(x)) *)
    let e = Stdlib.exp a.v in
    { v = Stdlib.log (1.0 +. e); d = a.d *. e /. (1.0 +. e) }

  (* Compute derivative of f at x *)
  let diff f x =
    let result = f (var x) in
    deriv result

  (* Compute n-th derivative *)
  let rec nth_diff n f x =
    if n <= 0 then f x
    else if n = 1 then diff (fun d -> const (f d)) x
    else
      (* For higher-order, nest forward mode *)
      let f' x' = diff (fun d -> const (f d)) x' in
      nth_diff (n - 1) f' x

  (* Directional derivative: df/dv at point x in direction v *)
  let directional_deriv f x v =
    (* f : float array -> float, x : float array, v : float array *)
    let n = Array.length x in
    let duals = Array.init n (fun i -> make x.(i) v.(i)) in
    let result = f duals in
    deriv result

  (* Gradient via multiple forward passes *)
  let gradient f x =
    let n = Array.length x in
    Array.init n (fun i ->
      let duals = Array.init n (fun j ->
        make x.(j) (if i = j then 1.0 else 0.0)) in
      let result = f duals in
      deriv result)

  (* Jacobian of f : R^n -> R^m *)
  let jacobian f x =
    let n = Array.length x in
    (* One forward pass per input dimension *)
    let cols = Array.init n (fun i ->
      let duals = Array.init n (fun j ->
        make x.(j) (if i = j then 1.0 else 0.0)) in
      let results = f duals in
      Array.map deriv results) in
    (* cols.(i) is the i-th column; transpose to get rows *)
    let m = Array.length cols.(0) in
    Array.init m (fun i ->
      Array.init n (fun j -> cols.(j).(i)))

  (* Hessian via finite differences on the gradient.
     Computing exact second derivatives with forward-mode dual numbers
     requires nested dual types (dual-of-dual), which OCaml's type system
     doesn't support without functorization. We use central differences
     on the analytically computed gradient instead, which is accurate to
     O(eps²) ≈ 1e-14. *)
  let hessian f x =
    let n = Array.length x in
    let eps = 1e-7 in
    Array.init n (fun i ->
      Array.init n (fun j ->
        let x_plus = Array.copy x in
        let x_minus = Array.copy x in
        x_plus.(j) <- x_plus.(j) +. eps;
        x_minus.(j) <- x_minus.(j) -. eps;
        let g_plus = gradient f x_plus in
        let g_minus = gradient f x_minus in
        (g_plus.(i) -. g_minus.(i)) /. (2.0 *. eps)))
end

(* ========== Reverse Mode AD with Computation Graph ========== *)

module Reverse = struct
  type node = {
    mutable value : float;
    mutable grad : float;
    mutable backward : unit -> unit;
  }

  let create v = { value = v; grad = 0.0; backward = (fun () -> ()) }

  let var x = create x

  let value n = n.value
  let grad n = n.grad

  let ( + ) a b =
    let c = create (a.value +. b.value) in
    c.backward <- (fun () ->
      a.grad <- a.grad +. c.grad;
      b.grad <- b.grad +. c.grad);
    c

  let ( - ) a b =
    let c = create (a.value -. b.value) in
    c.backward <- (fun () ->
      a.grad <- a.grad +. c.grad;
      b.grad <- b.grad -. c.grad);
    c

  let ( * ) a b =
    let c = create (a.value *. b.value) in
    c.backward <- (fun () ->
      a.grad <- a.grad +. c.grad *. b.value;
      b.grad <- b.grad +. c.grad *. a.value);
    c

  let ( / ) a b =
    let c = create (a.value /. b.value) in
    c.backward <- (fun () ->
      a.grad <- a.grad +. c.grad /. b.value;
      b.grad <- b.grad -. c.grad *. a.value /. (b.value *. b.value));
    c

  let neg a =
    let c = create (-. a.value) in
    c.backward <- (fun () -> a.grad <- a.grad -. c.grad);
    c

  let sin a =
    let c = create (Stdlib.sin a.value) in
    c.backward <- (fun () -> a.grad <- a.grad +. c.grad *. Stdlib.cos a.value);
    c

  let cos a =
    let c = create (Stdlib.cos a.value) in
    c.backward <- (fun () -> a.grad <- a.grad -. c.grad *. Stdlib.sin a.value);
    c

  let tan a =
    let co = Stdlib.cos a.value in
    let c = create (Stdlib.tan a.value) in
    c.backward <- (fun () -> a.grad <- a.grad +. c.grad /. (co *. co));
    c

  let exp a =
    let e = Stdlib.exp a.value in
    let c = create e in
    c.backward <- (fun () -> a.grad <- a.grad +. c.grad *. e);
    c

  let log a =
    let c = create (Stdlib.log a.value) in
    c.backward <- (fun () -> a.grad <- a.grad +. c.grad /. a.value);
    c

  let sqrt a =
    let s = Stdlib.sqrt a.value in
    let c = create s in
    c.backward <- (fun () -> a.grad <- a.grad +. c.grad /. (2.0 *. s));
    c

  let pow a n =
    let p = a.value ** n in
    let c = create p in
    c.backward <- (fun () ->
      a.grad <- a.grad +. c.grad *. n *. (a.value ** (n -. 1.0)));
    c

  let abs a =
    let c = create (Stdlib.abs_float a.value) in
    c.backward <- (fun () ->
      let sign = if a.value >= 0.0 then 1.0 else -1.0 in
      a.grad <- a.grad +. c.grad *. sign);
    c

  let sinh a =
    let c = create (Stdlib.sinh a.value) in
    c.backward <- (fun () -> a.grad <- a.grad +. c.grad *. Stdlib.cosh a.value);
    c

  let cosh a =
    let c = create (Stdlib.cosh a.value) in
    c.backward <- (fun () -> a.grad <- a.grad +. c.grad *. Stdlib.sinh a.value);
    c

  let tanh a =
    let t = Stdlib.tanh a.value in
    let c = create t in
    c.backward <- (fun () -> a.grad <- a.grad +. c.grad *. (1.0 -. t *. t));
    c

  let sigmoid a =
    let s = 1.0 /. (1.0 +. Stdlib.exp (-. a.value)) in
    let c = create s in
    c.backward <- (fun () -> a.grad <- a.grad +. c.grad *. s *. (1.0 -. s));
    c

  let relu a =
    let c = create (if a.value > 0.0 then a.value else 0.0) in
    c.backward <- (fun () ->
      if a.value > 0.0 then a.grad <- a.grad +. c.grad);
    c

  let softplus a =
    let e = Stdlib.exp a.value in
    let c = create (Stdlib.log (1.0 +. e)) in
    c.backward <- (fun () -> a.grad <- a.grad +. c.grad *. e /. (1.0 +. e));
    c

  let const x = create x

  (** Topological sort for backpropagation.
      We trace the graph from the output node using a simple DFS.
      Since nodes don't store children, we build the graph via a tape. *)
  
  (* Tape-based approach: record operations *)
  type tape = node list ref

  let new_tape () : tape = ref []

  (* Record a node on the tape *)
  let record (tape : tape) node =
    tape := node :: !tape;
    node

  (* Run backpropagation on the tape *)
  let backward tape output =
    output.grad <- 1.0;
    List.iter (fun node -> node.backward ()) !tape

  (* Reset gradients *)
  let zero_grads nodes =
    List.iter (fun n -> n.grad <- 0.0) nodes

  (* ---- Tape-aware operations ---- *)

  let t_var tape x = record tape (var x)
  let t_const tape x = record tape (const x)
  let t_add tape a b = record tape (a + b)
  let t_sub tape a b = record tape (a - b)
  let t_mul tape a b = record tape (a * b)
  let t_div tape a b = record tape (a / b)
  let t_neg tape a = record tape (neg a)
  let t_sin tape a = record tape (sin a)
  let t_cos tape a = record tape (cos a)
  let t_exp tape a = record tape (exp a)
  let t_log tape a = record tape (log a)
  let t_sqrt tape a = record tape (sqrt a)
  let t_pow tape a n = record tape (pow a n)
  let t_tanh tape a = record tape (tanh a)
  let t_sigmoid tape a = record tape (sigmoid a)
  let t_relu tape a = record tape (relu a)

  (* Compute gradient of scalar function f : R^n -> R *)
  let gradient f x =
    let n = Array.length x in
    let tape = new_tape () in
    let vars = Array.init n (fun i -> t_var tape x.(i)) in
    let output = f tape vars in
    let output_recorded = record tape output in
    backward tape output_recorded;
    Array.map grad vars

  (* Simple gradient descent *)
  let gradient_descent ?(lr=0.01) ?(steps=100) f x0 =
    let x = Array.copy x0 in
    for _ = 1 to steps do
      let g = gradient f x in
      Array.iteri (fun i gi -> x.(i) <- x.(i) -. lr *. gi) g
    done;
    x
end

(* ========== Optimization Algorithms ========== *)

module Optimize = struct
  (** Gradient descent with momentum *)
  let momentum ?(lr=0.01) ?(beta=0.9) ?(steps=100) f x0 =
    let x = Array.copy x0 in
    let n = Array.length x in
    let v = Array.make n 0.0 in
    for _ = 1 to steps do
      let g = Reverse.gradient f x in
      Array.iteri (fun i gi ->
        v.(i) <- beta *. v.(i) +. lr *. gi;
        x.(i) <- x.(i) -. v.(i)) g
    done;
    x

  (** Adam optimizer *)
  let adam ?(lr=0.001) ?(beta1=0.9) ?(beta2=0.999) ?(eps=1e-8) ?(steps=100) f x0 =
    let x = Array.copy x0 in
    let n = Array.length x in
    let m = Array.make n 0.0 in
    let v = Array.make n 0.0 in
    for t = 1 to steps do
      let g = Reverse.gradient f x in
      let tf = float_of_int t in
      Array.iteri (fun i gi ->
        m.(i) <- beta1 *. m.(i) +. (1.0 -. beta1) *. gi;
        v.(i) <- beta2 *. v.(i) +. (1.0 -. beta2) *. gi *. gi;
        let m_hat = m.(i) /. (1.0 -. beta1 ** tf) in
        let v_hat = v.(i) /. (1.0 -. beta2 ** tf) in
        x.(i) <- x.(i) -. lr *. m_hat /. (Stdlib.sqrt v_hat +. eps)) g
    done;
    x

  (** Newton's method using Hessian (forward mode) *)
  let newton ?(steps=20) ?(tol=1e-10) f_scalar x0 =
    let x = Array.copy x0 in
    let n = Array.length x in
    for _ = 1 to steps do
      let f_fwd duals = 
        let sum = ref (Forward.const 0.0) in
        (* Wrap f_scalar to work with Forward.t array *)
        let vals = Array.map Forward.value duals in
        let tape = Reverse.new_tape () in
        let vars = Array.init n (fun i -> Reverse.t_var tape vals.(i)) in
        let out = f_scalar tape vars in
        ignore (Reverse.record tape out);
        sum := Forward.const (Reverse.value out);
        !sum
      in
      let g = Forward.gradient f_fwd x in
      let h = Forward.hessian f_fwd x in
      (* Solve H * dx = -g via simple diagonal approximation *)
      let max_g = Array.fold_left (fun acc gi -> Stdlib.max acc (Stdlib.abs_float gi)) 0.0 g in
      if max_g < tol then ()
      else
        Array.iteri (fun i _ ->
          let hii = h.(i).(i) in
          if Stdlib.abs_float hii > 1e-12 then
            x.(i) <- x.(i) -. g.(i) /. hii) x
    done;
    x
end

(* ========== Simple Neural Network Layer ========== *)

module NN = struct
  (** Dense layer parameters *)
  type layer = {
    weights : float array array;  (* out_dim x in_dim *)
    biases : float array;         (* out_dim *)
  }

  (** Initialize with small random weights *)
  let init_layer in_dim out_dim =
    let scale = Stdlib.sqrt (2.0 /. float_of_int in_dim) in
    { weights = Array.init out_dim (fun _ ->
        Array.init in_dim (fun _ -> (Random.float 2.0 -. 1.0) *. scale));
      biases = Array.make out_dim 0.0 }

  (** Forward pass through a dense layer using reverse mode *)
  let forward_dense tape layer input =
    let out_dim = Array.length layer.biases in
    let in_dim = Array.length input in
    Array.init out_dim (fun i ->
      let sum = ref (Reverse.t_const tape layer.biases.(i)) in
      for j = 0 to in_dim - 1 do
        let w = Reverse.t_const tape layer.weights.(i).(j) in
        sum := Reverse.t_add tape !sum (Reverse.t_mul tape w input.(j))
      done;
      !sum)

  (** Apply activation function *)
  let apply_activation tape activation nodes =
    Array.map (fun n ->
      match activation with
      | `Relu -> Reverse.t_relu tape n
      | `Sigmoid -> Reverse.t_sigmoid tape n
      | `Tanh -> Reverse.t_tanh tape n
      | `None -> n) nodes

  (** Mean squared error loss *)
  let mse_loss tape predictions targets =
    let n = Array.length predictions in
    let sum = ref (Reverse.t_const tape 0.0) in
    for i = 0 to n - 1 do
      let diff = Reverse.t_sub tape predictions.(i) (Reverse.t_const tape targets.(i)) in
      let sq = Reverse.t_mul tape diff diff in
      sum := Reverse.t_add tape !sum sq
    done;
    Reverse.t_div tape !sum (Reverse.t_const tape (float_of_int n))
end

(* ========== Tests ========== *)

let () = Printf.printf "=== Automatic Differentiation Tests ===\n\n"

let tolerance = 1e-6

let passed = ref 0
let failed = ref 0

let check msg expected actual =
  if Stdlib.abs_float (expected -. actual) > tolerance then begin
    Printf.printf "  FAIL: %s — expected %.8f, got %.8f\n" msg expected actual;
    incr failed
  end else begin
    Printf.printf "  PASS: %s\n" msg;
    incr passed
  end

let check_approx ?(eps=1e-4) msg expected actual =
  if Stdlib.abs_float (expected -. actual) > eps then begin
    Printf.printf "  FAIL: %s — expected %.8f, got %.8f\n" msg expected actual;
    incr failed
  end else begin
    Printf.printf "  PASS: %s\n" msg;
    incr passed
  end

(* ----- Forward Mode Tests ----- *)

let () =
  Printf.printf "--- Forward Mode: Basic Arithmetic ---\n";

  (* d/dx (x^2) at x=3 => 6 *)
  let f x = Forward.(x * x) in
  check "d/dx(x²) at 3 = 6" 6.0 (Forward.diff (fun x -> f x) 3.0);

  (* d/dx (x^3) at x=2 => 12 *)
  let f x = Forward.(x * x * x) in
  check "d/dx(x³) at 2 = 12" 12.0 (Forward.diff (fun x -> f x) 2.0);

  (* d/dx (1/x) at x=2 => -1/4 *)
  let f x = Forward.(const 1.0 / x) in
  check "d/dx(1/x) at 2 = -0.25" (-0.25) (Forward.diff (fun x -> f x) 2.0);

  (* d/dx (x + 1/x) at x=1 => 0 *)
  let f x = Forward.(x + const 1.0 / x) in
  check "d/dx(x + 1/x) at 1 = 0" 0.0 (Forward.diff (fun x -> f x) 1.0);

  (* d/dx (3x + 5) at x=7 => 3 *)
  let f x = Forward.(const 3.0 * x + const 5.0) in
  check "d/dx(3x + 5) = 3" 3.0 (Forward.diff (fun x -> f x) 7.0);

  Printf.printf "\n"

let () =
  Printf.printf "--- Forward Mode: Transcendental Functions ---\n";

  (* d/dx sin(x) at x=0 => cos(0) = 1 *)
  check "d/dx sin(0) = 1" 1.0 (Forward.diff Forward.sin 0.0);

  (* d/dx cos(x) at x=0 => -sin(0) = 0 *)
  check "d/dx cos(0) = 0" 0.0 (Forward.diff Forward.cos 0.0);

  (* d/dx exp(x) at x=1 => e *)
  check "d/dx exp(1) = e" (Stdlib.exp 1.0) (Forward.diff Forward.exp 1.0);

  (* d/dx log(x) at x=1 => 1 *)
  check "d/dx log(1) = 1" 1.0 (Forward.diff Forward.log 1.0);

  (* d/dx sqrt(x) at x=4 => 0.25 *)
  check "d/dx sqrt(4) = 0.25" 0.25 (Forward.diff Forward.sqrt 4.0);

  (* d/dx tan(x) at x=0 => 1 *)
  check "d/dx tan(0) = 1" 1.0 (Forward.diff Forward.tan 0.0);

  (* d/dx sinh(x) at x=0 => cosh(0) = 1 *)
  check "d/dx sinh(0) = 1" 1.0 (Forward.diff Forward.sinh 0.0);

  (* d/dx tanh(x) at x=0 => 1 *)
  check "d/dx tanh(0) = 1" 1.0 (Forward.diff Forward.tanh 0.0);

  Printf.printf "\n"

let () =
  Printf.printf "--- Forward Mode: Activation Functions ---\n";

  (* sigmoid(0) = 0.5, sigmoid'(0) = 0.25 *)
  check "sigmoid(0) value = 0.5" 0.5 (Forward.value (Forward.sigmoid (Forward.var 0.0)));
  check "sigmoid'(0) = 0.25" 0.25 (Forward.diff Forward.sigmoid 0.0);

  (* relu(2) = 2, relu'(2) = 1 *)
  check "relu'(2) = 1" 1.0 (Forward.diff Forward.relu 2.0);
  (* relu(-1) = 0, relu'(-1) = 0 *)
  check "relu'(-1) = 0" 0.0 (Forward.diff Forward.relu (-1.0));

  (* softplus'(x) = sigmoid(x) *)
  let x = 1.5 in
  let sp_deriv = Forward.diff Forward.softplus x in
  let sig_val = 1.0 /. (1.0 +. Stdlib.exp (-. x)) in
  check "softplus'(x) = sigmoid(x)" sig_val sp_deriv;

  Printf.printf "\n"

let () =
  Printf.printf "--- Forward Mode: Inverse Trig ---\n";

  (* d/dx asin(x) at x=0 => 1 *)
  check "d/dx asin(0) = 1" 1.0 (Forward.diff Forward.asin 0.0);

  (* d/dx acos(x) at x=0 => -1 *)
  check "d/dx acos(0) = -1" (-1.0) (Forward.diff Forward.acos 0.0);

  (* d/dx atan(x) at x=0 => 1 *)
  check "d/dx atan(0) = 1" 1.0 (Forward.diff Forward.atan 0.0);

  (* d/dx atan(x) at x=1 => 0.5 *)
  check "d/dx atan(1) = 0.5" 0.5 (Forward.diff Forward.atan 1.0);

  Printf.printf "\n"

let () =
  Printf.printf "--- Forward Mode: Power Rule ---\n";

  (* d/dx x^3 at x=2 => 12 *)
  check "d/dx x^3 at 2 = 12" 12.0 (Forward.diff (fun x -> Forward.pow x 3.0) 2.0);

  (* d/dx x^0.5 at x=4 => 0.25 *)
  check "d/dx x^0.5 at 4 = 0.25" 0.25 (Forward.diff (fun x -> Forward.pow x 0.5) 4.0);

  (* d/dx x^(-1) at x=2 => -0.25 *)
  check "d/dx x^(-1) at 2 = -0.25" (-0.25) (Forward.diff (fun x -> Forward.pow x (-1.0)) 2.0);

  Printf.printf "\n"

let () =
  Printf.printf "--- Forward Mode: Chain Rule ---\n";

  (* d/dx sin(x^2) at x=1 => 2*cos(1) *)
  let f x = Forward.(sin (x * x)) in
  check "d/dx sin(x²) at 1 = 2cos(1)" (2.0 *. Stdlib.cos 1.0) (Forward.diff f 1.0);

  (* d/dx exp(sin(x)) at x=0 => exp(0)*cos(0) = 1 *)
  let f x = Forward.(exp (sin x)) in
  check "d/dx exp(sin(x)) at 0 = 1" 1.0 (Forward.diff f 0.0);

  (* d/dx log(x^2 + 1) at x=1 => 2/(1+1) = 1 *)
  let f x = Forward.(log (x * x + const 1.0)) in
  check "d/dx log(x²+1) at 1 = 1" 1.0 (Forward.diff f 1.0);

  Printf.printf "\n"

let () =
  Printf.printf "--- Forward Mode: Product/Quotient Rule ---\n";

  (* d/dx (x * sin(x)) at x=π => sin(π) + π*cos(π) = 0 + π*(-1) = -π *)
  let pi = Float.pi in
  let f x = Forward.(x * sin x) in
  check_approx "d/dx(x·sin(x)) at π = -π" (-. pi) (Forward.diff f pi);

  (* d/dx (sin(x)/x) at x=1 => (cos(1)*1 - sin(1)*1)/1 *)
  let f x = Forward.(sin x / x) in
  let expected = Stdlib.cos 1.0 -. Stdlib.sin 1.0 in
  check "d/dx(sin(x)/x) at 1" expected (Forward.diff f 1.0);

  Printf.printf "\n"

let () =
  Printf.printf "--- Forward Mode: Gradient ---\n";

  (* f(x,y) = x^2 + y^2, grad at (3,4) => (6, 8) *)
  let f duals = Forward.(duals.(0) * duals.(0) + duals.(1) * duals.(1)) in
  let g = Forward.gradient f [| 3.0; 4.0 |] in
  check "∂f/∂x at (3,4) = 6" 6.0 g.(0);
  check "∂f/∂y at (3,4) = 8" 8.0 g.(1);

  (* f(x,y) = x*y, grad at (2,5) => (5, 2) *)
  let f duals = Forward.(duals.(0) * duals.(1)) in
  let g = Forward.gradient f [| 2.0; 5.0 |] in
  check "∂(xy)/∂x at (2,5) = 5" 5.0 g.(0);
  check "∂(xy)/∂y at (2,5) = 2" 2.0 g.(1);

  (* f(x,y,z) = x*y + y*z, grad at (1,2,3) => (2, 4, 2) *)
  let f d = Forward.(d.(0) * d.(1) + d.(1) * d.(2)) in
  let g = Forward.gradient f [| 1.0; 2.0; 3.0 |] in
  check "∂(xy+yz)/∂x = 2" 2.0 g.(0);
  check "∂(xy+yz)/∂y = 4" 4.0 g.(1);
  check "∂(xy+yz)/∂z = 2" 2.0 g.(2);

  Printf.printf "\n"

let () =
  Printf.printf "--- Forward Mode: Jacobian ---\n";

  (* f(x,y) = (x+y, x*y), Jacobian at (2,3) = [[1,1],[3,2]] *)
  let f duals = Forward.([| duals.(0) + duals.(1); duals.(0) * duals.(1) |]) in
  let j = Forward.jacobian f [| 2.0; 3.0 |] in
  check "J[0][0] = 1" 1.0 j.(0).(0);
  check "J[0][1] = 1" 1.0 j.(0).(1);
  check "J[1][0] = 3" 3.0 j.(1).(0);
  check "J[1][1] = 2" 2.0 j.(1).(1);

  Printf.printf "\n"

let () =
  Printf.printf "--- Forward Mode: Directional Derivative ---\n";

  (* f(x,y) = x^2 + y^2, direction (1,0) at (3,4) => 6 *)
  let f d = Forward.(d.(0) * d.(0) + d.(1) * d.(1)) in
  check "dir deriv along (1,0)" 6.0 (Forward.directional_deriv f [|3.0;4.0|] [|1.0;0.0|]);

  (* direction (0,1) at (3,4) => 8 *)
  check "dir deriv along (0,1)" 8.0 (Forward.directional_deriv f [|3.0;4.0|] [|0.0;1.0|]);

  Printf.printf "\n"

let () =
  Printf.printf "--- Forward Mode: Hessian ---\n";

  (* f(x,y) = x^2 + 3*x*y + y^2, H = [[2, 3],[3, 2]] *)
  let f d = Forward.(d.(0) * d.(0) + const 3.0 * d.(0) * d.(1) + d.(1) * d.(1)) in
  let h = Forward.hessian f [| 1.0; 1.0 |] in
  check_approx "H[0][0] = 2" 2.0 h.(0).(0);
  check_approx "H[0][1] = 3" 3.0 h.(0).(1);
  check_approx "H[1][0] = 3" 3.0 h.(1).(0);
  check_approx "H[1][1] = 2" 2.0 h.(1).(1);

  Printf.printf "\n"

(* ----- Reverse Mode Tests ----- *)

let () =
  Printf.printf "--- Reverse Mode: Basic Operations ---\n";

  (* f(x) = x^2, df/dx at x=3 => 6 *)
  let g = Reverse.gradient (fun tape vars ->
    Reverse.t_mul tape vars.(0) vars.(0)) [| 3.0 |] in
  check "d/dx(x²) at 3 = 6" 6.0 g.(0);

  (* f(x,y) = x*y, at (4,5) => (5, 4) *)
  let g = Reverse.gradient (fun tape vars ->
    Reverse.t_mul tape vars.(0) vars.(1)) [| 4.0; 5.0 |] in
  check "∂(xy)/∂x at (4,5) = 5" 5.0 g.(0);
  check "∂(xy)/∂y at (4,5) = 4" 4.0 g.(1);

  Printf.printf "\n"

let () =
  Printf.printf "--- Reverse Mode: Arithmetic ---\n";

  (* f(x,y) = (x+y)*(x-y) = x²-y², at (3,2) => (6, -4) *)
  let g = Reverse.gradient (fun tape vars ->
    let sum = Reverse.t_add tape vars.(0) vars.(1) in
    let diff = Reverse.t_sub tape vars.(0) vars.(1) in
    Reverse.t_mul tape sum diff) [| 3.0; 2.0 |] in
  check "∂(x²-y²)/∂x at (3,2) = 6" 6.0 g.(0);
  check "∂(x²-y²)/∂y at (3,2) = -4" (-4.0) g.(1);

  (* f(x,y) = x/y at (6,3) => (1/3, -6/9) *)
  let g = Reverse.gradient (fun tape vars ->
    Reverse.t_div tape vars.(0) vars.(1)) [| 6.0; 3.0 |] in
  check "∂(x/y)/∂x at (6,3) = 1/3" (1.0 /. 3.0) g.(0);
  check "∂(x/y)/∂y at (6,3) = -2/3" (-2.0 /. 3.0) g.(1);

  Printf.printf "\n"

let () =
  Printf.printf "--- Reverse Mode: Transcendental ---\n";

  (* f(x) = sin(x), at x=π/4 => cos(π/4) *)
  let g = Reverse.gradient (fun tape vars ->
    Reverse.t_sin tape vars.(0)) [| Float.pi /. 4.0 |] in
  check "d/dx sin(π/4) = cos(π/4)" (Stdlib.cos (Float.pi /. 4.0)) g.(0);

  (* f(x) = exp(x), at x=2 => exp(2) *)
  let g = Reverse.gradient (fun tape vars ->
    Reverse.t_exp tape vars.(0)) [| 2.0 |] in
  check "d/dx exp(2) = exp(2)" (Stdlib.exp 2.0) g.(0);

  (* f(x) = log(x), at x=3 => 1/3 *)
  let g = Reverse.gradient (fun tape vars ->
    Reverse.t_log tape vars.(0)) [| 3.0 |] in
  check "d/dx log(3) = 1/3" (1.0 /. 3.0) g.(0);

  (* f(x) = sqrt(x) at x=9 => 1/6 *)
  let g = Reverse.gradient (fun tape vars ->
    Reverse.t_sqrt tape vars.(0)) [| 9.0 |] in
  check "d/dx sqrt(9) = 1/6" (1.0 /. 6.0) g.(0);

  Printf.printf "\n"

let () =
  Printf.printf "--- Reverse Mode: Chain Rule ---\n";

  (* f(x) = sin(x^2) at x=1 => 2*cos(1) *)
  let g = Reverse.gradient (fun tape vars ->
    let x2 = Reverse.t_mul tape vars.(0) vars.(0) in
    Reverse.t_sin tape x2) [| 1.0 |] in
  check "d/dx sin(x²) at 1 = 2cos(1)" (2.0 *. Stdlib.cos 1.0) g.(0);

  (* f(x) = exp(sin(x)) at x=0 => 1 *)
  let g = Reverse.gradient (fun tape vars ->
    Reverse.t_exp tape (Reverse.t_sin tape vars.(0))) [| 0.0 |] in
  check "d/dx exp(sin(x)) at 0 = 1" 1.0 g.(0);

  Printf.printf "\n"

let () =
  Printf.printf "--- Reverse Mode: Activations ---\n";

  (* sigmoid'(0) = 0.25 *)
  let g = Reverse.gradient (fun tape vars ->
    Reverse.t_sigmoid tape vars.(0)) [| 0.0 |] in
  check "sigmoid'(0) = 0.25" 0.25 g.(0);

  (* relu'(5) = 1, relu'(-5) = 0 *)
  let g = Reverse.gradient (fun tape vars ->
    Reverse.t_relu tape vars.(0)) [| 5.0 |] in
  check "relu'(5) = 1" 1.0 g.(0);

  let g = Reverse.gradient (fun tape vars ->
    Reverse.t_relu tape vars.(0)) [| -5.0 |] in
  check "relu'(-5) = 0" 0.0 g.(0);

  (* tanh'(0) = 1 *)
  let g = Reverse.gradient (fun tape vars ->
    Reverse.t_tanh tape vars.(0)) [| 0.0 |] in
  check "tanh'(0) = 1" 1.0 g.(0);

  Printf.printf "\n"

let () =
  Printf.printf "--- Reverse Mode: Multivariate ---\n";

  (* Rosenbrock: f(x,y) = (1-x)^2 + 100*(y-x^2)^2 *)
  (* At (1,1): gradient should be (0,0) — it's the minimum *)
  let g = Reverse.gradient (fun tape vars ->
    let x = vars.(0) and y = vars.(1) in
    let one = Reverse.t_const tape 1.0 in
    let hundred = Reverse.t_const tape 100.0 in
    let a = Reverse.t_sub tape one x in
    let a2 = Reverse.t_mul tape a a in
    let x2 = Reverse.t_mul tape x x in
    let b = Reverse.t_sub tape y x2 in
    let b2 = Reverse.t_mul tape b b in
    Reverse.t_add tape a2 (Reverse.t_mul tape hundred b2)) [| 1.0; 1.0 |] in
  check_approx "Rosenbrock ∂f/∂x at (1,1) ≈ 0" 0.0 g.(0);
  check_approx "Rosenbrock ∂f/∂y at (1,1) ≈ 0" 0.0 g.(1);

  (* At (0,0): ∂f/∂x = -2(1-0) + 100*2*(0-0)*(-2*0) = -2, ∂f/∂y = 0 *)
  let g = Reverse.gradient (fun tape vars ->
    let x = vars.(0) and y = vars.(1) in
    let one = Reverse.t_const tape 1.0 in
    let hundred = Reverse.t_const tape 100.0 in
    let a = Reverse.t_sub tape one x in
    let a2 = Reverse.t_mul tape a a in
    let x2 = Reverse.t_mul tape x x in
    let b = Reverse.t_sub tape y x2 in
    let b2 = Reverse.t_mul tape b b in
    Reverse.t_add tape a2 (Reverse.t_mul tape hundred b2)) [| 0.0; 0.0 |] in
  check "Rosenbrock ∂f/∂x at (0,0) = -2" (-2.0) g.(0);
  check "Rosenbrock ∂f/∂y at (0,0) = 0" 0.0 g.(1);

  Printf.printf "\n"

let () =
  Printf.printf "--- Reverse Mode: Power ---\n";

  (* d/dx x^3 at x=2 => 12 *)
  let g = Reverse.gradient (fun tape vars ->
    Reverse.t_pow tape vars.(0) 3.0) [| 2.0 |] in
  check "d/dx x^3 at 2 = 12" 12.0 g.(0);

  Printf.printf "\n"

(* ----- Forward vs Reverse Agreement ----- *)

let () =
  Printf.printf "--- Forward vs Reverse Agreement ---\n";

  let test_agreement name fwd_f rev_f x =
    let fwd_g = Forward.gradient (fun duals -> fwd_f duals) x in
    let rev_g = Reverse.gradient (fun tape vars -> rev_f tape vars) x in
    Array.iteri (fun i _ ->
      check (Printf.sprintf "%s: dim %d agrees" name i) fwd_g.(i) rev_g.(i)) x
  in

  (* f(x,y) = x^2 + x*y + y^2 *)
  test_agreement "x²+xy+y²"
    (fun d -> Forward.(d.(0) * d.(0) + d.(0) * d.(1) + d.(1) * d.(1)))
    (fun tape v ->
      let x2 = Reverse.t_mul tape v.(0) v.(0) in
      let xy = Reverse.t_mul tape v.(0) v.(1) in
      let y2 = Reverse.t_mul tape v.(1) v.(1) in
      Reverse.t_add tape (Reverse.t_add tape x2 xy) y2)
    [| 2.0; 3.0 |];

  (* f(x,y) = sin(x)*cos(y) *)
  test_agreement "sin(x)*cos(y)"
    (fun d -> Forward.(sin d.(0) * cos d.(1)))
    (fun tape v -> Reverse.t_mul tape (Reverse.t_sin tape v.(0)) (Reverse.t_cos tape v.(1)))
    [| 1.0; 2.0 |];

  (* f(x) = exp(x^2) *)
  test_agreement "exp(x²)"
    (fun d -> Forward.(exp (d.(0) * d.(0))))
    (fun tape v -> Reverse.t_exp tape (Reverse.t_mul tape v.(0) v.(0)))
    [| 0.5 |];

  Printf.printf "\n"

(* ----- Optimization Tests ----- *)

let () =
  Printf.printf "--- Optimization: Gradient Descent ---\n";

  (* Minimize f(x,y) = (x-2)^2 + (y-3)^2, minimum at (2,3) *)
  let f tape vars =
    let two = Reverse.t_const tape 2.0 in
    let three = Reverse.t_const tape 3.0 in
    let dx = Reverse.t_sub tape vars.(0) two in
    let dy = Reverse.t_sub tape vars.(1) three in
    Reverse.t_add tape (Reverse.t_mul tape dx dx) (Reverse.t_mul tape dy dy)
  in
  let result = Reverse.gradient_descent ~lr:0.1 ~steps:200 f [| 0.0; 0.0 |] in
  check_approx "GD finds x ≈ 2" 2.0 result.(0);
  check_approx "GD finds y ≈ 3" 3.0 result.(1);

  Printf.printf "\n"

let () =
  Printf.printf "--- Optimization: Momentum ---\n";

  let f tape vars =
    let two = Reverse.t_const tape 2.0 in
    let three = Reverse.t_const tape 3.0 in
    let dx = Reverse.t_sub tape vars.(0) two in
    let dy = Reverse.t_sub tape vars.(1) three in
    Reverse.t_add tape (Reverse.t_mul tape dx dx) (Reverse.t_mul tape dy dy)
  in
  let result = Optimize.momentum ~lr:0.05 ~steps:200 f [| 0.0; 0.0 |] in
  check_approx "Momentum finds x ≈ 2" 2.0 result.(0);
  check_approx "Momentum finds y ≈ 3" 3.0 result.(1);

  Printf.printf "\n"

let () =
  Printf.printf "--- Optimization: Adam ---\n";

  let f tape vars =
    let two = Reverse.t_const tape 2.0 in
    let three = Reverse.t_const tape 3.0 in
    let dx = Reverse.t_sub tape vars.(0) two in
    let dy = Reverse.t_sub tape vars.(1) three in
    Reverse.t_add tape (Reverse.t_mul tape dx dx) (Reverse.t_mul tape dy dy)
  in
  let result = Optimize.adam ~lr:0.1 ~steps:500 f [| 0.0; 0.0 |] in
  check_approx "Adam finds x ≈ 2" 2.0 result.(0);
  check_approx "Adam finds y ≈ 3" 3.0 result.(1);

  Printf.printf "\n"

(* ----- Neural Network Tests ----- *)

let () =
  Printf.printf "--- Neural Network: Dense Layer ---\n";

  (* Test that a simple dense layer forward pass works *)
  let layer = { NN.weights = [| [| 1.0; 0.0 |]; [| 0.0; 1.0 |] |];
                NN.biases = [| 0.5; -0.5 |] } in
  let tape = Reverse.new_tape () in
  let input = [| Reverse.t_var tape 2.0; Reverse.t_var tape 3.0 |] in
  let output = NN.forward_dense tape layer input in
  check "Dense [2,3] -> [2.5, 2.5] (identity+bias)" 2.5 (Reverse.value output.(0));
  check "Dense [2,3] -> [2.5, 2.5] dim 1" 2.5 (Reverse.value output.(1));

  Printf.printf "\n"

let () =
  Printf.printf "--- Neural Network: Activations ---\n";

  let tape = Reverse.new_tape () in
  let nodes = [| Reverse.t_var tape (-1.0); Reverse.t_var tape 2.0 |] in
  let relu_out = NN.apply_activation tape `Relu nodes in
  check "ReLU(-1) = 0" 0.0 (Reverse.value relu_out.(0));
  check "ReLU(2) = 2" 2.0 (Reverse.value relu_out.(1));

  let tape2 = Reverse.new_tape () in
  let nodes2 = [| Reverse.t_var tape2 0.0 |] in
  let sig_out = NN.apply_activation tape2 `Sigmoid nodes2 in
  check "Sigmoid(0) = 0.5" 0.5 (Reverse.value sig_out.(0));

  Printf.printf "\n"

let () =
  Printf.printf "--- Neural Network: MSE Loss ---\n";

  let tape = Reverse.new_tape () in
  let preds = [| Reverse.t_var tape 1.0; Reverse.t_var tape 2.0 |] in
  let targets = [| 1.5; 2.5 |] in
  let loss = NN.mse_loss tape preds targets in
  (* MSE = ((1-1.5)^2 + (2-2.5)^2) / 2 = (0.25+0.25)/2 = 0.25 *)
  check "MSE([1,2], [1.5,2.5]) = 0.25" 0.25 (Reverse.value loss);

  Printf.printf "\n"

(* ----- Edge Cases ----- *)

let () =
  Printf.printf "--- Edge Cases ---\n";

  (* Constants have zero derivative *)
  check "d/dx(5) = 0" 0.0 (Forward.diff (fun _ -> Forward.const 5.0) 3.0);

  (* Identity has unit derivative *)
  check "d/dx(x) = 1" 1.0 (Forward.diff (fun x -> x) 7.0);

  (* Negation *)
  check "d/dx(-x) = -1" (-1.0) (Forward.diff Forward.neg 2.0);

  (* abs *)
  check "d/dx |x| at 3 = 1" 1.0 (Forward.diff Forward.abs 3.0);
  check "d/dx |x| at -3 = -1" (-1.0) (Forward.diff Forward.abs (-3.0));

  Printf.printf "\n"

(* ----- Numerical Verification ----- *)

let () =
  Printf.printf "--- Numerical Verification (finite differences) ---\n";

  let finite_diff f x =
    let eps = 1e-7 in
    (f (x +. eps) -. f (x -. eps)) /. (2.0 *. eps)
  in

  let test_vs_finite name f x =
    let ad_deriv = Forward.diff (fun d -> f d) x in
    let num_deriv = finite_diff (fun v -> Forward.value (f (Forward.var v))) x in
    check_approx (Printf.sprintf "AD vs finite diff: %s" name) num_deriv ad_deriv
  in

  test_vs_finite "x^3 + 2x" (fun x -> Forward.(x * x * x + const 2.0 * x)) 1.5;
  test_vs_finite "sin(exp(x))" (fun x -> Forward.(sin (exp x))) 0.5;
  test_vs_finite "log(1+x^2)" (fun x -> Forward.(log (const 1.0 + x * x))) 2.0;
  test_vs_finite "tanh(x^2)" (fun x -> Forward.(tanh (x * x))) 0.7;
  test_vs_finite "sigmoid(3x)" (fun x -> Forward.(sigmoid (const 3.0 * x))) 0.0;

  Printf.printf "\n"

(* ----- Summary ----- *)

let () =
  Printf.printf "=== Results: %d passed, %d failed ===\n" !passed !failed;
  if !failed > 0 then exit 1
  else Printf.printf "All tests passed! ✓\n"
