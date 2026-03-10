(* neural_network.ml — Feedforward Neural Network with Backpropagation
 *
 * A from-scratch implementation of a multilayer perceptron (MLP) in OCaml.
 * No external dependencies — uses only the standard library.
 *
 * Features:
 *   - Configurable layer sizes (arbitrary depth)
 *   - Multiple activation functions: sigmoid, tanh, relu, leaky_relu, softmax
 *   - Xavier/He weight initialization
 *   - Backpropagation with gradient descent
 *   - Batch and stochastic training
 *   - Loss functions: MSE, cross-entropy
 *   - Learning rate scheduling (constant, decay, step)
 *   - Momentum and gradient clipping
 *   - Training history tracking
 *   - Model serialization (save/load weights)
 *   - Demo: XOR, AND, OR, circle classification
 *)

(* ── Random utilities ──────────────────────────────────────────────── *)

let () = Random.self_init ()

(** Box-Muller transform for normally distributed random numbers. *)
let rand_normal ?(mu = 0.0) ?(sigma = 1.0) () =
  let u1 = Random.float 1.0 in
  let u2 = Random.float 1.0 in
  let u1 = if u1 < 1e-10 then 1e-10 else u1 in
  mu +. sigma *. sqrt (-2.0 *. log u1) *. cos (2.0 *. Float.pi *. u2)

(* ── Activation functions ──────────────────────────────────────────── *)

type activation =
  | Sigmoid
  | Tanh
  | Relu
  | LeakyRelu of float
  | Linear
  | Softmax

let activate act x =
  match act with
  | Sigmoid -> 1.0 /. (1.0 +. exp (-.x))
  | Tanh -> tanh x
  | Relu -> if x > 0.0 then x else 0.0
  | LeakyRelu alpha -> if x > 0.0 then x else alpha *. x
  | Linear -> x
  | Softmax -> x

let activate_deriv act output =
  match act with
  | Sigmoid -> output *. (1.0 -. output)
  | Tanh -> 1.0 -. output *. output
  | Relu -> if output > 0.0 then 1.0 else 0.0
  | LeakyRelu alpha -> if output > 0.0 then 1.0 else alpha
  | Linear -> 1.0
  | Softmax -> 1.0

let softmax arr =
  let max_val = Array.fold_left max neg_infinity arr in
  let exps = Array.map (fun x -> exp (x -. max_val)) arr in
  let sum = Array.fold_left (+.) 0.0 exps in
  Array.map (fun e -> e /. sum) exps

(* ── Loss functions ────────────────────────────────────────────────── *)

type loss_fn = MSE | CrossEntropy

let compute_loss loss_fn predicted target =
  let n = Array.length predicted in
  match loss_fn with
  | MSE ->
    let sum = ref 0.0 in
    for i = 0 to n - 1 do
      let d = predicted.(i) -. target.(i) in
      sum := !sum +. d *. d
    done;
    !sum /. float_of_int n
  | CrossEntropy ->
    let sum = ref 0.0 in
    let eps = 1e-15 in
    for i = 0 to n - 1 do
      let p = max eps (min (1.0 -. eps) predicted.(i)) in
      sum := !sum -. (target.(i) *. log p +. (1.0 -. target.(i)) *. log (1.0 -. p))
    done;
    !sum /. float_of_int n

let loss_gradient loss_fn predicted target =
  let n = Array.length predicted in
  match loss_fn with
  | MSE ->
    Array.init n (fun i ->
      2.0 *. (predicted.(i) -. target.(i)) /. float_of_int n)
  | CrossEntropy ->
    let eps = 1e-15 in
    Array.init n (fun i ->
      let p = max eps (min (1.0 -. eps) predicted.(i)) in
      (-. target.(i) /. p +. (1.0 -. target.(i)) /. (1.0 -. p)) /. float_of_int n)

(* ── Layer ─────────────────────────────────────────────────────────── *)

type layer = {
  input_size : int;
  output_size : int;
  weights : float array array;
  biases : float array;
  activation : activation;
  mutable pre_activation : float array;
  mutable output : float array;
  mutable weight_grads : float array array;
  mutable bias_grads : float array;
  mutable weight_velocity : float array array;
  mutable bias_velocity : float array;
}

let create_layer input_size output_size act =
  let scale = match act with
    | Relu | LeakyRelu _ -> sqrt (2.0 /. float_of_int input_size)
    | _ -> sqrt (2.0 /. float_of_int (input_size + output_size))
  in
  {
    input_size; output_size;
    weights = Array.init output_size (fun _ ->
      Array.init input_size (fun _ -> rand_normal ~sigma:scale ()));
    biases = Array.make output_size 0.0;
    activation = act;
    pre_activation = Array.make output_size 0.0;
    output = Array.make output_size 0.0;
    weight_grads = Array.init output_size (fun _ -> Array.make input_size 0.0);
    bias_grads = Array.make output_size 0.0;
    weight_velocity = Array.init output_size (fun _ -> Array.make input_size 0.0);
    bias_velocity = Array.make output_size 0.0;
  }

let layer_forward layer input =
  let out = Array.make layer.output_size 0.0 in
  for j = 0 to layer.output_size - 1 do
    let sum = ref layer.biases.(j) in
    for i = 0 to layer.input_size - 1 do
      sum := !sum +. layer.weights.(j).(i) *. input.(i)
    done;
    out.(j) <- !sum
  done;
  layer.pre_activation <- Array.copy out;
  let activated = match layer.activation with
    | Softmax -> softmax out
    | _ -> Array.map (activate layer.activation) out
  in
  layer.output <- activated;
  activated

(* ── Network ───────────────────────────────────────────────────────── *)

type lr_schedule =
  | Constant of float
  | Decay of float * float
  | StepDecay of float * float * int

type network_config = {
  layer_sizes : int list;
  activations : activation list;
  loss : loss_fn;
  lr_schedule : lr_schedule;
  momentum : float;
  gradient_clip : float option;
}

type training_history = {
  mutable epoch_losses : float list;
  mutable best_loss : float;
  mutable best_epoch : int;
}

type network = {
  layers : layer array;
  config : network_config;
  history : training_history;
}

let create_network config =
  let sizes = config.layer_sizes in
  let n_layers = List.length sizes - 1 in
  if n_layers < 1 then
    failwith "Network must have at least 2 layer sizes (input, output)";
  if List.length config.activations <> n_layers then
    failwith (Printf.sprintf "Expected %d activations, got %d"
      n_layers (List.length config.activations));
  let sizes_arr = Array.of_list sizes in
  let acts_arr = Array.of_list config.activations in
  let layers = Array.init n_layers (fun i ->
    create_layer sizes_arr.(i) sizes_arr.(i + 1) acts_arr.(i)
  ) in
  { layers; config;
    history = { epoch_losses = []; best_loss = infinity; best_epoch = 0 } }

let forward net input =
  let current = ref input in
  for i = 0 to Array.length net.layers - 1 do
    current := layer_forward net.layers.(i) !current
  done;
  !current

let get_lr config epoch =
  match config.lr_schedule with
  | Constant lr -> lr
  | Decay (lr0, decay) -> lr0 *. (1.0 /. (1.0 +. decay *. float_of_int epoch))
  | StepDecay (lr0, factor, step) ->
    lr0 *. (factor ** float_of_int (epoch / step))

let clip_gradient clip_opt g =
  match clip_opt with
  | None -> g
  | Some max_g ->
    if g > max_g then max_g
    else if g < -.max_g then -.max_g
    else g

let backward net input target =
  let n_layers = Array.length net.layers in
  let predicted = net.layers.(n_layers - 1).output in
  let loss = compute_loss net.config.loss predicted target in
  let output_grad = loss_gradient net.config.loss predicted target in
  let deltas = Array.make n_layers [||] in
  let out_layer = net.layers.(n_layers - 1) in
  deltas.(n_layers - 1) <- Array.init out_layer.output_size (fun j ->
    output_grad.(j) *. activate_deriv out_layer.activation out_layer.output.(j));
  for l = n_layers - 2 downto 0 do
    let layer = net.layers.(l) in
    let next_layer = net.layers.(l + 1) in
    let next_delta = deltas.(l + 1) in
    deltas.(l) <- Array.init layer.output_size (fun j ->
      let sum = ref 0.0 in
      for k = 0 to next_layer.output_size - 1 do
        sum := !sum +. next_delta.(k) *. next_layer.weights.(k).(j)
      done;
      !sum *. activate_deriv layer.activation layer.output.(j))
  done;
  for l = 0 to n_layers - 1 do
    let layer = net.layers.(l) in
    let delta = deltas.(l) in
    let layer_input = if l = 0 then input else net.layers.(l - 1).output in
    for j = 0 to layer.output_size - 1 do
      layer.bias_grads.(j) <- delta.(j);
      for i = 0 to layer.input_size - 1 do
        layer.weight_grads.(j).(i) <- delta.(j) *. layer_input.(i)
      done
    done
  done;
  loss

let apply_gradients net lr =
  let momentum = net.config.momentum in
  let clip = net.config.gradient_clip in
  Array.iter (fun layer ->
    for j = 0 to layer.output_size - 1 do
      let bg = clip_gradient clip layer.bias_grads.(j) in
      layer.bias_velocity.(j) <- momentum *. layer.bias_velocity.(j) -. lr *. bg;
      layer.biases.(j) <- layer.biases.(j) +. layer.bias_velocity.(j);
      for i = 0 to layer.input_size - 1 do
        let wg = clip_gradient clip layer.weight_grads.(j).(i) in
        layer.weight_velocity.(j).(i) <-
          momentum *. layer.weight_velocity.(j).(i) -. lr *. wg;
        layer.weights.(j).(i) <-
          layer.weights.(j).(i) +. layer.weight_velocity.(j).(i)
      done
    done
  ) net.layers

let shuffle arr =
  let n = Array.length arr in
  for i = n - 1 downto 1 do
    let j = Random.int (i + 1) in
    let tmp = arr.(i) in
    arr.(i) <- arr.(j);
    arr.(j) <- tmp
  done

let train ?(batch_size = 0) ?(verbose = 0) net data epochs =
  let n = Array.length data in
  if n = 0 then failwith "Training data is empty";
  let indices = Array.init n (fun i -> i) in
  for epoch = 0 to epochs - 1 do
    shuffle indices;
    let lr = get_lr net.config epoch in
    let total_loss = ref 0.0 in
    let bs = if batch_size <= 0 || batch_size > n then n else batch_size in
    let batches = (n + bs - 1) / bs in
    for batch = 0 to batches - 1 do
      let start_idx = batch * bs in
      let end_idx = min n ((batch + 1) * bs) in
      Array.iter (fun layer ->
        Array.iter (fun wg -> Array.fill wg 0 (Array.length wg) 0.0) layer.weight_grads;
        Array.fill layer.bias_grads 0 layer.output_size 0.0
      ) net.layers;
      let batch_loss = ref 0.0 in
      let batch_count = end_idx - start_idx in
      for s = start_idx to end_idx - 1 do
        let (input, target) = data.(indices.(s)) in
        let _ = forward net input in
        let loss = backward net input target in
        batch_loss := !batch_loss +. loss
      done;
      let scale = 1.0 /. float_of_int batch_count in
      Array.iter (fun layer ->
        Array.iteri (fun j wg ->
          Array.iteri (fun i _ -> wg.(i) <- wg.(i) *. scale) wg;
          layer.bias_grads.(j) <- layer.bias_grads.(j) *. scale
        ) layer.weight_grads
      ) net.layers;
      apply_gradients net lr;
      total_loss := !total_loss +. !batch_loss
    done;
    let avg_loss = !total_loss /. float_of_int n in
    net.history.epoch_losses <- avg_loss :: net.history.epoch_losses;
    if avg_loss < net.history.best_loss then begin
      net.history.best_loss <- avg_loss;
      net.history.best_epoch <- epoch
    end;
    if verbose > 0 && (epoch mod verbose = 0 || epoch = epochs - 1) then
      Printf.printf "Epoch %4d | Loss: %.6f | LR: %.6f\n" epoch avg_loss lr
  done;
  match net.history.epoch_losses with
  | loss :: _ -> loss
  | [] -> infinity

let predict net input = forward net input

let classify net input =
  let output = predict net input in
  let best_idx = ref 0 in
  let best_val = ref output.(0) in
  for i = 1 to Array.length output - 1 do
    if output.(i) > !best_val then begin
      best_val := output.(i);
      best_idx := i
    end
  done;
  !best_idx

let accuracy net data =
  let n = Array.length data in
  if n = 0 then 0.0
  else begin
    let correct = ref 0 in
    Array.iter (fun (input, target) ->
      let pred_idx = classify net input in
      let true_idx = ref 0 in
      let best = ref target.(0) in
      for i = 1 to Array.length target - 1 do
        if target.(i) > !best then begin
          best := target.(i);
          true_idx := i
        end
      done;
      if pred_idx = !true_idx then incr correct
    ) data;
    float_of_int !correct /. float_of_int n
  end

(* ── Serialization ─────────────────────────────────────────────────── *)

let export_weights net =
  let acc = ref [] in
  Array.iter (fun layer ->
    Array.iter (fun row ->
      Array.iter (fun w -> acc := w :: !acc) row
    ) layer.weights;
    Array.iter (fun b -> acc := b :: !acc) layer.biases
  ) net.layers;
  List.rev !acc

let import_weights net weights =
  let ws = ref weights in
  let take () =
    match !ws with
    | [] -> failwith "Not enough weights"
    | w :: rest -> ws := rest; w
  in
  Array.iter (fun layer ->
    for j = 0 to layer.output_size - 1 do
      for i = 0 to layer.input_size - 1 do
        layer.weights.(j).(i) <- take ()
      done
    done;
    for j = 0 to layer.output_size - 1 do
      layer.biases.(j) <- take ()
    done
  ) net.layers

let param_count net =
  Array.fold_left (fun acc layer ->
    acc + layer.input_size * layer.output_size + layer.output_size
  ) 0 net.layers

let print_summary net =
  Printf.printf "Neural Network Summary\n";
  Printf.printf "------------------------------------------------------\n";
  let act_name = function
    | Sigmoid -> "sigmoid" | Tanh -> "tanh" | Relu -> "relu"
    | LeakyRelu a -> Printf.sprintf "leaky_relu(%.2f)" a
    | Linear -> "linear" | Softmax -> "softmax"
  in
  Array.iteri (fun i layer ->
    Printf.printf "Layer %d: %d -> %d  [%s]\n"
      i layer.input_size layer.output_size (act_name layer.activation)
  ) net.layers;
  Printf.printf "------------------------------------------------------\n";
  Printf.printf "Total parameters: %d\n" (param_count net)

let loss_history net = List.rev net.history.epoch_losses

let has_converged ?(threshold = 1e-6) net =
  match net.history.epoch_losses with
  | a :: b :: _ -> abs_float (a -. b) < threshold
  | _ -> false

let best_epoch net = (net.history.best_epoch, net.history.best_loss)

let create_simple ~input_size ~hidden_sizes ~output_size
    ?(hidden_act = Relu) ?(output_act = Sigmoid) ?(lr = 0.01)
    ?(momentum = 0.9) ?(loss = MSE) () =
  let sizes = [input_size] @ hidden_sizes @ [output_size] in
  let n_hidden = List.length hidden_sizes in
  let activations =
    List.init n_hidden (fun _ -> hidden_act) @ [output_act]
  in
  create_network {
    layer_sizes = sizes; activations; loss;
    lr_schedule = Constant lr; momentum;
    gradient_clip = Some 5.0;
  }

(* ── Demos ─────────────────────────────────────────────────────────── *)

let demo_xor () =
  Printf.printf "\n=== XOR Demo ===\n";
  let net = create_simple
    ~input_size:2 ~hidden_sizes:[8; 4] ~output_size:1
    ~hidden_act:Sigmoid ~output_act:Sigmoid ~lr:0.5 ~momentum:0.0
    ~loss:MSE ()
  in
  print_summary net;
  let data = [|
    ([| 0.0; 0.0 |], [| 0.0 |]);
    ([| 0.0; 1.0 |], [| 1.0 |]);
    ([| 1.0; 0.0 |], [| 1.0 |]);
    ([| 1.0; 1.0 |], [| 0.0 |]);
  |] in
  let final_loss = train ~verbose:500 net data 3000 in
  Printf.printf "\nFinal loss: %.6f\n" final_loss;
  Printf.printf "\nPredictions:\n";
  Array.iter (fun (input, target) ->
    let output = predict net input in
    let rounded = if output.(0) > 0.5 then 1 else 0 in
    Printf.printf "  [%.0f, %.0f] -> %.4f (rounded: %d, expected: %.0f) %s\n"
      input.(0) input.(1) output.(0) rounded target.(0)
      (if float_of_int rounded = target.(0) then "OK" else "WRONG")
  ) data

let demo_gates () =
  Printf.printf "\n=== Logic Gates Demo ===\n";
  let gate_data op_name op =
    let data = [|
      ([| 0.0; 0.0 |], [| if op 0 0 then 1.0 else 0.0 |]);
      ([| 0.0; 1.0 |], [| if op 0 1 then 1.0 else 0.0 |]);
      ([| 1.0; 0.0 |], [| if op 1 0 then 1.0 else 0.0 |]);
      ([| 1.0; 1.0 |], [| if op 1 1 then 1.0 else 0.0 |]);
    |] in
    let net = create_simple
      ~input_size:2 ~hidden_sizes:[4] ~output_size:1
      ~hidden_act:Sigmoid ~output_act:Sigmoid ~lr:1.0 ~momentum:0.0
      ~loss:MSE ()
    in
    let _ = train net data 1000 in
    Printf.printf "%s gate:\n" op_name;
    Array.iter (fun (input, target) ->
      let output = predict net input in
      Printf.printf "  [%.0f, %.0f] -> %.4f (expected: %.0f)\n"
        input.(0) input.(1) output.(0) target.(0)
    ) data
  in
  gate_data "AND" (fun a b -> a = 1 && b = 1);
  gate_data "OR" (fun a b -> a = 1 || b = 1)

let demo_circle () =
  Printf.printf "\n=== Circle Classification Demo ===\n";
  let net = create_simple
    ~input_size:2 ~hidden_sizes:[16; 8] ~output_size:2
    ~hidden_act:Relu ~output_act:Softmax ~lr:0.01 ~momentum:0.9
    ~loss:CrossEntropy ()
  in
  print_summary net;
  let n_samples = 200 in
  let data = Array.init n_samples (fun _ ->
    let x = Random.float 2.0 -. 1.0 in
    let y = Random.float 2.0 -. 1.0 in
    let inside = x *. x +. y *. y < 0.25 in
    let target = if inside then [| 1.0; 0.0 |] else [| 0.0; 1.0 |] in
    ([| x; y |], target)
  ) in
  let final_loss = train ~batch_size:32 ~verbose:100 net data 500 in
  let acc = accuracy net data in
  Printf.printf "\nFinal loss: %.6f | Accuracy: %.1f%%\n" final_loss (acc *. 100.0);
  Printf.printf "\nSample predictions:\n";
  let test_points = [|
    [| 0.0; 0.0 |]; [| 0.1; 0.1 |]; [| 0.8; 0.8 |];
    [| -0.9; 0.9 |]; [| 0.3; 0.3 |];
  |] in
  Array.iter (fun pt ->
    let cls = classify net pt in
    let label = if cls = 0 then "inside" else "outside" in
    Printf.printf "  (%.1f, %.1f) -> %s\n" pt.(0) pt.(1) label
  ) test_points

let demo_lr_schedules () =
  Printf.printf "\n=== Learning Rate Schedules Demo ===\n";
  let data = [|
    ([| 0.0; 0.0 |], [| 0.0 |]);
    ([| 0.0; 1.0 |], [| 1.0 |]);
    ([| 1.0; 0.0 |], [| 1.0 |]);
    ([| 1.0; 1.0 |], [| 0.0 |]);
  |] in
  let schedules = [
    ("Constant 0.5", Constant 0.5);
    ("Decay (0.5, 0.01)", Decay (0.5, 0.01));
    ("StepDecay (0.5, 0.5, 500)", StepDecay (0.5, 0.5, 500));
  ] in
  List.iter (fun (name, schedule) ->
    let net = create_network {
      layer_sizes = [2; 8; 1];
      activations = [Sigmoid; Sigmoid];
      loss = MSE; lr_schedule = schedule;
      momentum = 0.0; gradient_clip = None;
    } in
    let final_loss = train net data 2000 in
    let (best_ep, best_l) = best_epoch net in
    Printf.printf "  %-30s -> final=%.6f  best=%.6f@epoch%d\n"
      name final_loss best_l best_ep
  ) schedules

let () =
  Printf.printf "==================================================\n";
  Printf.printf "   Neural Network from Scratch -- OCaml Edition    \n";
  Printf.printf "==================================================\n";
  demo_xor ();
  demo_gates ();
  demo_circle ();
  demo_lr_schedules ();
  Printf.printf "\n==== All demos complete ====\n";
  Printf.printf "\nModule exports:\n";
  Printf.printf "  Activations: sigmoid, tanh, relu, leaky_relu, linear, softmax\n";
  Printf.printf "  Loss:        MSE, cross-entropy\n";
  Printf.printf "  LR:          constant, decay, step decay\n";
  Printf.printf "  Features:    momentum, gradient clipping, batch training\n";
  Printf.printf "  Utilities:   export/import weights, param count, convergence check\n"
