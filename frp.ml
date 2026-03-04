(* frp.ml — Functional Reactive Programming *)
(* Signals, behaviors, events, combinators, and reactive systems *)

(* ──────────────────────────────────────── *)
(* Core Types                               *)
(* ──────────────────────────────────────── *)

type time = float

(** A behavior is a time-varying value: time → value *)
type 'a behavior = Behavior of (time -> 'a)

(** An event is a list of time-stamped occurrences *)
type 'a event = Event of (time * 'a) list

(** A signal is a discrete-time varying value with change notification *)
type 'a signal = {
  mutable value: 'a;
  mutable listeners: ('a -> unit) list;
}

(** A reactive cell with dependency tracking *)
type 'a cell = {
  mutable cell_value: 'a;
  mutable cell_deps: (unit -> unit) list;
  mutable cell_dirty: bool;
}

(* ──────────────────────────────────────── *)
(* Behavior Combinators                     *)
(* ──────────────────────────────────────── *)

module Behavior = struct
  (** Create a constant behavior *)
  let constant x = Behavior (fun _ -> x)

  (** Create a behavior from a function of time *)
  let of_fun f = Behavior f

  (** Sample a behavior at a given time *)
  let sample (Behavior f) t = f t

  (** Map a function over a behavior *)
  let map f (Behavior b) = Behavior (fun t -> f (b t))

  (** Applicative: apply a behavior of functions to a behavior of values *)
  let apply (Behavior bf) (Behavior bx) =
    Behavior (fun t -> (bf t) (bx t))

  (** Combine two behaviors with a function *)
  let map2 f b1 b2 = apply (map f b1) b2

  (** Combine three behaviors *)
  let map3 f b1 b2 b3 = apply (map2 f b1 b2) b3

  (** Monadic bind: behavior that depends on another behavior's value *)
  let bind (Behavior b) f =
    Behavior (fun t ->
      let (Behavior b') = f (b t) in
      b' t)

  (** Join a behavior of behaviors *)
  let join bb = bind bb (fun x -> x)

  (** Time-varying identity: returns current time *)
  let time = Behavior (fun t -> t)

  (** Integral approximation using Riemann sum *)
  let integral ?(dt=0.01) (Behavior f) =
    Behavior (fun t ->
      let steps = int_of_float (t /. dt) in
      let sum = ref 0.0 in
      for i = 0 to steps - 1 do
        sum := !sum +. f (float_of_int i *. dt) *. dt
      done;
      !sum)

  (** Derivative approximation *)
  let derivative ?(dt=0.001) (Behavior f) =
    Behavior (fun t ->
      (f (t +. dt) -. f t) /. dt)

  (** Delay a behavior by a time offset *)
  let delay offset (Behavior f) =
    Behavior (fun t -> f (t -. offset))

  (** Sample a behavior at regular intervals *)
  let sample_at interval duration b =
    let n = int_of_float (duration /. interval) in
    List.init (n + 1) (fun i ->
      let t = float_of_int i *. interval in
      (t, sample b t))

  (** Smooth a behavior using exponential moving average *)
  let smooth alpha (Behavior f) =
    let prev = ref None in
    Behavior (fun t ->
      let v = f t in
      match !prev with
      | None -> prev := Some v; v
      | Some p ->
        let smoothed = alpha *. v +. (1.0 -. alpha) *. p in
        prev := Some smoothed;
        smoothed)

  (** Clamp a float behavior to [lo, hi] *)
  let clamp lo hi b =
    map (fun x -> Float.max lo (Float.min hi x)) b

  (** Switch between behaviors based on a boolean behavior *)
  let switch (Behavior cond) (Behavior b_true) (Behavior b_false) =
    Behavior (fun t -> if cond t then b_true t else b_false t)

  (** Until: use first behavior until time threshold, then second *)
  let until threshold b1 b2 =
    switch (of_fun (fun t -> t < threshold)) b1 b2

  (** Piecewise behavior from sorted (time, behavior) list *)
  let piecewise segments =
    Behavior (fun t ->
      let rec find = function
        | [] -> 0.0  (* default *)
        | [(_, Behavior b)] -> b t
        | (t1, Behavior b1) :: ((t2, _) :: _ as rest) ->
          if t >= t1 && t < t2 then b1 t
          else find rest
      in
      find segments)

  (** Linear interpolation between two values over [t0, t1] *)
  let lerp t0 t1 v0 v1 =
    Behavior (fun t ->
      if t <= t0 then v0
      else if t >= t1 then v1
      else
        let frac = (t -. t0) /. (t1 -. t0) in
        v0 +. frac *. (v1 -. v0))
end

(* ──────────────────────────────────────── *)
(* Event Combinators                        *)
(* ──────────────────────────────────────── *)

module EventOps = struct
  (** Empty event stream *)
  let never = Event []

  (** Create an event with a single occurrence *)
  let once t v = Event [(t, v)]

  (** Create events from a list of (time, value) pairs *)
  let of_list pairs =
    Event (List.sort (fun (t1, _) (t2, _) -> compare t1 t2) pairs)

  (** Get all occurrences *)
  let occurrences (Event es) = es

  (** Map a function over event values *)
  let map f (Event es) =
    Event (List.map (fun (t, v) -> (t, f v)) es)

  (** Filter events by a predicate *)
  let filter pred (Event es) =
    Event (List.filter (fun (_, v) -> pred v) es)

  (** Filter and map simultaneously *)
  let filter_map f (Event es) =
    Event (List.filter_map (fun (t, v) ->
      match f v with
      | Some v' -> Some (t, v')
      | None -> None) es)

  (** Merge two event streams (union, sorted by time) *)
  let merge (Event es1) (Event es2) =
    Event (List.sort (fun (t1, _) (t2, _) -> compare t1 t2) (es1 @ es2))

  (** Scan (fold) over events, producing a behavior *)
  let scan init f (Event es) =
    Behavior.of_fun (fun t ->
      List.fold_left (fun acc (te, v) ->
        if te <= t then f acc v else acc
      ) init es)

  (** Count occurrences up to time t *)
  let count (Event es) =
    Behavior.of_fun (fun t ->
      List.length (List.filter (fun (te, _) -> te <= t) es))

  (** Get the last event value before time t, or default *)
  let hold default (Event es) =
    Behavior.of_fun (fun t ->
      let before = List.filter (fun (te, _) -> te <= t) es in
      match List.rev before with
      | (_, v) :: _ -> v
      | [] -> default)

  (** Delay all events by a time offset *)
  let delay offset (Event es) =
    Event (List.map (fun (t, v) -> (t +. offset, v)) es)

  (** Take only events in [t_start, t_end) *)
  let window t_start t_end (Event es) =
    Event (List.filter (fun (t, _) -> t >= t_start && t < t_end) es)

  (** Throttle: keep at most one event per interval *)
  let throttle interval (Event es) =
    let _, result = List.fold_left (fun (last_t, acc) (t, v) ->
      match last_t with
      | None -> (Some t, (t, v) :: acc)
      | Some lt ->
        if t -. lt >= interval then (Some t, (t, v) :: acc)
        else (last_t, acc)
    ) (None, []) es in
    Event (List.rev result)

  (** Debounce: only keep an event if no other follows within the interval *)
  let debounce interval (Event es) =
    let arr = Array.of_list es in
    let n = Array.length arr in
    let result = ref [] in
    for i = 0 to n - 1 do
      let (t, v) = arr.(i) in
      let has_next = i < n - 1 && fst arr.(i+1) -. t < interval in
      if not has_next then result := (t, v) :: !result
    done;
    Event (List.rev !result)

  (** Zip two event streams pairwise (by position) *)
  let zip (Event es1) (Event es2) =
    Event (List.map2 (fun (t1, v1) (_, v2) -> (t1, (v1, v2))) es1 es2)

  (** Accumulate event values into a list behavior *)
  let collect (Event es) =
    Behavior.of_fun (fun t ->
      List.filter_map (fun (te, v) ->
        if te <= t then Some v else None
      ) es)

  (** Tag events with the current value of a behavior *)
  let tag (Event es) b =
    Event (List.map (fun (t, _) -> (t, Behavior.sample b t)) es)

  (** Partition events by a predicate *)
  let partition pred (Event es) =
    let yes, no = List.partition (fun (_, v) -> pred v) es in
    (Event yes, Event no)

  (** Group consecutive events *)
  let group_by f (Event es) =
    match es with
    | [] -> []
    | (t, v) :: rest ->
      let key = f v in
      let _, groups, current_key, current =
        List.fold_left (fun (_, groups, ck, cur) (t, v) ->
          let k = f v in
          if k = ck then ((), groups, ck, (t, v) :: cur)
          else ((), (ck, Event (List.rev cur)) :: groups, k, [(t, v)])
        ) ((), [], key, [(t, v)]) rest
      in
      List.rev ((current_key, Event (List.rev current)) :: groups)

  (** Take first n events *)
  let take n (Event es) =
    let rec aux n acc = function
      | _ when n <= 0 -> List.rev acc
      | [] -> List.rev acc
      | x :: rest -> aux (n - 1) (x :: acc) rest
    in
    Event (aux n [] es)

  (** Drop first n events *)
  let drop n (Event es) =
    let rec aux n = function
      | l when n <= 0 -> l
      | [] -> []
      | _ :: rest -> aux (n - 1) rest
    in
    Event (aux n es)

  (** Number of occurrences *)
  let length (Event es) = List.length es
end

(* ──────────────────────────────────────── *)
(* Mutable Signals (push-based FRP)         *)
(* ──────────────────────────────────────── *)

module Signal = struct
  (** Create a new signal with an initial value *)
  let create initial = { value = initial; listeners = [] }

  (** Get the current value *)
  let get s = s.value

  (** Set a new value and notify listeners *)
  let set s v =
    s.value <- v;
    List.iter (fun f -> f v) s.listeners

  (** Update the value with a function *)
  let update s f =
    set s (f s.value)

  (** Subscribe to changes *)
  let subscribe s f =
    s.listeners <- f :: s.listeners

  (** Map a signal (creates a derived signal) *)
  let map f src =
    let dst = create (f src.value) in
    subscribe src (fun v -> set dst (f v));
    dst

  (** Combine two signals *)
  let map2 f s1 s2 =
    let dst = create (f s1.value s2.value) in
    subscribe s1 (fun _ -> set dst (f s1.value s2.value));
    subscribe s2 (fun _ -> set dst (f s1.value s2.value));
    dst

  (** Fold over signal changes *)
  let fold f init src =
    let dst = create init in
    subscribe src (fun v -> set dst (f dst.value v));
    dst

  (** Filter signal updates *)
  let filter pred src =
    let dst = create src.value in
    subscribe src (fun v -> if pred v then set dst v);
    dst

  (** Distinct: only propagate when value changes *)
  let distinct src =
    let dst = create src.value in
    subscribe src (fun v -> if v <> dst.value then set dst v);
    dst

  (** Sample: snapshot a signal when another signal changes *)
  let sample trigger src =
    let dst = create (trigger.value, src.value) in
    subscribe trigger (fun t -> set dst (t, src.value));
    dst

  (** Merge two signals (latest wins) *)
  let merge s1 s2 =
    let dst = create s1.value in
    subscribe s1 (fun v -> set dst v);
    subscribe s2 (fun v -> set dst v);
    dst

  (** Collect all values into a list signal *)
  let collect src =
    let dst = create [src.value] in
    subscribe src (fun v -> set dst (v :: dst.value));
    dst

  (** Count the number of updates *)
  let count src =
    let dst = create 0 in
    subscribe src (fun _ -> set dst (dst.value + 1));
    dst

  (** Buffer: accumulate values, flush when predicate is true *)
  let buffer flush_pred src =
    let buf = ref [] in
    let dst = create [] in
    subscribe src (fun v ->
      buf := v :: !buf;
      if flush_pred !buf then begin
        set dst (List.rev !buf);
        buf := []
      end);
    dst

  (** Debounce signal (tracks last value, simulated) *)
  let history n src =
    let dst = create [src.value] in
    subscribe src (fun v ->
      let h = v :: dst.value in
      let trimmed = if List.length h > n then
        List.filteri (fun i _ -> i < n) h
      else h in
      set dst trimmed);
    dst
end

(* ──────────────────────────────────────── *)
(* Reactive Cells (spreadsheet-style)       *)
(* ──────────────────────────────────────── *)

module Cell = struct
  (** Create a reactive cell *)
  let create v = { cell_value = v; cell_deps = []; cell_dirty = false }

  (** Get cell value *)
  let get c = c.cell_value

  (** Set cell value and trigger dependents *)
  let set c v =
    c.cell_value <- v;
    List.iter (fun f -> f ()) c.cell_deps

  (** Create a computed cell from one source *)
  let computed f src =
    let c = create (f (get src)) in
    src.cell_deps <- (fun () -> set c (f (get src))) :: src.cell_deps;
    c

  (** Create a computed cell from two sources *)
  let computed2 f src1 src2 =
    let c = create (f (get src1) (get src2)) in
    let update () = set c (f (get src1) (get src2)) in
    src1.cell_deps <- update :: src1.cell_deps;
    src2.cell_deps <- update :: src2.cell_deps;
    c

  (** Create a computed cell from a list of sources *)
  let computed_list f sources =
    let c = create (f (List.map get sources)) in
    let update () = set c (f (List.map get sources)) in
    List.iter (fun src ->
      src.cell_deps <- update :: src.cell_deps
    ) sources;
    c
end

(* ──────────────────────────────────────── *)
(* Reactive Stream (push-based event pipe)  *)
(* ──────────────────────────────────────── *)

module Stream = struct
  type 'a t = {
    mutable subs: ('a -> unit) list;
  }

  let create () = { subs = [] }

  let subscribe s f =
    s.subs <- f :: s.subs

  let emit s v =
    List.iter (fun f -> f v) s.subs

  let map f src =
    let dst = create () in
    subscribe src (fun v -> emit dst (f v));
    dst

  let filter pred src =
    let dst = create () in
    subscribe src (fun v -> if pred v then emit dst v);
    dst

  let merge s1 s2 =
    let dst = create () in
    subscribe s1 (fun v -> emit dst v);
    subscribe s2 (fun v -> emit dst v);
    dst

  let scan init f src =
    let acc = ref init in
    let dst = create () in
    subscribe src (fun v ->
      acc := f !acc v;
      emit dst !acc);
    dst

  let buffer n src =
    let buf = ref [] in
    let dst = create () in
    subscribe src (fun v ->
      buf := v :: !buf;
      if List.length !buf >= n then begin
        emit dst (List.rev !buf);
        buf := []
      end);
    dst

  let take n src =
    let count = ref 0 in
    let dst = create () in
    subscribe src (fun v ->
      if !count < n then begin
        incr count;
        emit dst v
      end);
    dst

  let drop n src =
    let count = ref 0 in
    let dst = create () in
    subscribe src (fun v ->
      if !count >= n then emit dst v
      else incr count);
    dst

  let distinct src =
    let prev = ref None in
    let dst = create () in
    subscribe src (fun v ->
      match !prev with
      | Some p when p = v -> ()
      | _ -> prev := Some v; emit dst v);
    dst

  let flat_map f src =
    let dst = create () in
    subscribe src (fun v ->
      let inner = f v in
      subscribe inner (fun iv -> emit dst iv));
    dst

  let zip s1 s2 =
    let q1 = Queue.create () in
    let q2 = Queue.create () in
    let dst = create () in
    subscribe s1 (fun v ->
      if Queue.is_empty q2 then Queue.add v q1
      else emit dst (v, Queue.pop q2));
    subscribe s2 (fun v ->
      if Queue.is_empty q1 then Queue.add v q2
      else emit dst (Queue.pop q1, v));
    dst

  let to_list src =
    let items = ref [] in
    subscribe src (fun v -> items := v :: !items);
    fun () -> List.rev !items
end

(* ──────────────────────────────────────── *)
(* Reactive State Machine                   *)
(* ──────────────────────────────────────── *)

module StateMachine = struct
  type ('s, 'e) t = {
    mutable state: 's;
    transition: 's -> 'e -> 's;
    mutable on_transition: ('s -> 'e -> 's -> unit) list;
    mutable history: ('s * 'e * 's) list;
  }

  let create ~initial ~transition =
    { state = initial; transition; on_transition = []; history = [] }

  let current sm = sm.state

  let send sm event =
    let old = sm.state in
    let next = sm.transition old event in
    sm.state <- next;
    sm.history <- (old, event, next) :: sm.history;
    List.iter (fun f -> f old event next) sm.on_transition;
    next

  let on_transition sm f =
    sm.on_transition <- f :: sm.on_transition

  let history sm = List.rev sm.history

  let reset sm s =
    sm.state <- s;
    sm.history <- []

  let send_many sm events =
    List.map (send sm) events
end

(* ──────────────────────────────────────── *)
(* Animation Primitives                     *)
(* ──────────────────────────────────────── *)

module Animation = struct
  (** Ease in (quadratic) *)
  let ease_in = Behavior.of_fun (fun t ->
    let t = Float.max 0.0 (Float.min 1.0 t) in
    t *. t)

  (** Ease out (quadratic) *)
  let ease_out = Behavior.of_fun (fun t ->
    let t = Float.max 0.0 (Float.min 1.0 t) in
    t *. (2.0 -. t))

  (** Ease in-out (cubic) *)
  let ease_in_out = Behavior.of_fun (fun t ->
    let t = Float.max 0.0 (Float.min 1.0 t) in
    if t < 0.5 then 4.0 *. t *. t *. t
    else 1.0 -. ((-2.0 *. t +. 2.0) ** 3.0) /. 2.0)

  (** Bounce ease out *)
  let bounce = Behavior.of_fun (fun t ->
    let t = Float.max 0.0 (Float.min 1.0 t) in
    if t < 1.0 /. 2.75 then
      7.5625 *. t *. t
    else if t < 2.0 /. 2.75 then
      let t = t -. 1.5 /. 2.75 in
      7.5625 *. t *. t +. 0.75
    else if t < 2.5 /. 2.75 then
      let t = t -. 2.25 /. 2.75 in
      7.5625 *. t *. t +. 0.9375
    else
      let t = t -. 2.625 /. 2.75 in
      7.5625 *. t *. t +. 0.984375)

  (** Spring oscillation *)
  let spring ?(damping=0.3) ?(frequency=3.0) () =
    Behavior.of_fun (fun t ->
      let t = Float.max 0.0 t in
      1.0 -. exp (-. damping *. t) *.
        cos (frequency *. 2.0 *. Float.pi *. t))

  (** Sine wave oscillation *)
  let oscillate ?(amplitude=1.0) ?(frequency=1.0) ?(phase=0.0) () =
    Behavior.of_fun (fun t ->
      amplitude *. sin (2.0 *. Float.pi *. frequency *. t +. phase))

  (** Keyframe animation: interpolate between (time, value) pairs *)
  let keyframes points =
    let sorted = List.sort (fun (t1, _) (t2, _) -> compare t1 t2) points in
    Behavior.of_fun (fun t ->
      match sorted with
      | [] -> 0.0
      | [(_, v)] -> v
      | _ ->
        let rec find = function
          | [] -> 0.0
          | [(_, v)] -> v
          | (t1, v1) :: ((t2, v2) :: _ as rest) ->
            if t <= t1 then v1
            else if t <= t2 then
              let frac = (t -. t1) /. (t2 -. t1) in
              v1 +. frac *. (v2 -. v1)
            else find rest
        in
        find sorted)

  (** Sequence animations one after another *)
  let sequence anims =
    let total = float_of_int (List.length anims) in
    Behavior.of_fun (fun t ->
      let t = Float.max 0.0 (Float.min (total -. 0.0001) t) in
      let idx = int_of_float t in
      let local_t = t -. float_of_int idx in
      let b = List.nth anims idx in
      Behavior.sample b local_t)
end

(* ──────────────────────────────────────── *)
(* Tests                                    *)
(* ──────────────────────────────────────── *)

let tests_passed = ref 0
let tests_failed = ref 0

let assert_equal ~msg expected actual =
  if expected = actual then
    incr tests_passed
  else begin
    incr tests_failed;
    Printf.printf "FAIL: %s\n  expected: %s\n  actual:   %s\n"
      msg (string_of_int expected) (string_of_int actual)
  end

let assert_float ~msg ?(eps=0.01) expected actual =
  if Float.abs (expected -. actual) < eps then
    incr tests_passed
  else begin
    incr tests_failed;
    Printf.printf "FAIL: %s\n  expected: %f\n  actual:   %f\n"
      msg expected actual
  end

let assert_true ~msg b =
  if b then incr tests_passed
  else begin
    incr tests_failed;
    Printf.printf "FAIL: %s\n" msg
  end

let () =
  Printf.printf "=== Functional Reactive Programming Tests ===\n\n";

  (* --- Behavior tests --- *)
  Printf.printf "-- Behavior --\n";

  let b = Behavior.constant 42.0 in
  assert_float ~msg:"constant behavior" 42.0 (Behavior.sample b 0.0);
  assert_float ~msg:"constant at any time" 42.0 (Behavior.sample b 100.0);

  let b = Behavior.time in
  assert_float ~msg:"time at 0" 0.0 (Behavior.sample b 0.0);
  assert_float ~msg:"time at 5" 5.0 (Behavior.sample b 5.0);

  let b = Behavior.map (fun x -> x *. 2.0) Behavior.time in
  assert_float ~msg:"map time * 2" 10.0 (Behavior.sample b 5.0);

  let b = Behavior.map2 ( +. ) (Behavior.constant 3.0) Behavior.time in
  assert_float ~msg:"map2 const + time" 8.0 (Behavior.sample b 5.0);

  let b = Behavior.map3 (fun a b c -> a +. b +. c)
    (Behavior.constant 1.0) (Behavior.constant 2.0) Behavior.time in
  assert_float ~msg:"map3" 13.0 (Behavior.sample b 10.0);

  let b = Behavior.bind Behavior.time (fun t ->
    if t < 5.0 then Behavior.constant 0.0
    else Behavior.constant 1.0) in
  assert_float ~msg:"bind before threshold" 0.0 (Behavior.sample b 3.0);
  assert_float ~msg:"bind after threshold" 1.0 (Behavior.sample b 7.0);

  let b = Behavior.delay 2.0 Behavior.time in
  assert_float ~msg:"delay time" 3.0 (Behavior.sample b 5.0);

  let samples = Behavior.sample_at 1.0 3.0 Behavior.time in
  assert_equal ~msg:"sample_at count" 4 (List.length samples);
  assert_float ~msg:"sample_at t=2" 2.0 (snd (List.nth samples 2));

  let b = Behavior.clamp 0.0 10.0 (Behavior.of_fun (fun t -> t *. 5.0)) in
  assert_float ~msg:"clamp low" 0.0 (Behavior.sample b 0.0);
  assert_float ~msg:"clamp mid" 5.0 (Behavior.sample b 1.0);
  assert_float ~msg:"clamp high" 10.0 (Behavior.sample b 3.0);

  let b = Behavior.switch
    (Behavior.of_fun (fun t -> t < 5.0))
    (Behavior.constant 1.0) (Behavior.constant 2.0) in
  assert_float ~msg:"switch true" 1.0 (Behavior.sample b 3.0);
  assert_float ~msg:"switch false" 2.0 (Behavior.sample b 7.0);

  let b = Behavior.until 5.0 (Behavior.constant 1.0) (Behavior.constant 2.0) in
  assert_float ~msg:"until before" 1.0 (Behavior.sample b 3.0);
  assert_float ~msg:"until after" 2.0 (Behavior.sample b 7.0);

  let b = Behavior.lerp 0.0 10.0 0.0 100.0 in
  assert_float ~msg:"lerp at 0" 0.0 (Behavior.sample b 0.0);
  assert_float ~msg:"lerp at 5" 50.0 (Behavior.sample b 5.0);
  assert_float ~msg:"lerp at 10" 100.0 (Behavior.sample b 10.0);
  assert_float ~msg:"lerp before" 0.0 (Behavior.sample b (-1.0));
  assert_float ~msg:"lerp after" 100.0 (Behavior.sample b 15.0);

  let sine = Behavior.of_fun (fun t -> sin t) in
  let integral_b = Behavior.integral ~dt:0.001 sine in
  (* integral of sin from 0 to pi ≈ 2.0 *)
  assert_float ~msg:"integral of sin" ~eps:0.05 2.0
    (Behavior.sample integral_b Float.pi);

  let linear = Behavior.of_fun (fun t -> t) in
  let deriv = Behavior.derivative ~dt:0.0001 linear in
  assert_float ~msg:"derivative of t" ~eps:0.01 1.0 (Behavior.sample deriv 5.0);

  (* --- Event tests --- *)
  Printf.printf "-- Events --\n";

  let e = EventOps.of_list [(1.0, "a"); (3.0, "b"); (2.0, "c")] in
  let occ = EventOps.occurrences e in
  assert_equal ~msg:"sorted events" 3 (List.length occ);
  assert_true ~msg:"events sorted by time" (fst (List.nth occ 0) <= fst (List.nth occ 1));

  let e = EventOps.map String.length (EventOps.of_list [(1.0, "hi"); (2.0, "hello")]) in
  assert_equal ~msg:"event map" 2 (snd (List.hd (EventOps.occurrences e)));

  let e = EventOps.filter (fun x -> x > 2)
    (EventOps.of_list [(1.0, 1); (2.0, 3); (3.0, 5)]) in
  assert_equal ~msg:"event filter" 2 (EventOps.length e);

  let e1 = EventOps.of_list [(1.0, "a"); (3.0, "c")] in
  let e2 = EventOps.of_list [(2.0, "b"); (4.0, "d")] in
  let merged = EventOps.merge e1 e2 in
  assert_equal ~msg:"merge events" 4 (EventOps.length merged);

  let e = EventOps.of_list [(1.0, 1); (2.0, 2); (3.0, 3)] in
  let sum_b = EventOps.scan 0 ( + ) e in
  assert_equal ~msg:"scan at t=0" 0 (Behavior.sample sum_b 0.0);
  assert_equal ~msg:"scan at t=2.5" 3 (Behavior.sample sum_b 2.5);
  assert_equal ~msg:"scan at t=3" 6 (Behavior.sample sum_b 3.0);

  let e = EventOps.of_list [(1.0, "a"); (2.0, "b"); (3.0, "c")] in
  let cnt = EventOps.count e in
  assert_equal ~msg:"count at t=0" 0 (Behavior.sample cnt 0.0);
  assert_equal ~msg:"count at t=2.5" 2 (Behavior.sample cnt 2.5);

  let e = EventOps.of_list [(1.0, "x"); (3.0, "y")] in
  let held = EventOps.hold "default" e in
  assert_true ~msg:"hold before" ("default" = Behavior.sample held 0.0);
  assert_true ~msg:"hold after first" ("x" = Behavior.sample held 2.0);
  assert_true ~msg:"hold after second" ("y" = Behavior.sample held 5.0);

  let e = EventOps.delay 1.0 (EventOps.of_list [(1.0, "a"); (2.0, "b")]) in
  let occ = EventOps.occurrences e in
  assert_float ~msg:"delay events" 2.0 (fst (List.hd occ));

  let e = EventOps.window 2.0 4.0
    (EventOps.of_list [(1.0, "a"); (2.0, "b"); (3.0, "c"); (5.0, "d")]) in
  assert_equal ~msg:"window events" 2 (EventOps.length e);

  let e = EventOps.throttle 2.0
    (EventOps.of_list [(1.0, "a"); (1.5, "b"); (3.5, "c"); (4.0, "d")]) in
  assert_equal ~msg:"throttle" 2 (EventOps.length e);

  let e = EventOps.debounce 1.0
    (EventOps.of_list [(1.0, "a"); (1.5, "b"); (3.0, "c")]) in
  assert_equal ~msg:"debounce" 2 (EventOps.length e);

  let e = EventOps.take 2 (EventOps.of_list [(1.0, 1); (2.0, 2); (3.0, 3)]) in
  assert_equal ~msg:"take 2" 2 (EventOps.length e);

  let e = EventOps.drop 1 (EventOps.of_list [(1.0, 1); (2.0, 2); (3.0, 3)]) in
  assert_equal ~msg:"drop 1" 2 (EventOps.length e);

  let yes, no = EventOps.partition (fun x -> x > 2)
    (EventOps.of_list [(1.0, 1); (2.0, 3); (3.0, 5)]) in
  assert_equal ~msg:"partition yes" 2 (EventOps.length yes);
  assert_equal ~msg:"partition no" 1 (EventOps.length no);

  let e = EventOps.once 1.0 "x" in
  assert_equal ~msg:"once" 1 (EventOps.length e);

  let e = EventOps.never in
  assert_equal ~msg:"never" 0 (EventOps.length (e : string event));

  let groups = EventOps.group_by (fun x -> x mod 2)
    (EventOps.of_list [(1.0, 1); (2.0, 3); (3.0, 2); (4.0, 4)]) in
  assert_equal ~msg:"group_by" 2 (List.length groups);

  let tag_e = EventOps.tag
    (EventOps.of_list [(1.0, ()); (5.0, ())])
    (Behavior.of_fun (fun t -> t *. 10.0)) in
  let occ = EventOps.occurrences tag_e in
  assert_float ~msg:"tag at t=1" 10.0 (snd (List.hd occ));
  assert_float ~msg:"tag at t=5" 50.0 (snd (List.nth occ 1));

  let collected = EventOps.collect (EventOps.of_list [(1.0, "a"); (2.0, "b")]) in
  let vals = Behavior.sample collected 1.5 in
  assert_equal ~msg:"collect count" 1 (List.length vals);

  let fm = EventOps.filter_map
    (fun x -> if x > 2 then Some (x * 10) else None)
    (EventOps.of_list [(1.0, 1); (2.0, 3); (3.0, 5)]) in
  assert_equal ~msg:"filter_map" 2 (EventOps.length fm);

  (* --- Signal tests --- *)
  Printf.printf "-- Signals --\n";

  let s = Signal.create 0 in
  assert_equal ~msg:"signal initial" 0 (Signal.get s);
  Signal.set s 5;
  assert_equal ~msg:"signal set" 5 (Signal.get s);

  Signal.update s (fun x -> x + 1);
  assert_equal ~msg:"signal update" 6 (Signal.get s);

  let s = Signal.create 1 in
  let doubled = Signal.map (fun x -> x * 2) s in
  assert_equal ~msg:"signal map initial" 2 (Signal.get doubled);
  Signal.set s 5;
  assert_equal ~msg:"signal map propagates" 10 (Signal.get doubled);

  let a = Signal.create 1 in
  let b = Signal.create 2 in
  let sum = Signal.map2 ( + ) a b in
  assert_equal ~msg:"signal map2" 3 (Signal.get sum);
  Signal.set a 10;
  assert_equal ~msg:"signal map2 update" 12 (Signal.get sum);

  let s = Signal.create 0 in
  let acc = Signal.fold ( + ) 0 s in
  Signal.set s 1; Signal.set s 2; Signal.set s 3;
  assert_equal ~msg:"signal fold" 6 (Signal.get acc);

  let s = Signal.create 0 in
  let pos = Signal.filter (fun x -> x > 0) s in
  Signal.set s (-1);
  assert_equal ~msg:"signal filter skip" 0 (Signal.get pos);
  Signal.set s 5;
  assert_equal ~msg:"signal filter pass" 5 (Signal.get pos);

  let s = Signal.create 1 in
  let d = Signal.distinct s in
  let count = ref 0 in
  Signal.subscribe d (fun _ -> incr count);
  Signal.set s 1; (* same, no propagation *)
  Signal.set s 2; (* different *)
  assert_equal ~msg:"distinct propagations" 1 !count;

  let s = Signal.create 0 in
  let c = Signal.count s in
  Signal.set s 1; Signal.set s 2; Signal.set s 3;
  assert_equal ~msg:"signal count" 3 (Signal.get c);

  let s = Signal.create 0 in
  let h = Signal.history 3 s in
  Signal.set s 1; Signal.set s 2; Signal.set s 3;
  assert_equal ~msg:"history length" 3 (List.length (Signal.get h));

  let trigger = Signal.create 0 in
  let value = Signal.create "a" in
  let sampled = Signal.sample trigger value in
  Signal.set value "b";
  Signal.set trigger 1;
  let (_, v) = Signal.get sampled in
  assert_true ~msg:"signal sample" (v = "b");

  let s1 = Signal.create 0 in
  let s2 = Signal.create 0 in
  let m = Signal.merge s1 s2 in
  Signal.set s1 1;
  assert_equal ~msg:"merge s1" 1 (Signal.get m);
  Signal.set s2 2;
  assert_equal ~msg:"merge s2" 2 (Signal.get m);

  let s = Signal.create 0 in
  let collected = Signal.collect s in
  Signal.set s 1; Signal.set s 2;
  assert_equal ~msg:"signal collect" 3 (List.length (Signal.get collected));

  let s = Signal.create 0 in
  let buf = Signal.buffer (fun l -> List.length l >= 3) s in
  Signal.set s 1; Signal.set s 2;
  assert_equal ~msg:"buffer not flushed" 0 (List.length (Signal.get buf));
  Signal.set s 3;
  assert_equal ~msg:"buffer flushed" 3 (List.length (Signal.get buf));

  (* --- Cell tests --- *)
  Printf.printf "-- Cells --\n";

  let c = Cell.create 5 in
  assert_equal ~msg:"cell get" 5 (Cell.get c);
  Cell.set c 10;
  assert_equal ~msg:"cell set" 10 (Cell.get c);

  let src = Cell.create 3 in
  let doubled = Cell.computed (fun x -> x * 2) src in
  assert_equal ~msg:"cell computed" 6 (Cell.get doubled);
  Cell.set src 5;
  assert_equal ~msg:"cell computed propagate" 10 (Cell.get doubled);

  let a = Cell.create 1 in
  let b = Cell.create 2 in
  let sum = Cell.computed2 ( + ) a b in
  assert_equal ~msg:"cell computed2" 3 (Cell.get sum);
  Cell.set a 10;
  assert_equal ~msg:"cell computed2 update" 12 (Cell.get sum);

  let cells = [Cell.create 1; Cell.create 2; Cell.create 3] in
  let total = Cell.computed_list (List.fold_left ( + ) 0) cells in
  assert_equal ~msg:"cell computed_list" 6 (Cell.get total);
  Cell.set (List.hd cells) 10;
  assert_equal ~msg:"cell computed_list update" 15 (Cell.get total);

  (* chain: a -> b -> c *)
  let a = Cell.create 1 in
  let b = Cell.computed (fun x -> x * 2) a in
  let c = Cell.computed (fun x -> x + 1) b in
  assert_equal ~msg:"cell chain" 3 (Cell.get c);
  Cell.set a 5;
  assert_equal ~msg:"cell chain propagate" 11 (Cell.get c);

  (* --- Stream tests --- *)
  Printf.printf "-- Streams --\n";

  let s = Stream.create () in
  let results = ref [] in
  Stream.subscribe s (fun v -> results := v :: !results);
  Stream.emit s 1; Stream.emit s 2; Stream.emit s 3;
  assert_equal ~msg:"stream emit count" 3 (List.length !results);

  let s = Stream.create () in
  let mapped = Stream.map (fun x -> x * 2) s in
  let r = ref 0 in
  Stream.subscribe mapped (fun v -> r := v);
  Stream.emit s 5;
  assert_equal ~msg:"stream map" 10 !r;

  let s = Stream.create () in
  let filtered = Stream.filter (fun x -> x > 2) s in
  let r = ref [] in
  Stream.subscribe filtered (fun v -> r := v :: !r);
  Stream.emit s 1; Stream.emit s 3; Stream.emit s 5;
  assert_equal ~msg:"stream filter" 2 (List.length !r);

  let s1 = Stream.create () in
  let s2 = Stream.create () in
  let merged = Stream.merge s1 s2 in
  let r = ref 0 in
  Stream.subscribe merged (fun v -> r := !r + v);
  Stream.emit s1 1; Stream.emit s2 2;
  assert_equal ~msg:"stream merge" 3 !r;

  let s = Stream.create () in
  let scanned = Stream.scan 0 ( + ) s in
  let r = ref 0 in
  Stream.subscribe scanned (fun v -> r := v);
  Stream.emit s 1; Stream.emit s 2; Stream.emit s 3;
  assert_equal ~msg:"stream scan" 6 !r;

  let s = Stream.create () in
  let buffered = Stream.buffer 3 s in
  let r = ref [] in
  Stream.subscribe buffered (fun v -> r := v);
  Stream.emit s 1; Stream.emit s 2;
  assert_equal ~msg:"stream buffer not ready" 0 (List.length !r);
  Stream.emit s 3;
  assert_equal ~msg:"stream buffer flushed" 3 (List.length !r);

  let s = Stream.create () in
  let taken = Stream.take 2 s in
  let r = ref 0 in
  Stream.subscribe taken (fun _ -> incr r);
  Stream.emit s 1; Stream.emit s 2; Stream.emit s 3;
  assert_equal ~msg:"stream take" 2 !r;

  let s = Stream.create () in
  let dropped = Stream.drop 2 s in
  let r = ref 0 in
  Stream.subscribe dropped (fun _ -> incr r);
  Stream.emit s 1; Stream.emit s 2; Stream.emit s 3; Stream.emit s 4;
  assert_equal ~msg:"stream drop" 2 !r;

  let s = Stream.create () in
  let dist = Stream.distinct s in
  let r = ref 0 in
  Stream.subscribe dist (fun _ -> incr r);
  Stream.emit s 1; Stream.emit s 1; Stream.emit s 2; Stream.emit s 2; Stream.emit s 3;
  assert_equal ~msg:"stream distinct" 3 !r;

  let s = Stream.create () in
  let to_list_fn = Stream.to_list s in
  Stream.emit s 1; Stream.emit s 2; Stream.emit s 3;
  assert_equal ~msg:"stream to_list" 3 (List.length (to_list_fn ()));

  let s1 = Stream.create () in
  let s2 = Stream.create () in
  let zipped = Stream.zip s1 s2 in
  let r = ref [] in
  Stream.subscribe zipped (fun p -> r := p :: !r);
  Stream.emit s1 1; Stream.emit s2 10; Stream.emit s1 2; Stream.emit s2 20;
  assert_equal ~msg:"stream zip" 2 (List.length !r);

  let s = Stream.create () in
  let fm = Stream.flat_map (fun v ->
    let inner = Stream.create () in
    Stream.emit inner (v * 10);
    inner
  ) s in
  let r = ref 0 in
  Stream.subscribe fm (fun v -> r := v);
  Stream.emit s 5;
  assert_equal ~msg:"stream flat_map" 50 !r;

  (* --- StateMachine tests --- *)
  Printf.printf "-- StateMachine --\n";

  let sm = StateMachine.create ~initial:"idle"
    ~transition:(fun state event ->
      match state, event with
      | "idle", "start" -> "running"
      | "running", "stop" -> "idle"
      | "running", "pause" -> "paused"
      | "paused", "resume" -> "running"
      | s, _ -> s) in
  assert_true ~msg:"sm initial" ("idle" = StateMachine.current sm);
  ignore (StateMachine.send sm "start");
  assert_true ~msg:"sm transition" ("running" = StateMachine.current sm);
  ignore (StateMachine.send sm "pause");
  assert_true ~msg:"sm pause" ("paused" = StateMachine.current sm);
  ignore (StateMachine.send sm "resume");
  assert_true ~msg:"sm resume" ("running" = StateMachine.current sm);
  ignore (StateMachine.send sm "stop");
  assert_true ~msg:"sm stop" ("idle" = StateMachine.current sm);
  assert_equal ~msg:"sm history" 4 (List.length (StateMachine.history sm));

  let sm = StateMachine.create ~initial:0
    ~transition:(fun s e -> s + e) in
  let results = StateMachine.send_many sm [1; 2; 3; 4] in
  assert_equal ~msg:"sm send_many" 10 (StateMachine.current sm);
  assert_equal ~msg:"sm send_many results" 4 (List.length results);

  let listener_called = ref false in
  let sm = StateMachine.create ~initial:"off"
    ~transition:(fun _ _ -> "on") in
  StateMachine.on_transition sm (fun _ _ _ -> listener_called := true);
  ignore (StateMachine.send sm "flip");
  assert_true ~msg:"sm on_transition" !listener_called;

  StateMachine.reset sm "off";
  assert_true ~msg:"sm reset" ("off" = StateMachine.current sm);
  assert_equal ~msg:"sm reset history" 0 (List.length (StateMachine.history sm));

  (* --- Animation tests --- *)
  Printf.printf "-- Animation --\n";

  assert_float ~msg:"ease_in 0" 0.0 (Behavior.sample Animation.ease_in 0.0);
  assert_float ~msg:"ease_in 1" 1.0 (Behavior.sample Animation.ease_in 1.0);
  assert_float ~msg:"ease_in 0.5" 0.25 (Behavior.sample Animation.ease_in 0.5);

  assert_float ~msg:"ease_out 0" 0.0 (Behavior.sample Animation.ease_out 0.0);
  assert_float ~msg:"ease_out 1" 1.0 (Behavior.sample Animation.ease_out 1.0);

  assert_float ~msg:"ease_in_out 0" 0.0 (Behavior.sample Animation.ease_in_out 0.0);
  assert_float ~msg:"ease_in_out 1" 1.0 (Behavior.sample Animation.ease_in_out 1.0);

  assert_float ~msg:"bounce 0" 0.0 (Behavior.sample Animation.bounce 0.0);
  assert_float ~msg:"bounce 1" 1.0 (Behavior.sample Animation.bounce 1.0);

  let spring_b = Animation.spring () in
  assert_float ~msg:"spring 0" 0.0 (Behavior.sample spring_b 0.0);

  let osc = Animation.oscillate ~amplitude:2.0 ~frequency:1.0 () in
  assert_float ~msg:"oscillate 0" 0.0 (Behavior.sample osc 0.0);

  let kf = Animation.keyframes [(0.0, 0.0); (1.0, 10.0); (2.0, 5.0)] in
  assert_float ~msg:"keyframe 0" 0.0 (Behavior.sample kf 0.0);
  assert_float ~msg:"keyframe 0.5" 5.0 (Behavior.sample kf 0.5);
  assert_float ~msg:"keyframe 1" 10.0 (Behavior.sample kf 1.0);
  assert_float ~msg:"keyframe 1.5" 7.5 (Behavior.sample kf 1.5);
  assert_float ~msg:"keyframe 2" 5.0 (Behavior.sample kf 2.0);

  let seq = Animation.sequence [Animation.ease_in; Animation.ease_out] in
  assert_float ~msg:"sequence t=0" 0.0 (Behavior.sample seq 0.0);
  assert_float ~msg:"sequence t=1" 0.0 (Behavior.sample seq 1.0);

  Printf.printf "\n=== Results: %d passed, %d failed ===\n"
    !tests_passed !tests_failed;
  if !tests_failed > 0 then exit 1
