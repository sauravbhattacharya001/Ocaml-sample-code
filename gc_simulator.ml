(* gc_simulator.ml — Garbage Collector Simulator
 *
 * Educational implementation of four classic GC algorithms on a simulated heap:
 *   1. Mark-and-Sweep
 *   2. Copying (Cheney's semi-space)
 *   3. Reference Counting (with cycle detection via trial deletion)
 *   4. Generational (two-generation: nursery + old)
 *
 * Each algorithm operates on a virtual heap of fixed-size cells.
 * Objects can reference other objects, forming arbitrary graphs.
 *
 * Usage:
 *   let heap = Heap.create 1024 in
 *   let root_set = RootSet.create () in
 *   let a = Heap.alloc heap 4 in
 *   let b = Heap.alloc heap 2 in
 *   Heap.set_ref heap a 0 b;
 *   RootSet.add root_set a;
 *   let stats = MarkSweep.collect heap root_set in
 *   (* b is reachable from a which is a root, so both survive *)
 *)

(* ── Cell representation ──────────────────────────────────────────── *)

type cell = {
  mutable marked : bool;
  mutable forwarded : int;      (* -1 = not forwarded *)
  mutable ref_count : int;
  mutable size : int;           (* number of reference slots *)
  mutable refs : int array;     (* indices into heap; -1 = null *)
  mutable alive : bool;
  mutable generation : int;     (* 0 = nursery, 1 = old *)
}

let null_ref = -1

let make_cell size = {
  marked = false;
  forwarded = -1;
  ref_count = 0;
  size;
  refs = Array.make size null_ref;
  alive = true;
  generation = 0;
}

(* ── GC statistics ────────────────────────────────────────────────── *)

type gc_stats = {
  collected : int;
  survived : int;
  heap_size : int;
  live_before : int;
  live_after : int;
  cycles_detected : int;   (* for ref counting *)
  promoted : int;           (* for generational *)
}

let empty_stats heap_size = {
  collected = 0; survived = 0; heap_size;
  live_before = 0; live_after = 0;
  cycles_detected = 0; promoted = 0;
}

(* ── Heap ─────────────────────────────────────────────────────────── *)

module Heap = struct
  type t = {
    mutable cells : cell array;
    capacity : int;
    mutable next_free : int;
    mutable gc_count : int;
    mutable total_allocated : int;
    mutable total_collected : int;
  }

  let create cap = {
    cells = Array.init cap (fun _ -> make_cell 0);
    capacity = cap;
    next_free = 0;
    gc_count = 0;
    total_allocated = 0;
    total_collected = 0;
  }

  let is_valid t idx = idx >= 0 && idx < t.capacity

  let get t idx =
    if not (is_valid t idx) then failwith "Heap.get: index out of bounds";
    t.cells.(idx)

  let alloc t size =
    (* find next free slot *)
    let start = t.next_free in
    let rec find i =
      if i >= t.capacity then begin
        (* wrap around *)
        let rec find2 j =
          if j >= start then failwith "Heap.alloc: out of memory"
          else if not t.cells.(j).alive then j
          else find2 (j + 1)
        in
        find2 0
      end
      else if not t.cells.(i).alive then i
      else find (i + 1)
    in
    let idx = find start in
    let c = make_cell size in
    t.cells.(idx) <- c;
    t.next_free <- (idx + 1) mod t.capacity;
    t.total_allocated <- t.total_allocated + 1;
    idx

  let free t idx =
    if is_valid t idx && t.cells.(idx).alive then begin
      t.cells.(idx).alive <- false;
      t.total_collected <- t.total_collected + 1
    end

  let set_ref t src slot dst =
    if not (is_valid t src) then failwith "Heap.set_ref: invalid src";
    let c = t.cells.(src) in
    if slot < 0 || slot >= c.size then failwith "Heap.set_ref: slot out of bounds";
    c.refs.(slot) <- dst

  let get_ref t src slot =
    if not (is_valid t src) then failwith "Heap.get_ref: invalid src";
    let c = t.cells.(src) in
    if slot < 0 || slot >= c.size then failwith "Heap.get_ref: slot out of bounds";
    c.refs.(slot)

  let live_count t =
    Array.fold_left (fun acc c -> if c.alive then acc + 1 else acc) 0 t.cells

  let dead_count t =
    let used = Array.fold_left
      (fun acc c -> if c.alive || c.size > 0 then acc + 1 else acc) 0 t.cells
    in
    used - live_count t

  let reset_marks t =
    Array.iter (fun c -> c.marked <- false) t.cells

  let summary t =
    Printf.sprintf "Heap: cap=%d live=%d alloc_total=%d collected_total=%d gc_runs=%d"
      t.capacity (live_count t) t.total_allocated t.total_collected t.gc_count
end

(* ── Root Set ─────────────────────────────────────────────────────── *)

module RootSet = struct
  type t = {
    mutable roots : int list;
  }

  let create () = { roots = [] }

  let add t idx =
    if not (List.mem idx t.roots) then
      t.roots <- idx :: t.roots

  let remove t idx =
    t.roots <- List.filter (fun i -> i <> idx) t.roots

  let mem t idx = List.mem idx t.roots

  let to_list t = t.roots

  let clear t = t.roots <- []

  let size t = List.length t.roots
end

(* ── 1. Mark-and-Sweep ────────────────────────────────────────────── *)

module MarkSweep = struct
  (** Mark phase: DFS from roots, setting marked=true on reachable cells *)
  let mark heap roots =
    let rec dfs idx =
      if Heap.is_valid heap idx then begin
        let c = heap.Heap.cells.(idx) in
        if c.alive && not c.marked then begin
          c.marked <- true;
          Array.iter (fun r ->
            if r <> null_ref then dfs r
          ) c.refs
        end
      end
    in
    List.iter dfs (RootSet.to_list roots)

  (** Sweep phase: free all unmarked live cells *)
  let sweep heap =
    let collected = ref 0 in
    Array.iteri (fun i c ->
      if c.alive then begin
        if not c.marked then begin
          Heap.free heap i;
          incr collected
        end else
          c.marked <- false  (* reset for next GC cycle *)
      end
    ) heap.Heap.cells;
    !collected

  let collect heap roots =
    let live_before = Heap.live_count heap in
    Heap.reset_marks heap;
    mark heap roots;
    let collected = sweep heap in
    heap.Heap.gc_count <- heap.Heap.gc_count + 1;
    let live_after = Heap.live_count heap in
    { (empty_stats heap.Heap.capacity) with
      collected; survived = live_after;
      live_before; live_after }
end

(* ── 2. Copying GC (Cheney's semi-space) ──────────────────────────── *)

module CopyingGC = struct
  type semi_space = {
    mutable from_space : cell array;
    mutable to_space : cell array;
    mutable from_start : int;
    mutable to_start : int;
    space_size : int;
    mutable next_free : int;
    mutable gc_count : int;
    mutable total_allocated : int;
    mutable total_collected : int;
  }

  let create cap =
    let half = cap / 2 in
    {
      from_space = Array.init half (fun _ -> make_cell 0);
      to_space = Array.init half (fun _ -> make_cell 0);
      from_start = 0;
      to_start = half;
      space_size = half;
      next_free = 0;
      gc_count = 0;
      total_allocated = 0;
      total_collected = 0;
    }

  let alloc t size =
    if t.next_free >= t.space_size then
      failwith "CopyingGC.alloc: out of memory (need to collect)";
    let idx = t.next_free in
    t.from_space.(idx) <- make_cell size;
    t.next_free <- idx + 1;
    t.total_allocated <- t.total_allocated + 1;
    idx

  let set_ref t src slot dst =
    if src < 0 || src >= t.space_size then failwith "CopyingGC.set_ref: invalid src";
    let c = t.from_space.(src) in
    if slot < 0 || slot >= c.size then failwith "CopyingGC.set_ref: slot out of bounds";
    c.refs.(slot) <- dst

  let get_ref t src slot =
    if src < 0 || src >= t.space_size then failwith "CopyingGC.get_ref: invalid src";
    let c = t.from_space.(src) in
    if slot < 0 || slot >= c.size then failwith "CopyingGC.get_ref: slot out of bounds";
    c.refs.(slot)

  let live_count t =
    let count = ref 0 in
    for i = 0 to t.next_free - 1 do
      if t.from_space.(i).alive then incr count
    done;
    !count

  (** Cheney's algorithm: BFS copy from from_space to to_space *)
  let collect t roots =
    let live_before = live_count t in
    (* Reset to_space *)
    let new_to = Array.init t.space_size (fun _ -> make_cell 0) in
    let free_ptr = ref 0 in
    let scan_ptr = ref 0 in

    (* Copy a single object, returning its new index *)
    let copy_obj idx =
      if idx = null_ref || idx < 0 || idx >= t.space_size then idx
      else
        let c = t.from_space.(idx) in
        if not c.alive then idx
        else if c.forwarded >= 0 then c.forwarded  (* already copied *)
        else begin
          let new_idx = !free_ptr in
          let new_cell = make_cell c.size in
          Array.blit c.refs 0 new_cell.refs 0 c.size;
          new_to.(new_idx) <- new_cell;
          c.forwarded <- new_idx;
          incr free_ptr;
          new_idx
        end
    in

    (* Copy roots *)
    let new_roots = List.map (fun r ->
      let nr = copy_obj r in
      nr
    ) (RootSet.to_list roots) in

    (* Scan copied objects (BFS) *)
    while !scan_ptr < !free_ptr do
      let c = new_to.(!scan_ptr) in
      for s = 0 to c.size - 1 do
        c.refs.(s) <- copy_obj c.refs.(s)
      done;
      incr scan_ptr
    done;

    (* Update root set *)
    RootSet.clear roots;
    List.iter (fun r -> if r >= 0 then RootSet.add roots r) new_roots;

    (* Swap spaces *)
    let collected = live_before - !free_ptr in
    t.total_collected <- t.total_collected + (max 0 collected);
    t.from_space <- new_to;
    t.to_space <- Array.init t.space_size (fun _ -> make_cell 0);
    let old_start = t.from_start in
    t.from_start <- t.to_start;
    t.to_start <- old_start;
    t.next_free <- !free_ptr;
    t.gc_count <- t.gc_count + 1;

    (* Reset forwarding pointers in old from_space — not needed, it's discarded *)
    let live_after = !free_ptr in
    { (empty_stats (t.space_size * 2)) with
      collected = max 0 collected; survived = live_after;
      live_before; live_after }

  let summary t =
    Printf.sprintf "CopyingGC: space_size=%d live=%d next_free=%d alloc=%d collected=%d gc=%d"
      t.space_size (live_count t) t.next_free t.total_allocated t.total_collected t.gc_count
end

(* ── 3. Reference Counting ────────────────────────────────────────── *)

module RefCount = struct
  (** Increment ref count when creating a reference *)
  let inc_ref heap idx =
    if Heap.is_valid heap idx then begin
      let c = heap.Heap.cells.(idx) in
      if c.alive then
        c.ref_count <- c.ref_count + 1
    end

  (** Decrement ref count; recursively free if it reaches zero *)
  let rec dec_ref heap idx =
    if Heap.is_valid heap idx then begin
      let c = heap.Heap.cells.(idx) in
      if c.alive then begin
        c.ref_count <- c.ref_count - 1;
        if c.ref_count <= 0 then begin
          (* Recursively decrement children *)
          Array.iter (fun r ->
            if r <> null_ref then dec_ref heap r
          ) c.refs;
          Heap.free heap idx
        end
      end
    end

  (** Set a reference, updating ref counts *)
  let set_ref heap src slot dst =
    let old = Heap.get_ref heap src slot in
    if old <> null_ref then dec_ref heap old;
    Heap.set_ref heap src slot dst;
    if dst <> null_ref then inc_ref heap dst

  (** Detect cycles using trial deletion (simplified Lins' algorithm).
   *  Returns indices of cells involved in unreachable cycles. *)
  let detect_cycles heap =
    let n = heap.Heap.capacity in
    (* Save original ref counts *)
    let saved = Array.init n (fun i -> heap.Heap.cells.(i).ref_count) in
    (* Trial decrement: for each live cell, decrement its children's counts *)
    for i = 0 to n - 1 do
      let c = heap.Heap.cells.(i) in
      if c.alive then
        Array.iter (fun r ->
          if r <> null_ref && Heap.is_valid heap r then begin
            let child = heap.Heap.cells.(r) in
            if child.alive then
              child.ref_count <- child.ref_count - 1
          end
        ) c.refs
    done;
    (* Cells with ref_count = 0 after trial deletion are only kept alive
       by internal references — they form cycles if not reachable from
       cells that still have external refs *)
    let in_cycle = Array.make n false in
    let visited = Array.make n false in
    (* Mark reachable from cells that still have positive ref count *)
    let rec mark_reachable idx =
      if Heap.is_valid heap idx && not visited.(idx) then begin
        visited.(idx) <- true;
        let c = heap.Heap.cells.(idx) in
        if c.alive then
          Array.iter (fun r ->
            if r <> null_ref then mark_reachable r
          ) c.refs
      end
    in
    for i = 0 to n - 1 do
      let c = heap.Heap.cells.(i) in
      if c.alive && c.ref_count > 0 then
        mark_reachable i
    done;
    (* Anything live but not visited is in an unreachable cycle *)
    let cycle_count = ref 0 in
    for i = 0 to n - 1 do
      let c = heap.Heap.cells.(i) in
      if c.alive && not visited.(i) then begin
        in_cycle.(i) <- true;
        incr cycle_count
      end
    done;
    (* Restore original ref counts *)
    for i = 0 to n - 1 do
      heap.Heap.cells.(i).ref_count <- saved.(i)
    done;
    (in_cycle, !cycle_count)

  (** Collect cycles: detect and free cyclic garbage *)
  let collect_cycles heap =
    let live_before = Heap.live_count heap in
    let (in_cycle, cycle_count) = detect_cycles heap in
    let collected = ref 0 in
    Array.iteri (fun i is_cyclic ->
      if is_cyclic then begin
        Heap.free heap i;
        incr collected
      end
    ) in_cycle;
    heap.Heap.gc_count <- heap.Heap.gc_count + 1;
    let live_after = Heap.live_count heap in
    { (empty_stats heap.Heap.capacity) with
      collected = !collected; survived = live_after;
      live_before; live_after;
      cycles_detected = cycle_count }
end

(* ── 4. Generational GC ──────────────────────────────────────────── *)

module GenerationalGC = struct
  type t = {
    heap : Heap.t;
    nursery_size : int;       (* cells 0..nursery_size-1 *)
    mutable promotion_age : int;  (* cycles survived before promotion *)
    mutable ages : int array;     (* per-cell age *)
    mutable gc_count : int;
    mutable minor_collections : int;
    mutable major_collections : int;
  }

  let create total_cap nursery_frac =
    let nursery_size = int_of_float (float_of_int total_cap *. nursery_frac) in
    let heap = Heap.create total_cap in
    {
      heap;
      nursery_size = max 1 nursery_size;
      promotion_age = 2;
      ages = Array.make total_cap 0;
      gc_count = 0;
      minor_collections = 0;
      major_collections = 0;
    }

  let alloc t size =
    let idx = Heap.alloc t.heap size in
    t.heap.Heap.cells.(idx).generation <- 0;
    t.ages.(idx) <- 0;
    idx

  let set_ref t src slot dst =
    Heap.set_ref t.heap src slot dst

  (** Minor collection: only scan nursery (generation 0) *)
  let minor_collect t roots =
    let live_before = Heap.live_count t.heap in
    Heap.reset_marks t.heap;

    (* Mark phase from roots — but only traverse into nursery *)
    let rec mark_young idx =
      if Heap.is_valid t.heap idx then begin
        let c = t.heap.Heap.cells.(idx) in
        if c.alive && not c.marked then begin
          c.marked <- true;
          Array.iter (fun r ->
            if r <> null_ref then mark_young r
          ) c.refs
        end
      end
    in
    List.iter mark_young (RootSet.to_list roots);
    (* Also mark from old-gen objects that point to nursery (write barrier sim) *)
    Array.iteri (fun i c ->
      if c.alive && c.generation > 0 then begin
        c.marked <- true;  (* old gen survives *)
        Array.iter (fun r ->
          if r <> null_ref then mark_young r
        ) c.refs
      end
    ) t.heap.Heap.cells;

    (* Sweep only nursery, promote survivors *)
    let collected = ref 0 in
    let promoted = ref 0 in
    Array.iteri (fun i c ->
      if c.alive && c.generation = 0 then begin
        if not c.marked then begin
          Heap.free t.heap i;
          incr collected
        end else begin
          t.ages.(i) <- t.ages.(i) + 1;
          if t.ages.(i) >= t.promotion_age then begin
            c.generation <- 1;
            incr promoted
          end;
          c.marked <- false
        end
      end else if c.alive then
        c.marked <- false
    ) t.heap.Heap.cells;

    t.minor_collections <- t.minor_collections + 1;
    t.gc_count <- t.gc_count + 1;
    t.heap.Heap.gc_count <- t.heap.Heap.gc_count + 1;
    let live_after = Heap.live_count t.heap in
    { (empty_stats t.heap.Heap.capacity) with
      collected = !collected; survived = live_after;
      live_before; live_after;
      promoted = !promoted }

  (** Major collection: full mark-and-sweep of all generations *)
  let major_collect t roots =
    let stats = MarkSweep.collect t.heap roots in
    t.major_collections <- t.major_collections + 1;
    t.gc_count <- t.gc_count + 1;
    stats

  let summary t =
    Printf.sprintf "GenGC: cap=%d live=%d minor=%d major=%d nursery=%d"
      t.heap.Heap.capacity (Heap.live_count t.heap)
      t.minor_collections t.major_collections t.nursery_size
end

(* ── Fragmentation analysis ───────────────────────────────────────── *)

module Fragmentation = struct
  type report = {
    total_cells : int;
    live_cells : int;
    dead_cells : int;
    free_cells : int;
    fragments : int;            (* number of contiguous free regions *)
    largest_fragment : int;     (* size of largest contiguous free region *)
    fragmentation_ratio : float; (* 1.0 - (largest_fragment / total_free) *)
  }

  let analyze heap =
    let n = heap.Heap.capacity in
    let live = Heap.live_count heap in
    let total_free = n - live in
    if total_free = 0 then
      { total_cells = n; live_cells = live; dead_cells = 0;
        free_cells = 0; fragments = 0; largest_fragment = 0;
        fragmentation_ratio = 0.0 }
    else begin
      let fragments = ref 0 in
      let largest = ref 0 in
      let current = ref 0 in
      let in_free = ref false in
      for i = 0 to n - 1 do
        if not heap.Heap.cells.(i).alive then begin
          if not !in_free then begin
            in_free := true;
            incr fragments;
            current := 0
          end;
          incr current;
          if !current > !largest then largest := !current
        end else begin
          in_free := false;
          current := 0
        end
      done;
      let ratio =
        if total_free <= 0 then 0.0
        else 1.0 -. (float_of_int !largest /. float_of_int total_free)
      in
      { total_cells = n; live_cells = live;
        dead_cells = total_free - (n - live - total_free |> max 0);
        free_cells = total_free;
        fragments = !fragments; largest_fragment = !largest;
        fragmentation_ratio = ratio }
    end

  let report_to_string r =
    Printf.sprintf
      "Fragmentation Report:\n  Total cells: %d\n  Live: %d\n  Free: %d\n  \
       Fragments: %d\n  Largest free block: %d\n  Fragmentation ratio: %.3f"
      r.total_cells r.live_cells r.free_cells
      r.fragments r.largest_fragment r.fragmentation_ratio
end

(* ── GC comparison / benchmark ────────────────────────────────────── *)

module Benchmark = struct
  type scenario = {
    name : string;
    allocations : int;
    max_refs : int;
    root_fraction : float;   (* fraction of objects that are roots *)
    cycle_probability : float; (* probability of creating back-edges *)
  }

  let default_scenario = {
    name = "default";
    allocations = 100;
    max_refs = 3;
    root_fraction = 0.3;
    cycle_probability = 0.1;
  }

  let high_garbage = {
    name = "high-garbage";
    allocations = 200;
    max_refs = 2;
    root_fraction = 0.1;
    cycle_probability = 0.05;
  }

  let cyclic_heavy = {
    name = "cyclic-heavy";
    allocations = 80;
    max_refs = 4;
    root_fraction = 0.2;
    cycle_probability = 0.4;
  }

  (** Run mark-and-sweep on a scenario, returning stats *)
  let run_mark_sweep scenario =
    let heap = Heap.create (scenario.allocations * 2) in
    let roots = RootSet.create () in
    let indices = Array.make scenario.allocations (-1) in

    (* Deterministic pseudo-random using LCG *)
    let seed = ref 42 in
    let next_rand () =
      seed := (!seed * 1103515245 + 12345) land 0x7FFFFFFF;
      !seed
    in

    (* Allocate objects *)
    for i = 0 to scenario.allocations - 1 do
      let nrefs = (next_rand () mod (scenario.max_refs + 1)) in
      let idx = Heap.alloc heap nrefs in
      indices.(i) <- idx;
      (* Make some objects roots *)
      let threshold = int_of_float (scenario.root_fraction *. 1000.0) in
      if (next_rand () mod 1000) < threshold then
        RootSet.add roots idx
    done;

    (* Create references *)
    for i = 0 to scenario.allocations - 1 do
      let c = heap.Heap.cells.(indices.(i)) in
      for s = 0 to c.size - 1 do
        let target = next_rand () mod scenario.allocations in
        (* Maybe create cycle *)
        let cycle_threshold = int_of_float (scenario.cycle_probability *. 1000.0) in
        let actual_target =
          if target < i && (next_rand () mod 1000) < cycle_threshold
          then indices.(next_rand () mod (i + 1))  (* back-edge *)
          else indices.(target)
        in
        Heap.set_ref heap indices.(i) s actual_target
      done
    done;

    MarkSweep.collect heap roots

  (** Run all scenarios and return results *)
  let run_all () =
    let scenarios = [default_scenario; high_garbage; cyclic_heavy] in
    List.map (fun s ->
      let stats = run_mark_sweep s in
      (s.name, stats)
    ) scenarios

  let results_to_string results =
    let buf = Buffer.create 256 in
    Buffer.add_string buf "GC Benchmark Results:\n";
    Buffer.add_string buf (String.make 60 '-');
    Buffer.add_char buf '\n';
    List.iter (fun (name, stats) ->
      Buffer.add_string buf (Printf.sprintf
        "  %-15s | before: %3d | after: %3d | collected: %3d | survived: %3d\n"
        name stats.live_before stats.live_after stats.collected stats.survived)
    ) results;
    Buffer.contents buf
end

(* ── Heap visualization (ASCII) ───────────────────────────────────── *)

module HeapViz = struct
  (** ASCII visualization of heap state. Each cell is one character:
   *  '#' = live, '.' = free, 'R' = root, 'O' = old-gen *)
  let to_string heap roots =
    let root_set = RootSet.to_list roots in
    let buf = Buffer.create (heap.Heap.capacity + 20) in
    Buffer.add_string buf "|";
    Array.iteri (fun i c ->
      let ch =
        if not c.alive then '.'
        else if List.mem i root_set then 'R'
        else if c.generation > 0 then 'O'
        else '#'
      in
      Buffer.add_char buf ch
    ) heap.Heap.cells;
    Buffer.add_string buf "|";
    Buffer.contents buf

  (** Show reference graph as adjacency list *)
  let refs_to_string heap =
    let buf = Buffer.create 128 in
    Array.iteri (fun i c ->
      if c.alive && c.size > 0 then begin
        Buffer.add_string buf (Printf.sprintf "  [%d] ->" i);
        Array.iter (fun r ->
          if r <> null_ref then
            Buffer.add_string buf (Printf.sprintf " %d" r)
          else
            Buffer.add_string buf " _"
        ) c.refs;
        Buffer.add_char buf '\n'
      end
    ) heap.Heap.cells;
    Buffer.contents buf
end

(* ── Tests ────────────────────────────────────────────────────────── *)

let tests_passed = ref 0
let tests_failed = ref 0

let assert_equal name expected actual =
  if expected = actual then begin
    incr tests_passed
  end else begin
    Printf.printf "FAIL: %s — expected %s, got %s\n" name
      (string_of_int expected) (string_of_int actual);
    incr tests_failed
  end

let assert_true name cond =
  if cond then incr tests_passed
  else begin
    Printf.printf "FAIL: %s — expected true\n" name;
    incr tests_failed
  end

let assert_false name cond =
  if not cond then incr tests_passed
  else begin
    Printf.printf "FAIL: %s — expected false\n" name;
    incr tests_failed
  end

let () =
  Printf.printf "=== Garbage Collector Simulator Tests ===\n\n";

  (* ── Heap basics ──────────────────────────────────────────────── *)
  let h = Heap.create 10 in
  assert_equal "heap initial live" 0 (Heap.live_count h);
  let a = Heap.alloc h 2 in
  assert_equal "alloc returns index" 0 a;
  assert_equal "live after alloc" 1 (Heap.live_count h);
  let b = Heap.alloc h 1 in
  assert_equal "second alloc" 1 b;
  assert_equal "live after 2 allocs" 2 (Heap.live_count h);
  Heap.set_ref h a 0 b;
  assert_equal "get_ref" b (Heap.get_ref h a 0);
  Heap.free h b;
  assert_equal "live after free" 1 (Heap.live_count h);

  (* ── RootSet ──────────────────────────────────────────────────── *)
  let r = RootSet.create () in
  RootSet.add r 5;
  RootSet.add r 3;
  assert_true "root mem" (RootSet.mem r 5);
  assert_false "root not mem" (RootSet.mem r 7);
  assert_equal "root size" 2 (RootSet.size r);
  RootSet.remove r 5;
  assert_false "root removed" (RootSet.mem r 5);
  assert_equal "root size after remove" 1 (RootSet.size r);
  RootSet.add r 3;  (* duplicate add *)
  assert_equal "root no dup" 1 (RootSet.size r);

  (* ── Mark-and-Sweep: basic ────────────────────────────────────── *)
  let h = Heap.create 20 in
  let roots = RootSet.create () in
  let a = Heap.alloc h 2 in
  let b = Heap.alloc h 1 in
  let c = Heap.alloc h 0 in
  let d = Heap.alloc h 0 in   (* unreachable *)
  ignore d;
  Heap.set_ref h a 0 b;
  Heap.set_ref h a 1 c;
  RootSet.add roots a;
  let stats = MarkSweep.collect h roots in
  assert_equal "ms: collected 1" 1 stats.collected;
  assert_equal "ms: survived 3" 3 stats.survived;
  assert_equal "ms: live_after" 3 stats.live_after;

  (* ── Mark-and-Sweep: all garbage ──────────────────────────────── *)
  let h = Heap.create 10 in
  let roots = RootSet.create () in
  let _ = Heap.alloc h 0 in
  let _ = Heap.alloc h 0 in
  let _ = Heap.alloc h 0 in
  let stats = MarkSweep.collect h roots in
  assert_equal "ms: all garbage" 3 stats.collected;
  assert_equal "ms: none survive" 0 stats.survived;

  (* ── Mark-and-Sweep: cycle reachable from root ────────────────── *)
  let h = Heap.create 10 in
  let roots = RootSet.create () in
  let a = Heap.alloc h 1 in
  let b = Heap.alloc h 1 in
  Heap.set_ref h a 0 b;
  Heap.set_ref h b 0 a;   (* cycle *)
  RootSet.add roots a;
  let stats = MarkSweep.collect h roots in
  assert_equal "ms: cycle kept" 0 stats.collected;
  assert_equal "ms: cycle both alive" 2 stats.survived;

  (* ── Mark-and-Sweep: unreachable cycle ────────────────────────── *)
  let h = Heap.create 10 in
  let roots = RootSet.create () in
  let a = Heap.alloc h 1 in
  let b = Heap.alloc h 1 in
  Heap.set_ref h a 0 b;
  Heap.set_ref h b 0 a;   (* unreachable cycle *)
  let stats = MarkSweep.collect h roots in
  assert_equal "ms: unreachable cycle collected" 2 stats.collected;

  (* ── Copying GC: basic ────────────────────────────────────────── *)
  let cg = CopyingGC.create 20 in
  let roots = RootSet.create () in
  let a = CopyingGC.alloc cg 1 in
  let b = CopyingGC.alloc cg 0 in
  let _ = CopyingGC.alloc cg 0 in (* garbage *)
  CopyingGC.set_ref cg a 0 b;
  RootSet.add roots a;
  let stats = CopyingGC.collect cg roots in
  assert_equal "copy: collected 1" 1 stats.collected;
  assert_equal "copy: survived 2" 2 stats.survived;

  (* ── Copying GC: all garbage ──────────────────────────────────── *)
  let cg = CopyingGC.create 20 in
  let roots = RootSet.create () in
  let _ = CopyingGC.alloc cg 0 in
  let _ = CopyingGC.alloc cg 0 in
  let stats = CopyingGC.collect cg roots in
  assert_equal "copy: all garbage" 2 stats.collected;
  assert_equal "copy: 0 survived" 0 stats.survived;

  (* ── Copying GC: chain ────────────────────────────────────────── *)
  let cg = CopyingGC.create 20 in
  let roots = RootSet.create () in
  let a = CopyingGC.alloc cg 1 in
  let b = CopyingGC.alloc cg 1 in
  let c = CopyingGC.alloc cg 0 in
  CopyingGC.set_ref cg a 0 b;
  CopyingGC.set_ref cg b 0 c;
  RootSet.add roots a;
  let stats = CopyingGC.collect cg roots in
  assert_equal "copy: chain survived" 3 stats.survived;
  assert_equal "copy: chain collected" 0 stats.collected;

  (* ── Copying GC: objects renumbered after collection ──────────── *)
  let cg = CopyingGC.create 20 in
  let roots = RootSet.create () in
  let _ = CopyingGC.alloc cg 0 in   (* garbage, idx 0 *)
  let b = CopyingGC.alloc cg 0 in   (* keep, idx 1 *)
  RootSet.add roots b;
  let _ = CopyingGC.collect cg roots in
  (* After collection, b should be renumbered to 0 in to-space *)
  assert_true "copy: root updated" (RootSet.mem roots 0);
  assert_equal "copy: next_free" 1 cg.CopyingGC.next_free;

  (* ── Reference Counting: basic ────────────────────────────────── *)
  let h = Heap.create 10 in
  let a = Heap.alloc h 1 in
  let b = Heap.alloc h 0 in
  h.Heap.cells.(a).ref_count <- 1;  (* simulate root ref *)
  RefCount.set_ref h a 0 b;
  assert_equal "rc: b has ref 1" 1 h.Heap.cells.(b).ref_count;
  (* Remove the reference *)
  RefCount.set_ref h a 0 null_ref;
  (* b should be freed since its ref_count dropped to 0 *)
  assert_false "rc: b freed" h.Heap.cells.(b).alive;

  (* ── Reference Counting: chain free ───────────────────────────── *)
  let h = Heap.create 10 in
  let a = Heap.alloc h 1 in
  let b = Heap.alloc h 1 in
  let c = Heap.alloc h 0 in
  h.Heap.cells.(a).ref_count <- 1;
  RefCount.set_ref h a 0 b;
  RefCount.set_ref h b 0 c;
  (* Now remove a's ref to b *)
  RefCount.set_ref h a 0 null_ref;
  assert_false "rc: chain b freed" h.Heap.cells.(b).alive;
  assert_false "rc: chain c freed" h.Heap.cells.(c).alive;

  (* ── Reference Counting: cycle detection ──────────────────────── *)
  let h = Heap.create 10 in
  let a = Heap.alloc h 1 in
  let b = Heap.alloc h 1 in
  (* a -> b -> a, no external refs *)
  Heap.set_ref h a 0 b;
  Heap.set_ref h b 0 a;
  h.Heap.cells.(a).ref_count <- 1;  (* only from b *)
  h.Heap.cells.(b).ref_count <- 1;  (* only from a *)
  let (_, cycle_count) = RefCount.detect_cycles h in
  assert_equal "rc: cycle detected" 2 cycle_count;
  let stats = RefCount.collect_cycles h in
  assert_equal "rc: cycle collected" 2 stats.collected;
  assert_false "rc: cycle a dead" h.Heap.cells.(a).alive;
  assert_false "rc: cycle b dead" h.Heap.cells.(b).alive;

  (* ── Reference Counting: no false cycle ───────────────────────── *)
  let h = Heap.create 10 in
  let roots = RootSet.create () in
  let a = Heap.alloc h 1 in
  let b = Heap.alloc h 0 in
  Heap.set_ref h a 0 b;
  h.Heap.cells.(a).ref_count <- 2;  (* external ref *)
  h.Heap.cells.(b).ref_count <- 1;
  ignore roots;
  let (_, cycle_count) = RefCount.detect_cycles h in
  assert_equal "rc: no false cycle" 0 cycle_count;

  (* ── Generational GC: basic minor collection ──────────────────── *)
  let gg = GenerationalGC.create 20 0.5 in
  let roots = RootSet.create () in
  let a = GenerationalGC.alloc gg 1 in
  let b = GenerationalGC.alloc gg 0 in
  let _ = GenerationalGC.alloc gg 0 in  (* garbage *)
  GenerationalGC.set_ref gg a 0 b;
  RootSet.add roots a;
  let stats = GenerationalGC.minor_collect gg roots in
  assert_equal "gen: minor collected" 1 stats.collected;
  assert_equal "gen: minor survived" 2 stats.survived;

  (* ── Generational GC: promotion after 2 minor cycles ──────────── *)
  let gg = GenerationalGC.create 20 0.5 in
  let roots = RootSet.create () in
  let a = GenerationalGC.alloc gg 0 in
  RootSet.add roots a;
  let _ = GenerationalGC.minor_collect gg roots in
  assert_equal "gen: age 1" 1 gg.GenerationalGC.ages.(a);
  assert_equal "gen: still young" 0 gg.GenerationalGC.heap.Heap.cells.(a).generation;
  let stats2 = GenerationalGC.minor_collect gg roots in
  assert_equal "gen: promoted" 1 stats2.promoted;
  assert_equal "gen: now old" 1 gg.GenerationalGC.heap.Heap.cells.(a).generation;

  (* ── Generational GC: major collects everything ───────────────── *)
  let gg = GenerationalGC.create 20 0.5 in
  let roots = RootSet.create () in
  let a = GenerationalGC.alloc gg 0 in
  RootSet.add roots a;
  (* Promote *)
  let _ = GenerationalGC.minor_collect gg roots in
  let _ = GenerationalGC.minor_collect gg roots in
  (* Add garbage *)
  let _ = GenerationalGC.alloc gg 0 in
  let _ = GenerationalGC.alloc gg 0 in
  let stats = GenerationalGC.major_collect gg roots in
  assert_equal "gen: major collected" 2 stats.collected;
  assert_equal "gen: major survived" 1 stats.survived;

  (* ── Fragmentation analysis ───────────────────────────────────── *)
  let h = Heap.create 10 in
  let _ = Heap.alloc h 0 in  (* 0: live *)
  let b = Heap.alloc h 0 in  (* 1: will die *)
  let _ = Heap.alloc h 0 in  (* 2: live *)
  let d = Heap.alloc h 0 in  (* 3: will die *)
  let _ = Heap.alloc h 0 in  (* 4: live *)
  Heap.free h b;
  Heap.free h d;
  let frag = Fragmentation.analyze h in
  assert_equal "frag: live" 3 frag.live_cells;
  assert_equal "frag: free" 7 frag.free_cells;
  assert_equal "frag: fragments" 3 frag.fragments;
  assert_equal "frag: largest" 5 frag.largest_fragment;

  (* ── Fragmentation: no fragmentation ──────────────────────────── *)
  let h = Heap.create 5 in
  let _ = Heap.alloc h 0 in
  let _ = Heap.alloc h 0 in
  let frag = Fragmentation.analyze h in
  assert_equal "frag: contiguous free" 3 frag.free_cells;
  assert_equal "frag: 1 fragment" 1 frag.fragments;
  assert_equal "frag: largest=3" 3 frag.largest_fragment;
  assert_true "frag: ratio 0" (frag.fragmentation_ratio < 0.001);

  (* ── Fragmentation: full heap ─────────────────────────────────── *)
  let h = Heap.create 3 in
  let _ = Heap.alloc h 0 in
  let _ = Heap.alloc h 0 in
  let _ = Heap.alloc h 0 in
  let frag = Fragmentation.analyze h in
  assert_equal "frag: full" 0 frag.free_cells;
  assert_equal "frag: no frags" 0 frag.fragments;

  (* ── HeapViz ──────────────────────────────────────────────────── *)
  let h = Heap.create 6 in
  let roots = RootSet.create () in
  let a = Heap.alloc h 0 in
  let _ = Heap.alloc h 0 in
  let _ = Heap.alloc h 0 in
  RootSet.add roots a;
  let viz = HeapViz.to_string h roots in
  assert_equal "viz length" 8 (String.length viz);  (* |R##...|  *)
  assert_true "viz starts |" (String.get viz 0 = '|');
  assert_true "viz root R" (String.get viz 1 = 'R');
  assert_true "viz live #" (String.get viz 2 = '#');

  (* ── Benchmark ────────────────────────────────────────────────── *)
  let results = Benchmark.run_all () in
  assert_equal "benchmark: 3 results" 3 (List.length results);
  List.iter (fun (name, stats) ->
    assert_true (Printf.sprintf "bench %s: collected >= 0" name) (stats.collected >= 0);
    assert_true (Printf.sprintf "bench %s: survived >= 0" name) (stats.survived >= 0);
    assert_true (Printf.sprintf "bench %s: live_after >= 0" name) (stats.live_after >= 0)
  ) results;

  (* ── Copying GC: cycle reachable from root ────────────────────── *)
  let cg = CopyingGC.create 20 in
  let roots = RootSet.create () in
  let a = CopyingGC.alloc cg 1 in
  let b = CopyingGC.alloc cg 1 in
  CopyingGC.set_ref cg a 0 b;
  CopyingGC.set_ref cg b 0 a;
  RootSet.add roots a;
  let stats = CopyingGC.collect cg roots in
  assert_equal "copy: cycle survived" 2 stats.survived;
  assert_equal "copy: cycle collected 0" 0 stats.collected;

  (* ── Multiple GC runs ─────────────────────────────────────────── *)
  let h = Heap.create 20 in
  let roots = RootSet.create () in
  let a = Heap.alloc h 0 in
  RootSet.add roots a;
  let _ = MarkSweep.collect h roots in
  let _ = Heap.alloc h 0 in  (* garbage *)
  let stats2 = MarkSweep.collect h roots in
  assert_equal "ms: second run collected" 1 stats2.collected;
  assert_equal "ms: gc_count 2" 2 h.Heap.gc_count;

  (* ── Heap summary ─────────────────────────────────────────────── *)
  let s = Heap.summary h in
  assert_true "summary not empty" (String.length s > 0);

  (* ── CopyingGC summary ───────────────────────────────────────── *)
  let cg = CopyingGC.create 10 in
  let s = CopyingGC.summary cg in
  assert_true "copy summary not empty" (String.length s > 0);

  (* ── GenerationalGC summary ──────────────────────────────────── *)
  let gg = GenerationalGC.create 20 0.5 in
  let s = GenerationalGC.summary gg in
  assert_true "gen summary not empty" (String.length s > 0);

  (* ── Fragmentation report string ──────────────────────────────── *)
  let h = Heap.create 5 in
  let _ = Heap.alloc h 0 in
  let frag = Fragmentation.analyze h in
  let s = Fragmentation.report_to_string frag in
  assert_true "frag report not empty" (String.length s > 0);

  (* ── Benchmark results string ─────────────────────────────────── *)
  let results = Benchmark.run_all () in
  let s = Benchmark.results_to_string results in
  assert_true "bench results not empty" (String.length s > 0);

  (* ── HeapViz refs ─────────────────────────────────────────────── *)
  let h = Heap.create 5 in
  let a = Heap.alloc h 1 in
  let b = Heap.alloc h 0 in
  Heap.set_ref h a 0 b;
  let s = HeapViz.refs_to_string h in
  assert_true "refs string has arrow" (String.length s > 0);

  (* ── Edge cases ───────────────────────────────────────────────── *)
  (* Empty heap collection *)
  let h = Heap.create 5 in
  let roots = RootSet.create () in
  let stats = MarkSweep.collect h roots in
  assert_equal "ms: empty heap" 0 stats.collected;

  (* All roots *)
  let h = Heap.create 5 in
  let roots = RootSet.create () in
  let a = Heap.alloc h 0 in
  let b = Heap.alloc h 0 in
  let c = Heap.alloc h 0 in
  RootSet.add roots a;
  RootSet.add roots b;
  RootSet.add roots c;
  let stats = MarkSweep.collect h roots in
  assert_equal "ms: all roots survive" 0 stats.collected;
  assert_equal "ms: all roots count" 3 stats.survived;

  (* RootSet clear *)
  let r = RootSet.create () in
  RootSet.add r 1;
  RootSet.add r 2;
  RootSet.clear r;
  assert_equal "root clear" 0 (RootSet.size r);

  Printf.printf "\n%d tests passed, %d failed (total: %d)\n"
    !tests_passed !tests_failed (!tests_passed + !tests_failed);
  if !tests_failed > 0 then
    Printf.printf "*** SOME TESTS FAILED ***\n"
  else
    Printf.printf "All tests passed!\n"
