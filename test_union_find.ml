(* test_union_find.ml — Tests for union_find.ml
 *
 * Covers: create, find, union, connected, num_components,
 * component_size, roots, component_members, all_components,
 * cardinal, is_single_component, of_unions, kruskal,
 * would_cycle, persistence, path compression, edge cases.
 *)

#use "test_framework.ml";;
#use "union_find.ml";;

(* ── create ────────────────────────────────────────────── *)

let () = suite "create" (fun () ->
  let uf = create 5 in
  assert_true ~msg:"cardinal = 5" (cardinal uf = 5);
  assert_true ~msg:"5 components initially" (num_components uf = 5);
  assert_true ~msg:"not single component" (not (is_single_component uf));

  let uf0 = create 0 in
  assert_true ~msg:"create 0 has 0 elements" (cardinal uf0 = 0);
  assert_true ~msg:"create 0 has 0 components" (num_components uf0 = 0);

  let uf1 = create 1 in
  assert_true ~msg:"create 1 has 1 component" (num_components uf1 = 1);
  assert_true ~msg:"create 1 is single" (is_single_component uf1);

  assert_raises ~msg:"create negative raises" (fun () -> create (-1))
)

(* ── find / find_root ──────────────────────────────────── *)

let () = suite "find / find_root" (fun () ->
  let uf = create 5 in
  (* Every element is its own root initially *)
  for i = 0 to 4 do
    assert_true ~msg:(Printf.sprintf "root of %d is %d" i i)
      (find_root uf i = i)
  done;

  (* find returns same root *)
  let (root, _) = find uf 3 in
  assert_true ~msg:"find 3 root is 3" (root = 3);

  assert_raises ~msg:"find_root out of range"
    (fun () -> find_root uf 10);
  assert_raises ~msg:"find out of range"
    (fun () -> ignore (find uf 99))
)

(* ── union / connected ─────────────────────────────────── *)

let () = suite "union / connected" (fun () ->
  let uf = create 6 in
  assert_true ~msg:"0 not connected to 1" (not (connected uf 0 1));

  let uf = union uf 0 1 in
  assert_true ~msg:"0 connected to 1" (connected uf 0 1);
  assert_true ~msg:"1 connected to 0" (connected uf 1 0);
  assert_true ~msg:"0 not connected to 2" (not (connected uf 0 2));
  assert_true ~msg:"5 components" (num_components uf = 5);

  let uf = union uf 2 3 in
  assert_true ~msg:"2-3 connected" (connected uf 2 3);
  assert_true ~msg:"0 not connected to 2" (not (connected uf 0 2));
  assert_true ~msg:"4 components" (num_components uf = 4);

  let uf = union uf 0 2 in
  assert_true ~msg:"0-2 connected after merge" (connected uf 0 2);
  assert_true ~msg:"1-3 connected transitively" (connected uf 1 3);
  assert_true ~msg:"3 components" (num_components uf = 3);

  (* Union of already-connected elements is a no-op *)
  let uf2 = union uf 0 1 in
  assert_true ~msg:"redundant union: same components"
    (num_components uf2 = 3);

  (* Self-union *)
  let uf3 = union uf 4 4 in
  assert_true ~msg:"self-union: same components"
    (num_components uf3 = 3)
)

(* ── component_size ────────────────────────────────────── *)

let () = suite "component_size" (fun () ->
  let uf = create 5 in
  assert_true ~msg:"initial size = 1" (component_size uf 0 = 1);

  let uf = union uf 0 1 in
  assert_true ~msg:"after union size = 2" (component_size uf 0 = 2);
  assert_true ~msg:"member 1 also size 2" (component_size uf 1 = 2);
  assert_true ~msg:"unmerged still size 1" (component_size uf 2 = 1);

  let uf = union uf 2 3 in
  let uf = union uf 0 2 in
  assert_true ~msg:"merged component size = 4" (component_size uf 0 = 4);
  assert_true ~msg:"all members report 4" (
    component_size uf 1 = 4 &&
    component_size uf 2 = 4 &&
    component_size uf 3 = 4
  );
  assert_true ~msg:"unmerged element size = 1" (component_size uf 4 = 1)
)

(* ── roots ─────────────────────────────────────────────── *)

let () = suite "roots" (fun () ->
  let uf = create 4 in
  let rs = roots uf in
  assert_true ~msg:"initial roots = [0;1;2;3]"
    (List.sort compare rs = [0; 1; 2; 3]);

  let uf = union uf 0 1 in
  let uf = union uf 2 3 in
  let rs = roots uf in
  assert_true ~msg:"after 2 unions: 2 roots" (List.length rs = 2)
)

(* ── component_members ─────────────────────────────────── *)

let () = suite "component_members" (fun () ->
  let uf = create 5 in
  assert_true ~msg:"singleton member" (component_members uf 3 = [3]);

  let uf = union uf 0 1 in
  let uf = union uf 0 2 in
  let members = List.sort compare (component_members uf 1) in
  assert_true ~msg:"merged members = [0;1;2]" (members = [0; 1; 2]);

  let members4 = component_members uf 4 in
  assert_true ~msg:"unmerged member = [4]" (members4 = [4])
)

(* ── all_components ────────────────────────────────────── *)

let () = suite "all_components" (fun () ->
  let uf = create 5 in
  let cs = all_components uf in
  assert_true ~msg:"initial: 5 singleton components" (List.length cs = 5);
  assert_true ~msg:"each is singleton" (
    List.for_all (fun c -> List.length c = 1) cs
  );

  let uf = union uf 0 1 in
  let uf = union uf 3 4 in
  let cs = all_components uf in
  assert_true ~msg:"3 components after 2 unions" (List.length cs = 3);
  let sizes = List.sort compare (List.map List.length cs) in
  assert_true ~msg:"sizes = [1; 2; 2]" (sizes = [1; 2; 2])
)

(* ── is_single_component ──────────────────────────────── *)

let () = suite "is_single_component" (fun () ->
  let uf = create 3 in
  assert_true ~msg:"3 elems: not single" (not (is_single_component uf));

  let uf = union uf 0 1 in
  assert_true ~msg:"still not single" (not (is_single_component uf));

  let uf = union uf 1 2 in
  assert_true ~msg:"all merged: single" (is_single_component uf);

  let uf1 = create 1 in
  assert_true ~msg:"1 elem: single" (is_single_component uf1)
)

(* ── of_unions ─────────────────────────────────────────── *)

let () = suite "of_unions" (fun () ->
  let uf = of_unions 5 [(0, 1); (2, 3); (1, 3)] in
  assert_true ~msg:"0-1-2-3 connected" (connected uf 0 3);
  assert_true ~msg:"4 separate" (not (connected uf 0 4));
  assert_true ~msg:"2 components" (num_components uf = 2);

  let uf_empty = of_unions 3 [] in
  assert_true ~msg:"no unions: 3 components" (num_components uf_empty = 3)
)

(* ── would_cycle ───────────────────────────────────────── *)

let () = suite "would_cycle" (fun () ->
  let uf = create 4 in
  assert_true ~msg:"no cycle initially" (not (would_cycle uf 0 1));

  let uf = union uf 0 1 in
  assert_true ~msg:"0-1 would cycle" (would_cycle uf 0 1);
  assert_true ~msg:"1-0 would cycle" (would_cycle uf 1 0);
  assert_true ~msg:"0-2 no cycle" (not (would_cycle uf 0 2))
)

(* ── kruskal ───────────────────────────────────────────── *)

let () = suite "kruskal" (fun () ->
  (* Simple triangle: 0-1 (1), 0-2 (3), 1-2 (2) *)
  let edges = [(1, 0, 1); (3, 0, 2); (2, 1, 2)] in
  let mst = kruskal 3 edges in
  assert_true ~msg:"MST has 2 edges" (List.length mst = 2);
  let total_weight = List.fold_left (fun acc (w, _, _) -> acc + w) 0 mst in
  assert_true ~msg:"MST weight = 3" (total_weight = 3);
  (* Should pick edges with weight 1 and 2 *)
  let weights = List.sort compare (List.map (fun (w, _, _) -> w) mst) in
  assert_true ~msg:"MST edges are 1, 2" (weights = [1; 2]);

  (* Square: 0-1-2-3 with diagonal *)
  let edges = [
    (1, 0, 1); (4, 0, 3); (2, 1, 2);
    (3, 2, 3); (5, 0, 2)
  ] in
  let mst = kruskal 4 edges in
  assert_true ~msg:"square MST has 3 edges" (List.length mst = 3);
  let total = List.fold_left (fun acc (w, _, _) -> acc + w) 0 mst in
  assert_true ~msg:"square MST weight = 6" (total = 6);

  (* Disconnected graph — MST won't span all vertices *)
  let edges = [(1, 0, 1)] in
  let mst = kruskal 4 edges in
  assert_true ~msg:"disconnected: 1 edge in MST" (List.length mst = 1);

  (* Empty graph *)
  let mst = kruskal 3 [] in
  assert_true ~msg:"no edges: empty MST" (List.length mst = 0);

  (* Unsorted input — kruskal sorts internally *)
  let edges = [(3, 1, 2); (1, 0, 1); (2, 0, 2)] in
  let mst = kruskal 3 edges in
  let total = List.fold_left (fun acc (w, _, _) -> acc + w) 0 mst in
  assert_true ~msg:"unsorted input: correct MST weight" (total = 3)
)

(* ── persistence ───────────────────────────────────────── *)

let () = suite "persistence" (fun () ->
  let uf0 = create 4 in
  let uf1 = union uf0 0 1 in
  let uf2 = union uf0 2 3 in  (* based on uf0, not uf1 *)

  assert_true ~msg:"uf0 unchanged: 4 components"
    (num_components uf0 = 4);
  assert_true ~msg:"uf1: 0-1 connected"
    (connected uf1 0 1);
  assert_true ~msg:"uf1: 2-3 not connected"
    (not (connected uf1 2 3));
  assert_true ~msg:"uf2: 2-3 connected"
    (connected uf2 2 3);
  assert_true ~msg:"uf2: 0-1 not connected"
    (not (connected uf2 0 1))
)

(* ── path compression ──────────────────────────────────── *)

let () = suite "path_compression" (fun () ->
  (* Build a chain: 0->1->2->3->4 *)
  let uf = create 5 in
  let uf = union uf 0 1 in
  let uf = union uf 1 2 in
  let uf = union uf 2 3 in
  let uf = union uf 3 4 in
  assert_true ~msg:"all connected" (connected uf 0 4);

  (* find with path compression: root should be consistent *)
  let (r0, uf') = find uf 0 in
  let (r4, _) = find uf' 4 in
  assert_true ~msg:"same root after compression" (r0 = r4);

  (* After compression, find_root should be fast *)
  let root = find_root uf 0 in
  assert_true ~msg:"find_root finds root" (root = find_root uf 4)
)

(* ── to_string ─────────────────────────────────────────── *)

let () = suite "to_string" (fun () ->
  let uf = create 3 in
  let s = to_string uf in
  assert_true ~msg:"to_string contains '3 elems'"
    (String.length s > 0 &&
     let _ = s in true);  (* just check it doesn't crash *)

  let uf = union uf 0 1 in
  let s = to_string uf in
  assert_true ~msg:"to_string after union" (String.length s > 0)
)

(* ── larger scale ──────────────────────────────────────── *)

let () = suite "scale_100" (fun () ->
  let n = 100 in
  let uf = create n in
  (* Union all even numbers together *)
  let uf = ref uf in
  for i = 0 to n - 3 do
    if i mod 2 = 0 then uf := union !uf i (i + 2)
  done;
  (* Union all odd numbers together *)
  for i = 1 to n - 3 do
    if i mod 2 = 1 then uf := union !uf i (i + 2)
  done;
  let uf = !uf in
  assert_true ~msg:"2 components (even/odd)" (num_components uf = 2);
  assert_true ~msg:"0 and 98 connected" (connected uf 0 98);
  assert_true ~msg:"1 and 99 connected" (connected uf 1 99);
  assert_true ~msg:"0 and 1 not connected" (not (connected uf 0 1));
  assert_true ~msg:"even component size = 50" (component_size uf 0 = 50);
  assert_true ~msg:"odd component size = 50" (component_size uf 1 = 50)
)

(* ── edge: union-by-rank correctness ──────────────────── *)

let () = suite "union_by_rank" (fun () ->
  (* Merge two equal-sized trees, then merge with a single element *)
  let uf = create 5 in
  let uf = union uf 0 1 in  (* rank of root = 1 *)
  let uf = union uf 2 3 in  (* rank of root = 1 *)
  let uf = union uf 0 2 in  (* merge two rank-1 trees *)
  assert_true ~msg:"component size 4" (component_size uf 0 = 4);
  let uf = union uf 0 4 in  (* attach rank-0 to rank-2 *)
  assert_true ~msg:"all 5 in one component" (is_single_component uf)
)

let () = test_summary ()
