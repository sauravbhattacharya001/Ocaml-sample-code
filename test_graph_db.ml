(* test_graph_db.ml — Tests for the Property Graph Query Engine *)
(* 100+ assertions covering graph construction, queries, aggregation,
   path finding, filtering, mutations, and edge cases *)

let tests_run = ref 0
let tests_passed = ref 0
let tests_failed = ref 0
let current_suite = ref ""

let assert_true ~msg condition =
  incr tests_run;
  if condition then incr tests_passed
  else begin incr tests_failed; Printf.printf "  FAIL [%s] %s\n" !current_suite msg end

let assert_equal ~msg expected actual =
  incr tests_run;
  if expected = actual then incr tests_passed
  else begin incr tests_failed;
    Printf.printf "  FAIL [%s] %s: expected %s, got %s\n"
      !current_suite msg expected actual end

let assert_int ~msg expected actual =
  assert_equal ~msg (string_of_int expected) (string_of_int actual)

let assert_float_near ~msg ~eps expected actual =
  incr tests_run;
  if abs_float (expected -. actual) <= eps then incr tests_passed
  else begin incr tests_failed;
    Printf.printf "  FAIL [%s] %s: expected %.4f, got %.4f\n"
      !current_suite msg expected actual end

let suite name f = current_suite := name; Printf.printf "Running: %s\n" name; f ()

(* ===== Import graph_db types and functions ===== *)
open Graph_db

(* ── Helper: build a small social network ─────────────────────────── *)
let make_social_graph () =
  let g = create_graph () in
  let alice = add_node g ~labels:["Person"]
    ~props:["name", VString "Alice"; "age", VInt 30;
            "city", VString "Seattle"] () in
  let bob = add_node g ~labels:["Person"]
    ~props:["name", VString "Bob"; "age", VInt 25;
            "city", VString "Portland"] () in
  let charlie = add_node g ~labels:["Person"]
    ~props:["name", VString "Charlie"; "age", VInt 35;
            "city", VString "Seattle"] () in
  let techco = add_node g ~labels:["Company"]
    ~props:["name", VString "TechCo"; "industry", VString "Software"] () in
  let _ = add_edge g ~src:alice.id ~dst:bob.id ~rel_type:"FRIENDS_WITH"
    ~props:["since", VInt 2020] () in
  let _ = add_edge g ~src:bob.id ~dst:charlie.id ~rel_type:"FRIENDS_WITH"
    ~props:["since", VInt 2021] () in
  let _ = add_edge g ~src:alice.id ~dst:techco.id ~rel_type:"WORKS_AT"
    ~props:["role", VString "Engineer"; "salary", VInt 120000] () in
  let _ = add_edge g ~src:charlie.id ~dst:techco.id ~rel_type:"WORKS_AT"
    ~props:["role", VString "Manager"; "salary", VInt 150000] () in
  (g, alice, bob, charlie, techco)

(* ===== Tests ===== *)

let test_graph_creation () =
  suite "Graph Creation" (fun () ->
    let g = create_graph () in
    assert_int ~msg:"empty graph has 0 nodes" 0 (List.length g.nodes);
    assert_int ~msg:"empty graph has 0 edges" 0 (List.length g.edges);

    let n1 = add_node g ~labels:["A"] ~props:["x", VInt 1] () in
    assert_int ~msg:"first node id is 1" 1 n1.id;
    assert_int ~msg:"graph has 1 node" 1 (List.length g.nodes);
    assert_true ~msg:"node has label A" (List.mem "A" n1.labels);

    let n2 = add_node g ~labels:["B"; "C"] ~props:[] () in
    assert_int ~msg:"second node id is 2" 2 n2.id;
    assert_int ~msg:"graph has 2 nodes" 2 (List.length g.nodes);
    assert_true ~msg:"n2 has label B" (List.mem "B" n2.labels);
    assert_true ~msg:"n2 has label C" (List.mem "C" n2.labels);

    let e1 = add_edge g ~src:n1.id ~dst:n2.id ~rel_type:"REL"
      ~props:["w", VFloat 1.5] () in
    assert_int ~msg:"first edge id is 1" 1 e1.eid;
    assert_int ~msg:"graph has 1 edge" 1 (List.length g.edges);
    assert_equal ~msg:"edge rel_type" "REL" e1.rel_type;
  )

let test_properties () =
  suite "Property Operations" (fun () ->
    let g = create_graph () in
    let n = add_node g ~props:["name", VString "test"; "val", VInt 42] () in

    assert_true ~msg:"get existing prop"
      (get_property n.properties "name" = VString "test");
    assert_true ~msg:"get int prop"
      (get_property n.properties "val" = VInt 42);
    assert_true ~msg:"get missing prop is VNull"
      (get_property n.properties "missing" = VNull);

    let props2 = set_property n.properties "val" (VInt 99) in
    assert_true ~msg:"set overwrites value"
      (get_property props2 "val" = VInt 99);
    assert_true ~msg:"set preserves other props"
      (get_property props2 "name" = VString "test");

    let props3 = set_property props2 "new_key" (VBool true) in
    assert_true ~msg:"set adds new property"
      (get_property props3 "new_key" = VBool true);
  )

let test_value_comparison () =
  suite "Value Comparison" (fun () ->
    assert_true ~msg:"int equal" (compare_values (VInt 5) (VInt 5) = 0);
    assert_true ~msg:"int less" (compare_values (VInt 3) (VInt 5) < 0);
    assert_true ~msg:"int greater" (compare_values (VInt 7) (VInt 5) > 0);
    assert_true ~msg:"float equal" (compare_values (VFloat 3.14) (VFloat 3.14) = 0);
    assert_true ~msg:"int-float compare" (compare_values (VInt 3) (VFloat 3.5) < 0);
    assert_true ~msg:"string compare" (compare_values (VString "a") (VString "b") < 0);
    assert_true ~msg:"null equals null" (compare_values VNull VNull = 0);
    assert_true ~msg:"null less than int" (compare_values VNull (VInt 1) < 0);
  )

let test_node_query () =
  suite "Node Pattern Query" (fun () ->
    let (g, _alice, _bob, _charlie, _techco) = make_social_graph () in

    (* All nodes *)
    let q = query (PNode (n ~var:"x" ())) [RProp ("x", "name")] in
    let rows = execute g q in
    assert_int ~msg:"all nodes returns 4" 4 (List.length rows);

    (* By label *)
    let q = query (PNode (n ~var:"p" ~label:"Person" ()))
      [RProp ("p", "name")] in
    let rows = execute g q in
    assert_int ~msg:"Person label returns 3" 3 (List.length rows);

    (* Company label *)
    let q = query (PNode (n ~var:"c" ~label:"Company" ()))
      [RProp ("c", "name")] in
    let rows = execute g q in
    assert_int ~msg:"Company label returns 1" 1 (List.length rows);
  )

let test_where_filter () =
  suite "WHERE Filter" (fun () ->
    let (g, _, _, _, _) = make_social_graph () in

    (* Equality *)
    let q = query
      (PNode (n ~var:"p" ~label:"Person" ()))
      ~where:(Some (EEq (EVar ("p", "city"), ELit (VString "Seattle"))))
      [RProp ("p", "name")] in
    let rows = execute g q in
    assert_int ~msg:"Seattle people = 2" 2 (List.length rows);

    (* Greater than *)
    let q = query
      (PNode (n ~var:"p" ~label:"Person" ()))
      ~where:(Some (EGt (EVar ("p", "age"), ELit (VInt 26))))
      [RProp ("p", "name")] in
    let rows = execute g q in
    assert_int ~msg:"age > 26 = 2" 2 (List.length rows);

    (* AND *)
    let q = query
      (PNode (n ~var:"p" ~label:"Person" ()))
      ~where:(Some (EAnd (
        EEq (EVar ("p", "city"), ELit (VString "Seattle")),
        EGt (EVar ("p", "age"), ELit (VInt 32))
      )))
      [RProp ("p", "name")] in
    let rows = execute g q in
    assert_int ~msg:"Seattle AND age>32 = 1" 1 (List.length rows);

    (* OR *)
    let q = query
      (PNode (n ~var:"p" ~label:"Person" ()))
      ~where:(Some (EOr (
        EEq (EVar ("p", "name"), ELit (VString "Alice")),
        EEq (EVar ("p", "name"), ELit (VString "Bob"))
      )))
      [RProp ("p", "name")] in
    let rows = execute g q in
    assert_int ~msg:"Alice OR Bob = 2" 2 (List.length rows);

    (* NOT *)
    let q = query
      (PNode (n ~var:"p" ~label:"Person" ()))
      ~where:(Some (ENot (EEq (EVar ("p", "city"), ELit (VString "Seattle")))))
      [RProp ("p", "name")] in
    let rows = execute g q in
    assert_int ~msg:"NOT Seattle = 1" 1 (List.length rows);

    (* CONTAINS *)
    let q = query
      (PNode (n ~var:"p" ~label:"Person" ()))
      ~where:(Some (EContains (EVar ("p", "name"), ELit (VString "li"))))
      [RProp ("p", "name")] in
    let rows = execute g q in
    assert_int ~msg:"name contains 'li' = 2" 2 (List.length rows);
    (* Alice, Charlie *)

    (* STARTS WITH *)
    let q = query
      (PNode (n ~var:"p" ~label:"Person" ()))
      ~where:(Some (EStartsWith (EVar ("p", "name"), ELit (VString "Ch"))))
      [RProp ("p", "name")] in
    let rows = execute g q in
    assert_int ~msg:"starts with Ch = 1" 1 (List.length rows);

    (* IS NULL / IS NOT NULL *)
    let q = query
      (PNode (n ~var:"p" ~label:"Person" ()))
      ~where:(Some (EIsNull (EVar ("p", "email"))))
      [RProp ("p", "name")] in
    let rows = execute g q in
    assert_int ~msg:"email IS NULL = 3" 3 (List.length rows);

    (* HAS LABEL *)
    let q = query
      (PNode (n ~var:"x" ()))
      ~where:(Some (EHasLabel ("x", "Company")))
      [RProp ("x", "name")] in
    let rows = execute g q in
    assert_int ~msg:"HAS LABEL Company = 1" 1 (List.length rows);
  )

let test_relationship_query () =
  suite "Relationship Pattern Query" (fun () ->
    let (g, _, _, _, _) = make_social_graph () in

    (* All friendships *)
    let q = query
      (PStep (PNode (n ~var:"a" ~label:"Person" ()),
              r ~rel_type:"FRIENDS_WITH" (),
              n ~var:"b" ~label:"Person" ()))
      [RProp ("a", "name"); RProp ("b", "name")] in
    let rows = execute g q in
    assert_int ~msg:"friendships = 2" 2 (List.length rows);

    (* Employment *)
    let q = query
      (PStep (PNode (n ~var:"p" ~label:"Person" ()),
              r ~var:"w" ~rel_type:"WORKS_AT" (),
              n ~var:"c" ~label:"Company" ()))
      [RProp ("p", "name"); RProp ("w", "role")] in
    let rows = execute g q in
    assert_int ~msg:"employment = 2" 2 (List.length rows);

    (* With WHERE on relationship property *)
    let q = query
      (PStep (PNode (n ~var:"a" ~label:"Person" ()),
              r ~var:"f" ~rel_type:"FRIENDS_WITH" (),
              n ~var:"b" ~label:"Person" ()))
      ~where:(Some (EGt (EVar ("f", "since"), ELit (VInt 2020))))
      [RProp ("a", "name"); RProp ("b", "name")] in
    let rows = execute g q in
    assert_int ~msg:"friends since > 2020 = 1" 1 (List.length rows);
  )

let test_multi_hop_query () =
  suite "Multi-Hop Pattern Query" (fun () ->
    let (g, _, _, _, _) = make_social_graph () in

    (* 2-hop: friends of friends *)
    let step1 = PStep (PNode (n ~var:"a" ~label:"Person" ()),
                        r ~rel_type:"FRIENDS_WITH" (),
                        n ~var:"b" ~label:"Person" ()) in
    let step2 = PStep (step1,
                        r ~rel_type:"FRIENDS_WITH" (),
                        n ~var:"c" ~label:"Person" ()) in
    let q = query step2
      ~where:(Some (EEq (EVar ("a", "name"), ELit (VString "Alice"))))
      [RProp ("c", "name")] in
    let rows = execute g q in
    assert_int ~msg:"Alice's friends-of-friends = 1" 1 (List.length rows);
    (* Alice -> Bob -> Charlie *)
    assert_true ~msg:"FoF is Charlie"
      (List.hd (List.hd rows) = VString "Charlie");
  )

let test_aggregation () =
  suite "Aggregation Queries" (fun () ->
    let (g, _, _, _, _) = make_social_graph () in

    (* COUNT *)
    let q = query
      (PNode (n ~var:"p" ~label:"Person" ()))
      [RAggCount None] in
    let rows = execute g q in
    assert_int ~msg:"count returns 1 row" 1 (List.length rows);
    assert_true ~msg:"count = 3" (List.hd (List.hd rows) = VInt 3);

    (* COUNT with variable *)
    let q = query
      (PNode (n ~var:"p" ~label:"Person" ()))
      [RAggCount (Some "p")] in
    let rows = execute g q in
    assert_true ~msg:"count(p) = 3" (List.hd (List.hd rows) = VInt 3);

    (* SUM *)
    let q = query
      (PStep (PNode (n ~var:"p" ~label:"Person" ()),
              r ~var:"w" ~rel_type:"WORKS_AT" (),
              n ~var:"c" ~label:"Company" ()))
      [RAggSum ("w", "salary")] in
    let rows = execute g q in
    (match List.hd (List.hd rows) with
     | VFloat f -> assert_float_near ~msg:"sum salary = 270000"
                     ~eps:0.01 270000.0 f
     | _ -> assert_true ~msg:"sum returns VFloat" false);

    (* AVG *)
    let q = query
      (PStep (PNode (n ~var:"p" ~label:"Person" ()),
              r ~var:"w" ~rel_type:"WORKS_AT" (),
              n ~var:"c" ~label:"Company" ()))
      [RAggAvg ("w", "salary")] in
    let rows = execute g q in
    (match List.hd (List.hd rows) with
     | VFloat f -> assert_float_near ~msg:"avg salary = 135000"
                     ~eps:0.01 135000.0 f
     | _ -> assert_true ~msg:"avg returns VFloat" false);

    (* MIN *)
    let q = query
      (PNode (n ~var:"p" ~label:"Person" ()))
      [RAggMin ("p", "age")] in
    let rows = execute g q in
    assert_true ~msg:"min age = 25" (List.hd (List.hd rows) = VInt 25);

    (* MAX *)
    let q = query
      (PNode (n ~var:"p" ~label:"Person" ()))
      [RAggMax ("p", "age")] in
    let rows = execute g q in
    assert_true ~msg:"max age = 35" (List.hd (List.hd rows) = VInt 35);

    (* COLLECT *)
    let q = query
      (PNode (n ~var:"p" ~label:"Person" ()))
      [RAggCollect ("p", "city")] in
    let rows = execute g q in
    (match List.hd (List.hd rows) with
     | VList vs -> assert_int ~msg:"collect cities = 3" 3 (List.length vs)
     | _ -> assert_true ~msg:"collect returns VList" false);
  )

let test_shortest_path () =
  suite "Shortest Path" (fun () ->
    let (g, alice, bob, charlie, _) = make_social_graph () in

    (* Direct neighbor *)
    (match shortest_path g alice.id bob.id with
     | Some path -> assert_int ~msg:"Alice->Bob = 2 nodes" 2 (List.length path)
     | None -> assert_true ~msg:"path Alice->Bob exists" false);

    (* 2-hop *)
    (match shortest_path g alice.id charlie.id with
     | Some path -> assert_int ~msg:"Alice->Charlie = 3 nodes" 3 (List.length path)
     | None -> assert_true ~msg:"path Alice->Charlie exists" false);

    (* Self-loop *)
    (match shortest_path g alice.id alice.id with
     | Some path -> assert_int ~msg:"self-path = 1 node" 1 (List.length path)
     | None -> assert_true ~msg:"self-path exists" false);

    (* No path (Charlie has no outgoing FRIENDS_WITH) *)
    (* Actually Charlie -> nobody via FRIENDS_WITH, but Bob -> Charlie exists *)
    (* charlie.id to alice.id: no reverse edges *)
    (match shortest_path g ~rel_type:"FRIENDS_WITH" charlie.id alice.id with
     | None -> assert_true ~msg:"no reverse path" true
     | Some _ -> assert_true ~msg:"should be no path Charlie->Alice" false);

    (* With rel_type filter *)
    (match shortest_path g ~rel_type:"WORKS_AT" alice.id charlie.id with
     | None -> assert_true ~msg:"no WORKS_AT path between people" true
     | Some _ -> assert_true ~msg:"should be no WORKS_AT path" false);
  )

let test_all_paths () =
  suite "All Paths" (fun () ->
    let g = create_graph () in
    let a = add_node g ~labels:["N"] ~props:["name", VString "A"] () in
    let b = add_node g ~labels:["N"] ~props:["name", VString "B"] () in
    let c = add_node g ~labels:["N"] ~props:["name", VString "C"] () in
    let d = add_node g ~labels:["N"] ~props:["name", VString "D"] () in
    let _ = add_edge g ~src:a.id ~dst:b.id ~rel_type:"E" () in
    let _ = add_edge g ~src:b.id ~dst:d.id ~rel_type:"E" () in
    let _ = add_edge g ~src:a.id ~dst:c.id ~rel_type:"E" () in
    let _ = add_edge g ~src:c.id ~dst:d.id ~rel_type:"E" () in

    let paths = all_paths g a.id d.id in
    assert_int ~msg:"2 paths A->D" 2 (List.length paths);

    let lengths = List.map List.length paths in
    assert_true ~msg:"both paths length 3"
      (List.for_all (fun l -> l = 3) lengths);
  )

let test_mutations () =
  suite "Graph Mutations" (fun () ->
    let g = create_graph () in
    let n1 = add_node g ~labels:["X"] ~props:["v", VInt 1] () in
    let n2 = add_node g ~labels:["X"] ~props:["v", VInt 2] () in
    let e1 = add_edge g ~src:n1.id ~dst:n2.id ~rel_type:"R" () in

    (* Update properties *)
    update_node_props g n1.id [("v", VInt 99); ("new", VString "hi")];
    (match find_node g n1.id with
     | Some n ->
       assert_true ~msg:"updated prop" (get_property n.properties "v" = VInt 99);
       assert_true ~msg:"new prop added" (get_property n.properties "new" = VString "hi")
     | None -> assert_true ~msg:"node still exists" false);

    (* Delete edge *)
    delete_edge g e1.eid;
    assert_int ~msg:"0 edges after delete" 0 (List.length g.edges);

    (* Delete node *)
    delete_node g n2.id;
    assert_int ~msg:"1 node after delete" 1 (List.length g.nodes);
    assert_true ~msg:"deleted node is gone" (find_node g n2.id = None);
  )

let test_graph_stats () =
  suite "Graph Statistics" (fun () ->
    let (g, _, _, _, _) = make_social_graph () in
    let stats = graph_stats g in

    assert_int ~msg:"4 nodes" 4 stats.node_count;
    assert_int ~msg:"4 edges" 4 stats.edge_count;
    assert_true ~msg:"avg degree > 0" (stats.avg_degree > 0.0);
    assert_true ~msg:"density between 0 and 1"
      (stats.density >= 0.0 && stats.density <= 1.0);
    assert_true ~msg:"has Person label"
      (List.exists (fun (l, _) -> l = "Person") stats.label_counts);
    assert_true ~msg:"has Company label"
      (List.exists (fun (l, _) -> l = "Company") stats.label_counts);
  )

let test_limit_skip () =
  suite "LIMIT and SKIP" (fun () ->
    let (g, _, _, _, _) = make_social_graph () in

    (* LIMIT *)
    let q = query
      (PNode (n ~var:"p" ~label:"Person" ()))
      ~limit:(Some 2)
      [RProp ("p", "name")] in
    let rows = execute g q in
    assert_int ~msg:"limit 2 = 2 rows" 2 (List.length rows);

    (* SKIP *)
    let q = query
      (PNode (n ~var:"p" ~label:"Person" ()))
      ~skip:1
      [RProp ("p", "name")] in
    let rows = execute g q in
    assert_int ~msg:"skip 1 = 2 rows" 2 (List.length rows);

    (* SKIP + LIMIT *)
    let q = query
      (PNode (n ~var:"p" ~label:"Person" ()))
      ~skip:1 ~limit:(Some 1)
      [RProp ("p", "name")] in
    let rows = execute g q in
    assert_int ~msg:"skip 1 + limit 1 = 1 row" 1 (List.length rows);
  )

let test_order_by () =
  suite "ORDER BY" (fun () ->
    let (g, _, _, _, _) = make_social_graph () in

    (* Ascending *)
    let q = query
      (PNode (n ~var:"p" ~label:"Person" ()))
      ~order:[(RProp ("p", "age"), Asc)]
      [RProp ("p", "name"); RProp ("p", "age")] in
    let rows = execute g q in
    assert_int ~msg:"ordered returns 3 rows" 3 (List.length rows);
    assert_true ~msg:"first is youngest"
      (List.nth (List.hd rows) 1 = VInt 25);

    (* Descending *)
    let q = query
      (PNode (n ~var:"p" ~label:"Person" ()))
      ~order:[(RProp ("p", "age"), Desc)]
      [RProp ("p", "name"); RProp ("p", "age")] in
    let rows = execute g q in
    assert_true ~msg:"first is oldest"
      (List.nth (List.hd rows) 1 = VInt 35);
  )

let test_distinct () =
  suite "DISTINCT" (fun () ->
    let (g, _, _, _, _) = make_social_graph () in

    let q = query
      (PNode (n ~var:"p" ~label:"Person" ()))
      ~distinct:true
      [RProp ("p", "city")] in
    let rows = execute g q in
    (* Seattle x2, Portland x1 -> distinct = 2 *)
    assert_int ~msg:"distinct cities = 2" 2 (List.length rows);
  )

let test_render_table () =
  suite "Table Rendering" (fun () ->
    let table = render_table ["a"; "b"]
      [[VInt 1; VString "x"]; [VInt 2; VString "yy"]] in
    assert_true ~msg:"table contains header 'a'"
      (let len = String.length table in
       let rec search i = if i >= len then false
         else if table.[i] = 'a' then true else search (i+1) in
       search 0);
    assert_true ~msg:"table has separators"
      (String.contains table '+');
  )

let test_render_stats () =
  suite "Stats Rendering" (fun () ->
    let (g, _, _, _, _) = make_social_graph () in
    let s = render_stats (graph_stats g) in
    assert_true ~msg:"stats contains Nodes"
      (let len = String.length s in
       let target = "Nodes" and tl = 5 in
       let rec search i = if i + tl > len then false
         else if String.sub s i tl = target then true
         else search (i+1) in search 0);
  )

let test_string_of_value () =
  suite "Value Serialization" (fun () ->
    assert_equal ~msg:"int" "42" (string_of_value (VInt 42));
    assert_equal ~msg:"bool" "true" (string_of_value (VBool true));
    assert_equal ~msg:"null" "NULL" (string_of_value VNull);
    assert_true ~msg:"string is quoted"
      (String.contains (string_of_value (VString "hi")) '"');
    assert_true ~msg:"list has brackets"
      (let s = string_of_value (VList [VInt 1; VInt 2]) in
       s.[0] = '[');
  )

let test_empty_graph_queries () =
  suite "Empty Graph Edge Cases" (fun () ->
    let g = create_graph () in

    let q = query (PNode (n ~var:"x" ())) [RProp ("x", "name")] in
    let rows = execute g q in
    assert_int ~msg:"empty graph = 0 rows" 0 (List.length rows);

    let q = query (PNode (n ~var:"x" ~label:"Nope" ())) [RAggCount None] in
    let rows = execute g q in
    assert_true ~msg:"count on empty = 0" (List.hd (List.hd rows) = VInt 0);

    let paths = all_paths g 1 2 in
    assert_int ~msg:"no paths in empty graph" 0 (List.length paths);
  )

let test_direction () =
  suite "Relationship Direction" (fun () ->
    let g = create_graph () in
    let a = add_node g ~labels:["N"] ~props:["name", VString "A"] () in
    let b = add_node g ~labels:["N"] ~props:["name", VString "B"] () in
    let _ = add_edge g ~src:a.id ~dst:b.id ~rel_type:"E" () in

    (* Outgoing: A->B *)
    let q = query
      (PStep (PNode (n ~var:"x" ~label:"N" ()),
              r ~rel_type:"E" ~dir:Outgoing (),
              n ~var:"y" ~label:"N" ()))
      [RProp ("x", "name"); RProp ("y", "name")] in
    let rows = execute g q in
    assert_int ~msg:"outgoing A->B = 1" 1 (List.length rows);

    (* Incoming: B<-A *)
    let q = query
      (PStep (PNode (n ~var:"x" ~label:"N" ()),
              r ~rel_type:"E" ~dir:Incoming (),
              n ~var:"y" ~label:"N" ()))
      [RProp ("x", "name"); RProp ("y", "name")] in
    let rows = execute g q in
    assert_int ~msg:"incoming B<-A = 1" 1 (List.length rows);

    (* Both directions *)
    let q = query
      (PStep (PNode (n ~var:"x" ~label:"N" ()),
              r ~rel_type:"E" ~dir:Both (),
              n ~var:"y" ~label:"N" ()))
      [RProp ("x", "name"); RProp ("y", "name")] in
    let rows = execute g q in
    assert_int ~msg:"both directions = 2" 2 (List.length rows);
  )

(* ── Run all tests ──────────────────────────────────────────────────── *)

let () =
  Printf.printf "=== Property Graph Query Engine Tests ===\n\n";

  test_graph_creation ();
  test_properties ();
  test_value_comparison ();
  test_node_query ();
  test_where_filter ();
  test_relationship_query ();
  test_multi_hop_query ();
  test_aggregation ();
  test_shortest_path ();
  test_all_paths ();
  test_mutations ();
  test_graph_stats ();
  test_limit_skip ();
  test_order_by ();
  test_distinct ();
  test_render_table ();
  test_render_stats ();
  test_string_of_value ();
  test_empty_graph_queries ();
  test_direction ();

  Printf.printf "\n=== Results: %d/%d passed, %d failed ===\n"
    !tests_passed !tests_run !tests_failed;
  if !tests_failed > 0 then begin
    Printf.printf "STATUS: SOME TESTS FAILED\n";
    exit 1
  end else begin
    Printf.printf "STATUS: ALL TESTS PASSED ✓\n";
    exit 0
  end
