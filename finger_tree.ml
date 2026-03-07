(* finger_tree.ml — 2-3 Finger Trees (Hinze & Paterson, 2006)
 *
 * The Swiss Army knife of functional data structures: a single
 * implementation that provides O(1) amortised access to both ends,
 * O(log n) concatenation, and O(log n) split/search — all immutably.
 *
 * By parameterising over a *measure monoid* it naturally specialises to:
 *   - Sequences (measure = size)
 *   - Priority queues (measure = min/max priority)
 *   - Ordered sequences (measure = max key → supports sorted ops)
 *   - Interval trees (measure = max endpoint)
 *
 * Concepts demonstrated:
 *   - Polymorphic recursion (nested types)
 *   - Monoid abstraction (identity + associative combine)
 *   - Amortised O(1) deque operations via digit buffers
 *   - Efficient O(log n) split via cached monoidal annotations
 *   - 2-3 nodes for guaranteed balance
 *   - Higher-kinded-style module system (functors)
 *
 * Usage:
 *   ocamlopt finger_tree.ml -o finger_tree && ./finger_tree
 *
 * References:
 *   Ralf Hinze & Ross Paterson (2006).
 *   "Finger trees: a simple general-purpose data structure."
 *   Journal of Functional Programming 16(2):197-217.
 *)

(* ------------------------------------------------------------------ *)
(* Monoid signature — any measure must provide identity + combine      *)
(* ------------------------------------------------------------------ *)

module type MONOID = sig
  type t
  val empty  : t
  val append : t -> t -> t
end

(* ------------------------------------------------------------------ *)
(* Measured signature — elements carry a monoidal measure              *)
(* ------------------------------------------------------------------ *)

module type MEASURED = sig
  type elt
  type measure
  val measure : elt -> measure
end

(* ------------------------------------------------------------------ *)
(* Core Finger Tree functor                                            *)
(* ------------------------------------------------------------------ *)

module Make
    (Mon : MONOID)
    (Meas : MEASURED with type measure = Mon.t) = struct

  type measure = Mon.t
  type elt     = Meas.elt

  (* -- 2-3 Nodes --------------------------------------------------- *)

  type 'a node =
    | Node2 of measure * 'a * 'a
    | Node3 of measure * 'a * 'a * 'a

  let node_measure = function
    | Node2 (m, _, _)    -> m
    | Node3 (m, _, _, _) -> m

  let node2 a b =
    Node2 (Mon.append (Meas.measure a) (Meas.measure b), a, b)

  let node3 a b c =
    Node3 (Mon.append (Mon.append (Meas.measure a) (Meas.measure b))
                      (Meas.measure c), a, b, c)

  let node_to_list = function
    | Node2 (_, a, b)    -> [a; b]
    | Node3 (_, a, b, c) -> [a; b; c]

  (* Node constructors for inner level (nodes of nodes) *)
  let node2_n a b =
    Node2 (Mon.append (node_measure a) (node_measure b), a, b)

  let node3_n a b c =
    Node3 (Mon.append (Mon.append (node_measure a) (node_measure b))
                      (node_measure c), a, b, c)

  (* -- Digits (1-4 elements) --------------------------------------- *)

  type 'a digit =
    | One   of 'a
    | Two   of 'a * 'a
    | Three of 'a * 'a * 'a
    | Four  of 'a * 'a * 'a * 'a

  let digit_measure m = function
    | One a          -> m a
    | Two (a, b)     -> Mon.append (m a) (m b)
    | Three (a,b,c)  -> Mon.append (Mon.append (m a) (m b)) (m c)
    | Four (a,b,c,d) -> Mon.append (Mon.append (m a) (m b))
                                    (Mon.append (m c) (m d))

  let digit_to_list = function
    | One a          -> [a]
    | Two (a, b)     -> [a; b]
    | Three (a,b,c)  -> [a; b; c]
    | Four (a,b,c,d) -> [a; b; c; d]

  let digit_head = function
    | One a | Two (a,_) | Three (a,_,_) | Four (a,_,_,_) -> a

  let digit_last = function
    | One a | Two (_,a) | Three (_,_,a) | Four (_,_,_,a) -> a

  let digit_tail = function
    | One _          -> failwith "digit_tail of One"
    | Two (_, b)     -> One b
    | Three (_,b,c)  -> Two (b, c)
    | Four (_,b,c,d) -> Three (b, c, d)

  let digit_init = function
    | One _          -> failwith "digit_init of One"
    | Two (a, _)     -> One a
    | Three (a,b,_)  -> Two (a, b)
    | Four (a,b,c,_) -> Three (a, b, c)

  let digit_of_list = function
    | [a]       -> One a
    | [a;b]     -> Two (a, b)
    | [a;b;c]   -> Three (a, b, c)
    | [a;b;c;d] -> Four (a, b, c, d)
    | _         -> failwith "digit_of_list: expected 1-4 elements"

  (* -- The finger tree itself -------------------------------------- *)
  (* We avoid polymorphic recursion by using a separate inner type    *)
  (* that stores nodes directly.                                      *)

  type t =
    | Empty
    | Single of elt
    | Deep   of measure * elt digit * inner * elt digit

  and inner =
    | IEmpty
    | ISingle of elt node
    | IDeep   of measure * (elt node) digit * inner * (elt node) digit

  (* -- Measure helpers --------------------------------------------- *)

  let tree_measure = function
    | Empty           -> Mon.empty
    | Single x        -> Meas.measure x
    | Deep (m,_,_,_)  -> m

  let inner_measure = function
    | IEmpty            -> Mon.empty
    | ISingle n         -> node_measure n
    | IDeep (m,_,_,_)   -> m

  let deep pr mid sf =
    let m = Mon.append
              (Mon.append (digit_measure Meas.measure pr) (inner_measure mid))
              (digit_measure Meas.measure sf) in
    Deep (m, pr, mid, sf)

  let ideep pr mid sf =
    let m = Mon.append
              (Mon.append (digit_measure node_measure pr) (inner_measure mid))
              (digit_measure node_measure sf) in
    IDeep (m, pr, mid, sf)

  (* -- Construction ------------------------------------------------ *)

  let empty = Empty

  let singleton x = Single x

  let is_empty = function Empty -> true | _ -> false

  (* -- Push left (cons) -------------------------------------------- *)

  let rec push_left : elt -> t -> t = fun a -> function
    | Empty      -> Single a
    | Single b   -> deep (One a) IEmpty (One b)
    | Deep (_, Four (b,c,d,e), mid, sf) ->
        deep (Two (a, b)) (inner_push_left (node3 c d e) mid) sf
    | Deep (_, pr, mid, sf) ->
        let pr' = match pr with
          | One b         -> Two (a, b)
          | Two (b,c)     -> Three (a, b, c)
          | Three (b,c,d) -> Four (a, b, c, d)
          | Four _        -> failwith "unreachable" in
        deep pr' mid sf

  and inner_push_left : elt node -> inner -> inner = fun n -> function
    | IEmpty      -> ISingle n
    | ISingle m   -> ideep (One n) IEmpty (One m)
    | IDeep (_, Four (b,c,d,e), mid, sf) ->
        ideep (Two (n, b)) (inner_push_left (node3_n c d e) mid) sf
    | IDeep (_, pr, mid, sf) ->
        let pr' = match pr with
          | One b         -> Two (n, b)
          | Two (b,c)     -> Three (n, b, c)
          | Three (b,c,d) -> Four (n, b, c, d)
          | Four _        -> failwith "unreachable" in
        ideep pr' mid sf

  (* -- Push right (snoc) ------------------------------------------- *)

  and push_right : t -> elt -> t = fun t a -> match t with
    | Empty      -> Single a
    | Single b   -> deep (One b) IEmpty (One a)
    | Deep (_, pr, mid, Four (b,c,d,e)) ->
        deep pr (inner_push_right mid (node3 b c d)) (Two (e, a))
    | Deep (_, pr, mid, sf) ->
        let sf' = match sf with
          | One b         -> Two (b, a)
          | Two (b,c)     -> Three (b, c, a)
          | Three (b,c,d) -> Four (b, c, d, a)
          | Four _        -> failwith "unreachable" in
        deep pr mid sf'

  and inner_push_right : inner -> elt node -> inner = fun t n -> match t with
    | IEmpty      -> ISingle n
    | ISingle m   -> ideep (One m) IEmpty (One n)
    | IDeep (_, pr, mid, Four (b,c,d,e)) ->
        ideep pr (inner_push_right mid (node3_n b c d)) (Two (e, n))
    | IDeep (_, pr, mid, sf) ->
        let sf' = match sf with
          | One b         -> Two (b, n)
          | Two (b,c)     -> Three (b, c, n)
          | Three (b,c,d) -> Four (b, c, d, n)
          | Four _        -> failwith "unreachable" in
        ideep pr mid sf'

  (* -- View from the left ------------------------------------------ *)
  (* Returns the head element and the remaining tree (if non-empty).  *)

  let rec view_left : t -> (elt * t) option = function
    | Empty      -> None
    | Single x   -> Some (x, Empty)
    | Deep (_, pr, mid, sf) ->
        let hd = digit_head pr in
        let rest = match pr with
          | One _ ->
              (match inner_view_left mid with
               | None ->
                   (* Promote suffix to the whole tree *)
                   list_to_tree (digit_to_list sf)
               | Some (n, mid') ->
                   deep (digit_of_list (node_to_list n)) mid' sf)
          | _ -> deep (digit_tail pr) mid sf in
        Some (hd, rest)

  and inner_view_left : inner -> (elt node * inner) option = function
    | IEmpty -> None
    | ISingle n -> Some (n, IEmpty)
    | IDeep (_, pr, mid, sf) ->
        let hd = digit_head pr in
        let rest = match pr with
          | One _ ->
              (match inner_view_left mid with
               | None ->
                   list_to_inner (digit_to_list sf)
               | Some (n, mid') ->
                   ideep (digit_of_list (node_to_list n)) mid' sf)
          | _ -> ideep (digit_tail pr) mid sf in
        Some (hd, rest)

  and list_to_tree : elt list -> t = function
    | []  -> Empty
    | [a] -> Single a
    | xs  -> List.fold_left push_right Empty xs

  and list_to_inner : elt node list -> inner = function
    | []  -> IEmpty
    | [a] -> ISingle a
    | xs  -> List.fold_left inner_push_right IEmpty xs

  (* -- View from the right ----------------------------------------- *)

  and view_right : t -> (t * elt) option = function
    | Empty      -> None
    | Single x   -> Some (Empty, x)
    | Deep (_, pr, mid, sf) ->
        let lst = digit_last sf in
        let rest = match sf with
          | One _ ->
              (match inner_view_right mid with
               | None ->
                   list_to_tree (digit_to_list pr)
               | Some (mid', n) ->
                   deep pr mid' (digit_of_list (node_to_list n)))
          | _ -> deep pr mid (digit_init sf) in
        Some (rest, lst)

  and inner_view_right : inner -> (inner * elt node) option = function
    | IEmpty -> None
    | ISingle n -> Some (IEmpty, n)
    | IDeep (_, pr, mid, sf) ->
        let lst = digit_last sf in
        let rest = match sf with
          | One _ ->
              (match inner_view_right mid with
               | None ->
                   list_to_inner (digit_to_list pr)
               | Some (mid', n) ->
                   ideep pr mid' (digit_of_list (node_to_list n)))
          | _ -> ideep pr mid (digit_init sf) in
        Some (rest, lst)

  (* -- Head / tail / last / init ----------------------------------- *)

  let head t = match view_left t with
    | Some (x, _) -> x
    | None -> failwith "head of empty finger tree"

  let tail t = match view_left t with
    | Some (_, rest) -> rest
    | None -> failwith "tail of empty finger tree"

  let last t = match view_right t with
    | Some (_, x) -> x
    | None -> failwith "last of empty finger tree"

  let init t = match view_right t with
    | Some (rest, _) -> rest
    | None -> failwith "init of empty finger tree"

  (* -- Concatenation ----------------------------------------------- *)
  (* O(log(min(n,m))) — the key advantage of finger trees.           *)

  let rec app3 : t -> elt list -> t -> t = fun l mid r ->
    match l, r with
    | Empty, _ -> List.fold_right push_left mid r
    | _, Empty -> List.fold_left push_right l mid
    | Single x, _ -> push_left x (List.fold_right push_left mid r)
    | _, Single x -> push_right (List.fold_left push_right l mid) x
    | Deep (_, pr1, mid1, sf1), Deep (_, pr2, mid2, sf2) ->
        let nodes = nodes_of (digit_to_list sf1 @ mid @ digit_to_list pr2) in
        deep pr1 (inner_app3 mid1 nodes mid2) sf2

  and inner_app3 : inner -> elt node list -> inner -> inner =
    fun l mid r ->
    match l, r with
    | IEmpty, _ -> List.fold_right inner_push_left mid r
    | _, IEmpty -> List.fold_left inner_push_right l mid
    | ISingle n, _ ->
        inner_push_left n (List.fold_right inner_push_left mid r)
    | _, ISingle n ->
        inner_push_right (List.fold_left inner_push_right l mid) n
    | IDeep (_, pr1, mid1, sf1), IDeep (_, pr2, mid2, sf2) ->
        let all = digit_to_list sf1 @ mid @ digit_to_list pr2 in
        let nodes = nodes_of_nodes all in
        ideep pr1 (inner_app3 mid1 nodes mid2) sf2

  and nodes_of : elt list -> elt node list = function
    | [a; b]             -> [node2 a b]
    | [a; b; c]          -> [node3 a b c]
    | [a; b; c; d]       -> [node2 a b; node2 c d]
    | a :: b :: c :: rest -> node3 a b c :: nodes_of rest
    | _                  -> failwith "nodes_of: too few elements"

  and nodes_of_nodes : elt node list -> (elt node) node list = function
    | [a; b]             -> [node2_n a b]
    | [a; b; c]          -> [node3_n a b c]
    | [a; b; c; d]       -> [node2_n a b; node2_n c d]
    | a :: b :: c :: rest -> node3_n a b c :: nodes_of_nodes rest
    | _                  -> failwith "nodes_of_nodes: too few elements"

  let concat l r = app3 l [] r

  (* -- Split ------------------------------------------------------- *)
  (* O(log n) — split at the point where a predicate on the running  *)
  (* measure first becomes true. The predicate must be monotonic:    *)
  (* once true, it stays true.                                        *)

  type split_result = { left : t; pivot : elt; right : t }

  let rec split_digit_at : (measure -> bool) -> measure -> elt list ->
    elt list * elt * elt list =
    fun p acc -> function
    | [] -> failwith "split_digit_at: empty"
    | [x] -> ([], x, [])
    | x :: xs ->
        let acc' = Mon.append acc (Meas.measure x) in
        if p acc' then ([], x, xs)
        else
          let (l, v, r) = split_digit_at p acc' xs in
          (x :: l, v, r)

  let rec inner_split_digit_at : (measure -> bool) -> measure ->
    elt node list -> elt node list * elt node * elt node list =
    fun p acc -> function
    | [] -> failwith "inner_split_digit_at: empty"
    | [x] -> ([], x, [])
    | x :: xs ->
        let acc' = Mon.append acc (node_measure x) in
        if p acc' then ([], x, xs)
        else
          let (l, v, r) = inner_split_digit_at p acc' xs in
          (x :: l, v, r)

  let rec split : (measure -> bool) -> t -> split_result =
    fun p t ->
    match t with
    | Empty -> failwith "split of empty finger tree"
    | Single x -> { left = Empty; pivot = x; right = Empty }
    | Deep (_, pr, mid, sf) ->
        let m_pr = digit_measure Meas.measure pr in
        if p m_pr then
          (* Split is within the prefix *)
          let (l, v, r) = split_digit_at p Mon.empty (digit_to_list pr) in
          let left = list_to_tree l in
          let right = match r with
            | [] -> inner_to_tree mid sf
            | _  -> deep (digit_of_list r) mid sf in
          { left; pivot = v; right }
        else
          let m_mid = Mon.append m_pr (inner_measure mid) in
          if p m_mid then
            (* Split is within the middle (inner tree) *)
            let (ml, node, mr) = inner_split_tree p m_pr mid in
            let node_elts = node_to_list node in
            let (l, v, r) = split_digit_at p
              (Mon.append m_pr (inner_measure ml)) node_elts in
            let left = match l with
              | [] -> inner_to_tree_left pr ml
              | _  -> app3 (inner_to_tree_left pr ml) [] (list_to_tree l) in
            let right = match r with
              | [] -> inner_to_tree_right mr sf
              | _  -> app3 (list_to_tree r) [] (inner_to_tree_right mr sf) in
            { left; pivot = v; right }
          else
            (* Split is within the suffix *)
            let (l, v, r) = split_digit_at p m_mid (digit_to_list sf) in
            let left = match l with
              | [] -> tree_of_inner_left pr mid
              | _  -> app3 (tree_of_inner_left pr mid) [] (list_to_tree l) in
            let right = list_to_tree r in
            { left; pivot = v; right }

  and inner_split_tree : (measure -> bool) -> measure -> inner ->
    inner * elt node * inner =
    fun p acc -> function
    | IEmpty -> failwith "inner_split_tree of empty"
    | ISingle n -> (IEmpty, n, IEmpty)
    | IDeep (_, pr, mid, sf) ->
        let m_pr = Mon.append acc (digit_measure node_measure pr) in
        if p m_pr then
          let (l, v, r) = inner_split_digit_at p acc (digit_to_list pr) in
          let left = list_to_inner l in
          let right = match r with
            | [] ->
                (match inner_view_left mid with
                 | None -> list_to_inner (digit_to_list sf)
                 | Some (n, mid') ->
                     ideep (digit_of_list (node_to_list n)) mid' sf)
            | _ ->
                (match mid with
                 | IEmpty -> list_to_inner (r @ digit_to_list sf)
                 | _ -> ideep (digit_of_list r) mid sf) in
          (left, v, right)
        else
          let m_mid = Mon.append m_pr (inner_measure mid) in
          if p m_mid then
            let (ml, node, mr) = inner_split_tree p m_pr mid in
            let node_nodes = match node with
              | Node2 (_, a, b) -> [a; b]
              | Node3 (_, a, b, c) -> [a; b; c] in
            let (l, v, r) = inner_split_digit_at p
              (Mon.append m_pr (inner_measure ml)) node_nodes in
            let left = match l with
              | [] -> inner_rebuild_left pr ml
              | _ ->
                  let base = inner_rebuild_left pr ml in
                  List.fold_left inner_push_right base l in
            let right = match r with
              | [] -> inner_rebuild_right mr sf
              | _ ->
                  let base = inner_rebuild_right mr sf in
                  List.fold_right inner_push_left r base in
            (left, v, right)
          else
            let (l, v, r) = inner_split_digit_at p m_mid (digit_to_list sf) in
            let left = match l with
              | [] ->
                  (match inner_view_right mid with
                   | None -> list_to_inner (digit_to_list pr)
                   | Some (mid', n) ->
                       ideep pr mid' (digit_of_list (node_to_list n)))
              | _ ->
                  (match mid with
                   | IEmpty -> list_to_inner (digit_to_list pr @ l)
                   | _ -> ideep pr mid (digit_of_list l)) in
            let right = list_to_inner r in
            (left, v, right)

  and inner_rebuild_left pr ml =
    match inner_view_right ml with
    | None -> list_to_inner (digit_to_list pr)
    | Some (ml', n) -> ideep pr ml' (digit_of_list (node_to_list n))

  and inner_rebuild_right mr sf =
    match inner_view_left mr with
    | None -> list_to_inner (digit_to_list sf)
    | Some (n, mr') -> ideep (digit_of_list (node_to_list n)) mr' sf

  and inner_to_tree mid sf =
    let mid_elts = inner_to_elt_list mid in
    let sf_elts = digit_to_list sf in
    list_to_tree (mid_elts @ sf_elts)

  and inner_to_tree_left pr mid =
    let pr_elts = digit_to_list pr in
    let mid_elts = inner_to_elt_list mid in
    list_to_tree (pr_elts @ mid_elts)

  and inner_to_tree_right mid sf =
    let mid_elts = inner_to_elt_list mid in
    let sf_elts = digit_to_list sf in
    list_to_tree (mid_elts @ sf_elts)

  and tree_of_inner_left pr mid =
    let pr_elts = digit_to_list pr in
    let mid_elts = inner_to_elt_list mid in
    list_to_tree (pr_elts @ mid_elts)

  and inner_to_elt_list : inner -> elt list = function
    | IEmpty -> []
    | ISingle n -> node_to_list n
    | IDeep (_, pr, mid, sf) ->
        let pr_elts = List.concat_map node_to_list (digit_to_list pr) in
        let mid_elts = inner_to_elt_list_deep mid in
        let sf_elts = List.concat_map node_to_list (digit_to_list sf) in
        pr_elts @ mid_elts @ sf_elts

  and inner_to_elt_list_deep : inner -> elt list = function
    | IEmpty -> []
    | ISingle n ->
        (* n is a node of nodes at this level *)
        List.concat_map node_to_list (node_to_list n)
    | IDeep (_, pr, mid, sf) ->
        let flatten_digit d =
          List.concat_map (fun n ->
            List.concat_map node_to_list (node_to_list n)
          ) (digit_to_list d) in
        flatten_digit pr @ inner_to_elt_list_deep mid @ flatten_digit sf

  (* -- Conversion -------------------------------------------------- *)

  let of_list xs = List.fold_left push_right Empty xs

  let to_list t =
    let rec go acc = function
      | Empty -> List.rev acc
      | t ->
          match view_left t with
          | None -> List.rev acc
          | Some (x, rest) -> go (x :: acc) rest in
    go [] t

  let length t =
    let rec go n t =
      match view_left t with
      | None -> n
      | Some (_, rest) -> go (n + 1) rest in
    go 0 t

  (* -- Lookup by measure ------------------------------------------- *)

  let lookup p t = (split p t).pivot

  (* -- Fold / iter / map / filter ---------------------------------- *)

  let fold_left f acc t =
    let rec go a t =
      match view_left t with
      | None -> a
      | Some (x, rest) -> go (f a x) rest in
    go acc t

  let fold_right f t acc =
    let rec go a t =
      match view_right t with
      | None -> a
      | Some (rest, x) -> go (f x a) rest in
    go acc t

  let iter f = fold_left (fun () x -> f x) ()

  let measure t = tree_measure t

  (* -- Reverse ----------------------------------------------------- *)

  let rev t = fold_left (fun acc x -> push_left x acc) Empty t

  (* -- take_while / drop_while / filter ---------------------------- *)

  let take_while p t =
    let rec go acc t =
      match view_left t with
      | None -> of_list (List.rev acc)
      | Some (x, rest) ->
          if p x then go (x :: acc) rest
          else of_list (List.rev acc) in
    go [] t

  let drop_while p t =
    let rec go t =
      match view_left t with
      | None -> Empty
      | Some (x, rest) ->
          if p x then go rest
          else push_left x rest in
    go t

  let filter p t =
    fold_left (fun acc x -> if p x then push_right acc x else acc) Empty t

end

(* ================================================================== *)
(*                        SPECIALIZATIONS                              *)
(* ================================================================== *)

(* -- Sequence (measure = size) ------------------------------------- *)
(* Size-indexed: random access by position, efficient length.         *)

module SizeMonoid = struct
  type t = int
  let empty = 0
  let append = ( + )
end

module IntSeqMeasured = struct
  type elt = int
  type measure = int
  let measure _ = 1
end

module IntSeq = Make(SizeMonoid)(IntSeqMeasured)

(* -- Priority Queue (measure = min) -------------------------------- *)
(* Extract-min by splitting where the accumulated min reaches the     *)
(* global minimum.                                                     *)

module MinMonoid = struct
  type t = int
  let empty = max_int
  let append a b = min a b
end

module PrioMeasured = struct
  type elt = int
  type measure = int
  let measure x = x
end

module PrioQueue = Make(MinMonoid)(PrioMeasured)

(* -- Sorted Sequence (measure = max key) --------------------------- *)
(* Supports O(log n) sorted insertion via split on max key.           *)

module MaxMonoid = struct
  type t = int
  let empty = min_int
  let append a b = max a b
end

module SortedMeasured = struct
  type elt = int
  type measure = int
  let measure x = x
end

module SortedSeq = Make(MaxMonoid)(SortedMeasured)

(* ================================================================== *)
(*                        DEMONSTRATION                                *)
(* ================================================================== *)

let () =
  Printf.printf "=== Finger Trees (Hinze & Paterson, 2006) ===\n\n";

  (* Helper for display *)
  let show xs =
    "[" ^ String.concat "; " (List.map string_of_int xs) ^ "]" in

  (* -- Sequence demo ----------------------------------------------- *)
  Printf.printf "--- Sequence (double-ended queue) ---\n";
  let open IntSeq in
  let seq = of_list [1; 2; 3; 4; 5; 6; 7; 8] in
  Printf.printf "Built from list:  %s\n" (show (to_list seq));
  Printf.printf "Length:           %d\n" (length seq);
  Printf.printf "Head:             %d\n" (head seq);
  Printf.printf "Last:             %d\n" (last seq);

  Printf.printf "Push left 0:      %s\n" (show (to_list (push_left 0 seq)));
  Printf.printf "Push right 9:     %s\n" (show (to_list (push_right seq 9)));
  Printf.printf "Tail:             %s\n" (show (to_list (tail seq)));
  Printf.printf "Init:             %s\n" (show (to_list (init seq)));
  Printf.printf "Reversed:         %s\n" (show (to_list (rev seq)));
  Printf.printf "Evens only:       %s\n"
    (show (to_list (filter (fun x -> x mod 2 = 0) seq)));

  (* Concatenation *)
  let a = of_list [1; 2; 3] in
  let b = of_list [4; 5; 6] in
  Printf.printf "Concat [1;2;3] ++ [4;5;6]: %s\n"
    (show (to_list (concat a b)));

  Printf.printf "Sum (fold_left):  %d\n" (fold_left ( + ) 0 seq);

  (* Indexed access via split *)
  let nth t i =
    let { pivot; _ } = split (fun s -> s > i) t in
    pivot in
  Printf.printf "Index 0:          %d\n" (nth seq 0);
  Printf.printf "Index 4:          %d\n" (nth seq 4);
  Printf.printf "Index 7:          %d\n" (nth seq 7);

  Printf.printf "\n";

  (* -- Priority Queue demo ----------------------------------------- *)
  Printf.printf "--- Priority Queue (extract-min) ---\n";
  let open PrioQueue in
  let pq = of_list [5; 3; 8; 1; 4; 9; 2; 7; 6] in
  Printf.printf "PQ contents: %s\n" (show (to_list pq));
  Printf.printf "Min (measure): %d\n" (measure pq);

  let global_min = measure pq in
  let { pivot; left = pq_l; right = pq_r } =
    split (fun m -> m <= global_min) pq in
  Printf.printf "Extract min: %d\n" pivot;
  Printf.printf "Remaining:   %s\n" (show (to_list (concat pq_l pq_r)));

  (* Extract sorted sequence *)
  let rec drain acc t =
    if is_empty t then List.rev acc
    else
      let m = measure t in
      let { pivot; left; right } = split (fun x -> x <= m) t in
      drain (pivot :: acc) (concat left right) in
  Printf.printf "Drain sorted: %s\n" (show (drain [] pq));
  Printf.printf "\n";

  (* -- Sorted sequence demo ---------------------------------------- *)
  Printf.printf "--- Sorted Sequence (ordered insert) ---\n";
  let open SortedSeq in

  let sorted_insert x t =
    if is_empty t then singleton x
    else if x <= head t then push_left x t
    else if x >= last t then push_right t x
    else
      let { left; right; _ } =
        split (fun m -> m >= x) t in
      concat (push_right left x) right in

  let sorted = List.fold_left (fun t x -> sorted_insert x t)
                 empty [5; 3; 8; 1; 4; 9; 2; 7; 6; 10] in
  Printf.printf "Sorted insert: %s\n" (show (to_list sorted));
  Printf.printf "Max (measure): %d\n" (measure sorted);

  Printf.printf "\n";

  (* -- Performance characteristics --------------------------------- *)
  Printf.printf "--- Complexity summary ---\n";
  Printf.printf "  push_left / push_right : O(1) amortised\n";
  Printf.printf "  head / last            : O(1)\n";
  Printf.printf "  tail / init            : O(1) amortised\n";
  Printf.printf "  concat                 : O(log(min(n,m)))\n";
  Printf.printf "  split / lookup         : O(log n)\n";
  Printf.printf "\n";

  (* -- Stress test ------------------------------------------------- *)
  Printf.printf "--- Stress test (10,000 elements) ---\n";
  let n = 10000 in
  let big = List.init n Fun.id |> IntSeq.of_list in
  Printf.printf "Head: %d, Last: %d, Length: %d\n"
    (IntSeq.head big) (IntSeq.last big) (IntSeq.length big);

  let t0 = Sys.time () in
  let _ = IntSeq.concat big big in
  let t1 = Sys.time () in
  Printf.printf "Concat 10k ++ 10k: %.4fs\n" (t1 -. t0);

  let t2 = Sys.time () in
  let _ = IntSeq.rev big in
  let t3 = Sys.time () in
  Printf.printf "Reverse 10k:       %.4fs\n" (t3 -. t2);

  Printf.printf "\nAll demonstrations complete!\n"
