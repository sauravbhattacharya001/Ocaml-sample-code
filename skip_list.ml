(* skip_list.ml — Probabilistic Skip List *)
(* A randomized data structure providing O(log n) expected-time     *)
(* search, insert, and delete in a sorted sequence. Each element    *)
(* is promoted to higher levels with probability 1/2, creating      *)
(* express lanes for binary-search–like traversal.                  *)
(* Supports: create, insert, mem, find, remove, size, is_empty,     *)
(* to_list, min_elt, max_elt, fold, iter, of_list, range_query,     *)
(* height, floor, ceil.                                             *)
(* Uses imperative nodes internally for authentic skip list         *)
(* behavior; public API is value-oriented.                          *)

module SkipList = struct

  let max_level = 32   (* maximum height of the skip list *)

  type 'a node = {
    key     : 'a;
    forward : 'a node option array;  (* forward[i] = next node at level i *)
  }

  type 'a t = {
    header    : 'a node;     (* sentinel head node *)
    mutable level : int;     (* current max level in use (0-indexed) *)
    mutable length : int;    (* number of elements *)
    compare   : 'a -> 'a -> int;
  }

  (* ---- Internal helpers ---- *)

  let make_node key lvl =
    { key; forward = Array.make (lvl + 1) None }

  let random_level () =
    let rec go lvl =
      if lvl >= max_level - 1 then lvl
      else if Random.bool () then go (lvl + 1)
      else lvl
    in
    go 0

  (* ---- Construction ---- *)

  (** [create ~compare] builds an empty skip list.
      [compare] must define a total order (like [Stdlib.compare]). *)
  let create ?(compare = Stdlib.compare) () =
    (* The header's key is never inspected — it's a sentinel. We use
       Obj.magic to avoid requiring a dummy value from the caller. *)
    let header = { key = Obj.magic 0; forward = Array.make max_level None } in
    { header; level = 0; length = 0; compare }

  (** [size sl] returns the number of elements. *)
  let size sl = sl.length

  (** [is_empty sl] returns [true] if the skip list has no elements. *)
  let is_empty sl = sl.length = 0

  (** [height sl] returns the current maximum level (1-indexed).
      An empty list has height 0. *)
  let height sl = if sl.length = 0 then 0 else sl.level + 1

  (* ---- Search ---- *)

  (** [mem key sl] returns [true] if [key] is in the skip list. *)
  let mem key sl =
    let x = ref sl.header in
    for i = sl.level downto 0 do
      let continue_ = ref true in
      while !continue_ do
        match !x.forward.(i) with
        | Some next when sl.compare next.key key < 0 ->
          x := next
        | _ -> continue_ := false
      done
    done;
    match !x.forward.(0) with
    | Some n -> sl.compare n.key key = 0
    | None   -> false

  (** [find key sl] returns [Some value] if [key] exists, [None] otherwise. *)
  let find key sl =
    let x = ref sl.header in
    for i = sl.level downto 0 do
      let continue_ = ref true in
      while !continue_ do
        match !x.forward.(i) with
        | Some next when sl.compare next.key key < 0 ->
          x := next
        | _ -> continue_ := false
      done
    done;
    match !x.forward.(0) with
    | Some n when sl.compare n.key key = 0 -> Some n.key
    | _ -> None

  (* ---- Insertion ---- *)

  (** [insert key sl] adds [key] to the skip list.
      If [key] already exists, the list is unchanged. *)
  let insert key sl =
    let update = Array.make max_level sl.header in
    let x = ref sl.header in
    for i = sl.level downto 0 do
      let continue_ = ref true in
      while !continue_ do
        match !x.forward.(i) with
        | Some next when sl.compare next.key key < 0 ->
          x := next
        | _ -> continue_ := false
      done;
      update.(i) <- !x
    done;
    (* Check for duplicate *)
    let is_dup = match !x.forward.(0) with
      | Some n -> sl.compare n.key key = 0
      | None   -> false
    in
    if not is_dup then begin
      let lvl = random_level () in
      if lvl > sl.level then begin
        for i = sl.level + 1 to lvl do
          update.(i) <- sl.header
        done;
        sl.level <- lvl
      end;
      let new_node = make_node key lvl in
      for i = 0 to lvl do
        new_node.forward.(i) <- update.(i).forward.(i);
        update.(i).forward.(i) <- Some new_node
      done;
      sl.length <- sl.length + 1
    end

  (* ---- Deletion ---- *)

  (** [remove key sl] removes [key] from the skip list.
      Returns [true] if the element was found and removed, [false] otherwise. *)
  let remove key sl =
    let update = Array.make max_level sl.header in
    let x = ref sl.header in
    for i = sl.level downto 0 do
      let continue_ = ref true in
      while !continue_ do
        match !x.forward.(i) with
        | Some next when sl.compare next.key key < 0 ->
          x := next
        | _ -> continue_ := false
      done;
      update.(i) <- !x
    done;
    match !x.forward.(0) with
    | Some n when sl.compare n.key key = 0 ->
      for i = 0 to sl.level do
        match update.(i).forward.(i) with
        | Some fwd when fwd == n ->
          update.(i).forward.(i) <- n.forward.(i)
        | _ -> ()
      done;
      (* Lower the level if top levels are now empty *)
      while sl.level > 0 && sl.header.forward.(sl.level) = None do
        sl.level <- sl.level - 1
      done;
      sl.length <- sl.length - 1;
      true
    | _ -> false

  (* ---- Traversal ---- *)

  (** [to_list sl] returns all elements in sorted order. *)
  let to_list sl =
    let acc = ref [] in
    let x = ref sl.header.forward.(0) in
    while !x <> None do
      (match !x with
       | Some n ->
         acc := n.key :: !acc;
         x := n.forward.(0)
       | None -> ())
    done;
    List.rev !acc

  (** [iter f sl] applies [f] to each element in sorted order. *)
  let iter f sl =
    let x = ref sl.header.forward.(0) in
    while !x <> None do
      (match !x with
       | Some n -> f n.key; x := n.forward.(0)
       | None -> ())
    done

  (** [fold f acc sl] folds [f] over elements in sorted order. *)
  let fold f acc sl =
    let result = ref acc in
    let x = ref sl.header.forward.(0) in
    while !x <> None do
      (match !x with
       | Some n -> result := f !result n.key; x := n.forward.(0)
       | None -> ())
    done;
    !result

  (** [min_elt sl] returns the smallest element, or [None] if empty. *)
  let min_elt sl =
    match sl.header.forward.(0) with
    | Some n -> Some n.key
    | None   -> None

  (** [max_elt sl] returns the largest element, or [None] if empty. *)
  let max_elt sl =
    if sl.length = 0 then None
    else begin
      let x = ref sl.header in
      for i = sl.level downto 0 do
        let continue_ = ref true in
        while !continue_ do
          match !x.forward.(i) with
          | Some next -> x := next
          | None -> continue_ := false
        done
      done;
      Some !x.key
    end

  (* ---- Range queries ---- *)

  (** [range_query ~lo ~hi sl] returns all elements [x] where
      [lo <= x <= hi] in sorted order. *)
  let range_query ~lo ~hi sl =
    if sl.compare lo hi > 0 then []
    else begin
      (* Find the first node >= lo *)
      let x = ref sl.header in
      for i = sl.level downto 0 do
        let continue_ = ref true in
        while !continue_ do
          match !x.forward.(i) with
          | Some next when sl.compare next.key lo < 0 ->
            x := next
          | _ -> continue_ := false
        done
      done;
      (* Collect from forward.(0) while <= hi *)
      let acc = ref [] in
      let cur = ref !x.forward.(0) in
      let stop = ref false in
      while not !stop do
        match !cur with
        | Some n when sl.compare n.key hi <= 0 ->
          if sl.compare n.key lo >= 0 then
            acc := n.key :: !acc;
          cur := n.forward.(0)
        | _ -> stop := true
      done;
      List.rev !acc
    end

  (** [floor key sl] returns the largest element [<= key], or [None]. *)
  let floor key sl =
    let x = ref sl.header in
    for i = sl.level downto 0 do
      let continue_ = ref true in
      while !continue_ do
        match !x.forward.(i) with
        | Some next when sl.compare next.key key <= 0 ->
          x := next
        | _ -> continue_ := false
      done
    done;
    if !x == sl.header then None
    else Some !x.key

  (** [ceil key sl] returns the smallest element [>= key], or [None]. *)
  let ceil key sl =
    let x = ref sl.header in
    for i = sl.level downto 0 do
      let continue_ = ref true in
      while !continue_ do
        match !x.forward.(i) with
        | Some next when sl.compare next.key key < 0 ->
          x := next
        | _ -> continue_ := false
      done
    done;
    match !x.forward.(0) with
    | Some n when sl.compare n.key key >= 0 -> Some n.key
    | _ -> None

  (** [of_list ~compare lst] builds a skip list from a list of elements. *)
  let of_list ?(compare = Stdlib.compare) lst =
    let sl = create ~compare () in
    List.iter (fun k -> insert k sl) lst;
    sl

end
