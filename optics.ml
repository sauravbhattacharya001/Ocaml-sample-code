(* =============================================================================
   Optics: Lenses, Prisms, and Traversals in OCaml
   =============================================================================
   Functional optics for composable, immutable data access and modification.
   
   Covers:
   - Lenses: focus on a product field (get + set)
   - Prisms: focus on a sum variant (preview + build)
   - Traversals: focus on zero-or-more targets (fold + over)
   - Optional: focus on zero-or-one target
   - Iso: bidirectional conversion (isomorphisms)
   - Composition: all optics compose with (|>>) operator
   
   Usage: ocamlfind ocamlopt -package alcotest -linkpkg optics.ml -o optics && ./optics
          (or simply: ocamlfind ocamlopt optics.ml -o optics && ./optics)
   ============================================================================= *)

(* ---------------------------------------------------------------------------
   Core optic types
   --------------------------------------------------------------------------- *)

(** A lens focuses on exactly one field in a product type *)
type ('s, 'a) lens = {
  get : 's -> 'a;
  set : 'a -> 's -> 's;
}

(** A prism focuses on one variant in a sum type *)
type ('s, 'a) prism = {
  preview : 's -> 'a option;
  build   : 'a -> 's;
}

(** An optional focuses on zero-or-one target *)
type ('s, 'a) optional = {
  get_opt : 's -> 'a option;
  set_opt : 'a -> 's -> 's;
}

(** A traversal focuses on zero-or-more targets *)
type ('s, 'a) traversal = {
  fold : ('a -> 'b -> 'b) -> 'b -> 's -> 'b;
  over : ('a -> 'a) -> 's -> 's;
}

(** An iso is a bidirectional, lossless conversion *)
type ('s, 'a) iso = {
  forward  : 's -> 'a;
  backward : 'a -> 's;
}

(* ---------------------------------------------------------------------------
   Lens operations
   --------------------------------------------------------------------------- *)

module Lens = struct
  let make ~get ~set = { get; set }

  (** Modify via a function *)
  let over (l : ('s, 'a) lens) (f : 'a -> 'a) (s : 's) : 's =
    l.set (f (l.get s)) s

  (** Compose two lenses: outer then inner *)
  let compose (outer : ('s, 'a) lens) (inner : ('a, 'b) lens) : ('s, 'b) lens =
    { get = (fun s -> inner.get (outer.get s));
      set = (fun b s -> outer.set (inner.set b (outer.get s)) s);
    }

  (** Infix composition operator *)
  let ( |>> ) = compose

  (** Convert a lens to an optional *)
  let to_optional (l : ('s, 'a) lens) : ('s, 'a) optional =
    { get_opt = (fun s -> Some (l.get s));
      set_opt = (fun a s -> l.set a s);
    }

  (** Convert a lens to a traversal *)
  let to_traversal (l : ('s, 'a) lens) : ('s, 'a) traversal =
    { fold = (fun f z s -> f (l.get s) z);
      over = (fun f s -> l.set (f (l.get s)) s);
    }
end

(* ---------------------------------------------------------------------------
   Prism operations
   --------------------------------------------------------------------------- *)

module Prism = struct
  let make ~preview ~build = { preview; build }

  (** Modify target if present *)
  let over (p : ('s, 'a) prism) (f : 'a -> 'a) (s : 's) : 's =
    match p.preview s with
    | Some a -> p.build (f a)
    | None   -> s

  (** Check if prism matches *)
  let is (p : ('s, 'a) prism) (s : 's) : bool =
    Option.is_some (p.preview s)

  (** Compose two prisms *)
  let compose (outer : ('s, 'a) prism) (inner : ('a, 'b) prism) : ('s, 'b) prism =
    { preview = (fun s ->
        match outer.preview s with
        | Some a -> inner.preview a
        | None   -> None);
      build = (fun b -> outer.build (inner.build b));
    }

  let ( |>> ) = compose

  (** Convert a prism to an optional *)
  let to_optional (p : ('s, 'a) prism) : ('s, 'a) optional =
    { get_opt = p.preview;
      set_opt = (fun a s ->
        match p.preview s with
        | Some _ -> p.build a
        | None   -> s);
    }

  (** Convert a prism to a traversal *)
  let to_traversal (p : ('s, 'a) prism) : ('s, 'a) traversal =
    { fold = (fun f z s ->
        match p.preview s with
        | Some a -> f a z
        | None   -> z);
      over = over p;
    }
end

(* ---------------------------------------------------------------------------
   Optional operations
   --------------------------------------------------------------------------- *)

module Optional = struct
  let make ~get_opt ~set_opt = { get_opt; set_opt }

  let over (o : ('s, 'a) optional) (f : 'a -> 'a) (s : 's) : 's =
    match o.get_opt s with
    | Some a -> o.set_opt (f a) s
    | None   -> s

  let compose (outer : ('s, 'a) optional) (inner : ('a, 'b) optional) : ('s, 'b) optional =
    { get_opt = (fun s ->
        match outer.get_opt s with
        | Some a -> inner.get_opt a
        | None   -> None);
      set_opt = (fun b s ->
        match outer.get_opt s with
        | Some a -> outer.set_opt (inner.set_opt b a) s
        | None   -> s);
    }

  let ( |>> ) = compose
end

(* ---------------------------------------------------------------------------
   Traversal operations
   --------------------------------------------------------------------------- *)

module Traversal = struct
  let make ~fold ~over = { fold; over }

  (** Collect all targets into a list *)
  let to_list (t : ('s, 'a) traversal) (s : 's) : 'a list =
    List.rev (t.fold (fun a acc -> a :: acc) [] s)

  (** Count targets *)
  let length (t : ('s, 'a) traversal) (s : 's) : int =
    t.fold (fun _ n -> n + 1) 0 s

  (** Check if any target satisfies predicate *)
  let exists (t : ('s, 'a) traversal) (pred : 'a -> bool) (s : 's) : bool =
    t.fold (fun a found -> found || pred a) false s

  (** Check if all targets satisfy predicate *)
  let for_all (t : ('s, 'a) traversal) (pred : 'a -> bool) (s : 's) : bool =
    t.fold (fun a ok -> ok && pred a) true s

  (** Compose two traversals *)
  let compose (outer : ('s, 'a) traversal) (inner : ('a, 'b) traversal) : ('s, 'b) traversal =
    { fold = (fun f z s -> outer.fold (fun a z' -> inner.fold f z' a) z s);
      over = (fun f s -> outer.over (inner.over f) s);
    }

  let ( |>> ) = compose

  (** Traversal over list elements *)
  let each : ('a list, 'a) traversal =
    { fold = (fun f z xs -> List.fold_left (fun acc x -> f x acc) z xs);
      over = List.map;
    }

  (** Traversal that filters by predicate *)
  let filtered (pred : 'a -> bool) : ('a list, 'a) traversal =
    { fold = (fun f z xs ->
        List.fold_left (fun acc x -> if pred x then f x acc else acc) z xs);
      over = (fun g xs -> List.map (fun x -> if pred x then g x else x) xs);
    }
end

(* ---------------------------------------------------------------------------
   Iso operations
   --------------------------------------------------------------------------- *)

module Iso = struct
  let make ~forward ~backward = { forward; backward }

  (** Reverse an iso *)
  let reverse (i : ('s, 'a) iso) : ('a, 's) iso =
    { forward = i.backward; backward = i.forward }

  (** Compose two isos *)
  let compose (outer : ('s, 'a) iso) (inner : ('a, 'b) iso) : ('s, 'b) iso =
    { forward = (fun s -> inner.forward (outer.forward s));
      backward = (fun b -> outer.backward (inner.backward b));
    }

  let ( |>> ) = compose

  (** Convert an iso to a lens *)
  let to_lens (i : ('s, 'a) iso) : ('s, 'a) lens =
    { get = i.forward;
      set = (fun a _ -> i.backward a);
    }

  (** Convert an iso to a prism (always matches) *)
  let to_prism (i : ('s, 'a) iso) : ('s, 'a) prism =
    { preview = (fun s -> Some (i.forward s));
      build = i.backward;
    }
end

(* ---------------------------------------------------------------------------
   Example domain: nested records
   --------------------------------------------------------------------------- *)

type address = {
  street : string;
  city   : string;
  zip    : string;
}

type person = {
  name    : string;
  age     : int;
  address : address;
}

type company = {
  company_name : string;
  ceo          : person;
  employees    : person list;
}

(* Lenses for address *)
let address_street : (address, string) lens =
  Lens.make
    ~get:(fun a -> a.street)
    ~set:(fun s a -> { a with street = s })

let address_city : (address, string) lens =
  Lens.make
    ~get:(fun a -> a.city)
    ~set:(fun c a -> { a with city = c })

let address_zip : (address, string) lens =
  Lens.make
    ~get:(fun a -> a.zip)
    ~set:(fun z a -> { a with zip = z })

(* Lenses for person *)
let person_name : (person, string) lens =
  Lens.make
    ~get:(fun p -> p.name)
    ~set:(fun n p -> { p with name = n })

let person_age : (person, int) lens =
  Lens.make
    ~get:(fun p -> p.age)
    ~set:(fun a p -> { p with age = a })

let person_address : (person, address) lens =
  Lens.make
    ~get:(fun p -> p.address)
    ~set:(fun a p -> { p with address = a })

(* Lenses for company *)
let company_ceo : (company, person) lens =
  Lens.make
    ~get:(fun c -> c.ceo)
    ~set:(fun p c -> { c with ceo = p })

let company_employees : (company, person list) lens =
  Lens.make
    ~get:(fun c -> c.employees)
    ~set:(fun es c -> { c with employees = es })

(* Composed lenses *)
let ceo_city = Lens.(company_ceo |>> person_address |>> address_city)
let ceo_street = Lens.(company_ceo |>> person_address |>> address_street)

(* ---------------------------------------------------------------------------
   Example domain: sum types for prisms
   --------------------------------------------------------------------------- *)

type shape =
  | Circle    of float
  | Rectangle of float * float
  | Triangle  of float * float * float

let _circle : (shape, float) prism =
  Prism.make
    ~preview:(function Circle r -> Some r | _ -> None)
    ~build:(fun r -> Circle r)

let _rectangle : (shape, float * float) prism =
  Prism.make
    ~preview:(function Rectangle (w, h) -> Some (w, h) | _ -> None)
    ~build:(fun (w, h) -> Rectangle (w, h))

let _triangle : (shape, float * float * float) prism =
  Prism.make
    ~preview:(function Triangle (a, b, c) -> Some (a, b, c) | _ -> None)
    ~build:(fun (a, b, c) -> Triangle (a, b, c))

(* ---------------------------------------------------------------------------
   Example: Isos
   --------------------------------------------------------------------------- *)

let celsius_fahrenheit : (float, float) iso =
  Iso.make
    ~forward:(fun c -> c *. 9.0 /. 5.0 +. 32.0)
    ~backward:(fun f -> (f -. 32.0) *. 5.0 /. 9.0)

let string_chars : (string, char list) iso =
  Iso.make
    ~forward:(fun s -> List.init (String.length s) (String.get s))
    ~backward:(fun cs -> String.init (List.length cs) (List.nth cs))

(* ---------------------------------------------------------------------------
   Tests
   --------------------------------------------------------------------------- *)

let () =
  let pass = ref 0 in
  let fail = ref 0 in
  let total = ref 0 in
  let check name cond =
    incr total;
    if cond then (
      incr pass;
      Printf.printf "  ✓ %s\n" name
    ) else (
      incr fail;
      Printf.printf "  ✗ FAIL: %s\n" name
    )
  in
  let feq a b = Float.abs (a -. b) < 1e-9 in

  Printf.printf "\n=== Optics: Lenses, Prisms, and Traversals ===\n\n";

  (* --- Lens tests --- *)
  Printf.printf "── Lens ──\n";

  let addr = { street = "123 Main St"; city = "Springfield"; zip = "62704" } in
  let bob = { name = "Bob"; age = 30; address = addr } in
  let acme = {
    company_name = "Acme";
    ceo = bob;
    employees = [
      { name = "Alice"; age = 25; address = { street = "1 Elm"; city = "Portland"; zip = "97201" } };
      { name = "Carol"; age = 35; address = { street = "2 Oak"; city = "Seattle"; zip = "98101" } };
    ];
  } in

  check "get street" (address_street.get addr = "123 Main St");
  check "set street" ((address_street.set "456 Oak Ave" addr).street = "456 Oak Ave");
  check "set preserves other fields" ((address_street.set "x" addr).city = "Springfield");
  check "over lens" (Lens.over person_age (fun a -> a + 1) bob).age = 31;
  check "composed get: ceo city" (ceo_city.get acme = "Springfield");
  check "composed set: ceo city" ((ceo_city.set "Austin" acme).ceo.address.city = "Austin");
  check "deep compose: ceo street" (ceo_street.get acme = "123 Main St");
  check "deep compose set preserves" ((ceo_street.set "X" acme).ceo.name = "Bob");
  check "lens to_optional" (Option.get ((Lens.to_optional person_name).get_opt bob) = "Bob");
  check "lens to_traversal" (
    Traversal.to_list (Lens.to_traversal person_name) bob = ["Bob"]);

  (* --- Prism tests --- *)
  Printf.printf "\n── Prism ──\n";

  let c = Circle 5.0 in
  let r = Rectangle (3.0, 4.0) in
  let t = Triangle (3.0, 4.0, 5.0) in

  check "preview match" (_circle.preview c = Some 5.0);
  check "preview no match" (_circle.preview r = None);
  check "build" (_circle.build 10.0 = Circle 10.0);
  check "over match" (Prism.over _circle (fun r -> r *. 2.0) c = Circle 10.0);
  check "over no match" (Prism.over _circle (fun r -> r *. 2.0) r = Rectangle (3.0, 4.0));
  check "is true" (Prism.is _circle c = true);
  check "is false" (Prism.is _rectangle c = false);
  check "rectangle preview" (_rectangle.preview r = Some (3.0, 4.0));
  check "triangle preview" (_triangle.preview t = Some (3.0, 4.0, 5.0));
  check "prism to_optional" (
    let o = Prism.to_optional _circle in
    o.get_opt c = Some 5.0 && o.get_opt r = None);
  check "prism to_traversal" (
    Traversal.to_list (Prism.to_traversal _circle) c = [5.0] &&
    Traversal.to_list (Prism.to_traversal _circle) r = []);

  (* --- Optional tests --- *)
  Printf.printf "\n── Optional ──\n";

  let list_head : ('a list, 'a) optional =
    Optional.make
      ~get_opt:(function x :: _ -> Some x | [] -> None)
      ~set_opt:(fun a -> function _ :: rest -> a :: rest | [] -> [])
  in
  check "optional get some" (list_head.get_opt [1;2;3] = Some 1);
  check "optional get none" (list_head.get_opt [] = None);
  check "optional set" (list_head.set_opt 10 [1;2;3] = [10;2;3]);
  check "optional set empty" (list_head.set_opt 10 [] = []);
  check "optional over" (Optional.over list_head (fun x -> x * 100) [5;6] = [500;6]);
  check "optional over empty" (Optional.over list_head (fun x -> x * 100) [] = []);

  (* Compose optionals *)
  let list_of_lists_head = Optional.(
    let outer : ('a list list, 'a list) optional =
      make
        ~get_opt:(function x :: _ -> Some x | [] -> None)
        ~set_opt:(fun a -> function _ :: rest -> a :: rest | [] -> [])
    in
    outer |>> list_head
  ) in
  check "composed optional get" (list_of_lists_head.get_opt [[1;2];[3;4]] = Some 1);
  check "composed optional get empty" (list_of_lists_head.get_opt [[];[3;4]] = None);
  check "composed optional set" (list_of_lists_head.set_opt 99 [[1;2];[3;4]] = [[99;2];[3;4]]);

  (* --- Traversal tests --- *)
  Printf.printf "\n── Traversal ──\n";

  check "each to_list" (Traversal.to_list Traversal.each [1;2;3] = [1;2;3]);
  check "each over" (Traversal.each.over (fun x -> x * 2) [1;2;3] = [2;4;6]);
  check "each length" (Traversal.length Traversal.each [1;2;3] = 3);
  check "each exists" (Traversal.exists Traversal.each (fun x -> x > 2) [1;2;3] = true);
  check "each exists false" (Traversal.exists Traversal.each (fun x -> x > 5) [1;2;3] = false);
  check "each for_all" (Traversal.for_all Traversal.each (fun x -> x > 0) [1;2;3] = true);
  check "each for_all false" (Traversal.for_all Traversal.each (fun x -> x > 1) [1;2;3] = false);

  let evens = Traversal.filtered (fun x -> x mod 2 = 0) in
  check "filtered to_list" (Traversal.to_list evens [1;2;3;4;5] = [2;4]);
  check "filtered over" (evens.over (fun x -> x * 10) [1;2;3;4;5] = [1;20;3;40;5]);
  check "filtered length" (Traversal.length evens [1;2;3;4;5] = 2);

  (* Composed traversal: employees' names *)
  let employee_names =
    Traversal.compose
      (Lens.to_traversal company_employees)
      Traversal.each
    |> fun t -> Traversal.compose t (Lens.to_traversal person_name)
  in
  check "composed traversal to_list" (
    Traversal.to_list employee_names acme = ["Alice"; "Carol"]);
  check "composed traversal over" (
    let acme2 = employee_names.over String.uppercase_ascii acme in
    List.map (fun e -> e.name) acme2.employees = ["ALICE"; "CAROL"]);

  (* --- Iso tests --- *)
  Printf.printf "\n── Iso ──\n";

  check "celsius to fahrenheit" (feq (celsius_fahrenheit.forward 100.0) 212.0);
  check "fahrenheit to celsius" (feq (celsius_fahrenheit.backward 32.0) 0.0);
  check "iso roundtrip" (feq (celsius_fahrenheit.backward (celsius_fahrenheit.forward 37.5)) 37.5);
  check "iso reverse" (feq ((Iso.reverse celsius_fahrenheit).forward 212.0) 100.0);
  check "string_chars forward" (string_chars.forward "abc" = ['a';'b';'c']);
  check "string_chars backward" (string_chars.backward ['x';'y';'z'] = "xyz");
  check "string_chars roundtrip" (string_chars.backward (string_chars.forward "hello") = "hello");

  let iso_lens = Iso.to_lens celsius_fahrenheit in
  check "iso to_lens get" (feq (iso_lens.get 0.0) 32.0);
  check "iso to_lens set" (feq (iso_lens.set 212.0 999.0) 100.0);  (* set ignores source *)

  let iso_prism = Iso.to_prism celsius_fahrenheit in
  check "iso to_prism preview" (
    match iso_prism.preview 100.0 with Some f -> feq f 212.0 | None -> false);
  check "iso to_prism build" (feq (iso_prism.build 32.0) 0.0);

  (* Composed iso *)
  let double_iso = Iso.make ~forward:(fun x -> x *. 2.0) ~backward:(fun x -> x /. 2.0) in
  let composed = Iso.(celsius_fahrenheit |>> double_iso) in
  check "composed iso forward" (feq (composed.forward 100.0) 424.0);
  check "composed iso backward" (feq (composed.backward 424.0) 100.0);

  Printf.printf "\n── Summary ──\n";
  Printf.printf "  %d/%d tests passed\n\n" !pass !total;
  if !fail > 0 then exit 1
