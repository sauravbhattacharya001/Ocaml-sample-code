(* Type Class Emulation in OCaml
   =============================
   Demonstrates how to emulate Haskell-style type classes using
   OCaml's module system (module types + functors).

   Concepts: module types as type class signatures, struct as instances,
   functors as type-class-constrained functions, first-class modules.
*)

(* ── 1. The "Show" type class ──────────────────────────────── *)

module type SHOW = sig
  type t
  val show : t -> string
end

(* Instances *)
module ShowInt : SHOW with type t = int = struct
  type t = int
  let show = string_of_int
end

module ShowFloat : SHOW with type t = float = struct
  type t = float
  let show = string_of_float
end

module ShowString : SHOW with type t = string = struct
  type t = string
  let show s = "\"" ^ s ^ "\""
end

module ShowBool : SHOW with type t = bool = struct
  type t = bool
  let show = function true -> "true" | false -> "false"
end

(* Derived instance: Show for lists given Show for elements *)
module ShowList (S : SHOW) : SHOW with type t = S.t list = struct
  type t = S.t list
  let show xs =
    "[" ^ (String.concat "; " (List.map S.show xs)) ^ "]"
end

(* ── 2. The "Eq" type class ────────────────────────────────── *)

module type EQ = sig
  type t
  val equal : t -> t -> bool
  val not_equal : t -> t -> bool
end

module EqInt : EQ with type t = int = struct
  type t = int
  let equal = Int.equal
  let not_equal a b = not (equal a b)
end

module EqString : EQ with type t = string = struct
  type t = string
  let equal = String.equal
  let not_equal a b = not (equal a b)
end

(* ── 3. The "Ord" type class (extends Eq) ──────────────────── *)

module type ORD = sig
  include EQ
  type ordering = Lt | Eq | Gt
  val compare : t -> t -> ordering
  val lt : t -> t -> bool
  val gt : t -> t -> bool
  val min : t -> t -> t
  val max : t -> t -> t
end

module OrdInt : ORD with type t = int = struct
  type t = int
  let equal = Int.equal
  let not_equal a b = not (equal a b)
  type ordering = Lt | Eq | Gt
  let compare a b =
    if a < b then Lt else if a = b then Eq else Gt
  let lt a b = a < b
  let gt a b = a > b
  let min a b = if a <= b then a else b
  let max a b = if a >= b then a else b
end

(* ── 4. The "Functor" type class ───────────────────────────── *)

module type FUNCTOR = sig
  type 'a t
  val fmap : ('a -> 'b) -> 'a t -> 'b t
end

module FunctorList : FUNCTOR with type 'a t = 'a list = struct
  type 'a t = 'a list
  let fmap = List.map
end

module FunctorOption : FUNCTOR with type 'a t = 'a option = struct
  type 'a t = 'a option
  let fmap f = function
    | None -> None
    | Some x -> Some (f x)
end

(* ── 5. The "Monoid" type class ────────────────────────────── *)

module type MONOID = sig
  type t
  val empty : t
  val append : t -> t -> t
  val concat : t list -> t
end

module MonoidString : MONOID with type t = string = struct
  type t = string
  let empty = ""
  let append = ( ^ )
  let concat = String.concat ""
end

module MonoidIntSum : MONOID with type t = int = struct
  type t = int
  let empty = 0
  let append = ( + )
  let concat = List.fold_left ( + ) 0
end

module MonoidList (A : sig type t end) : MONOID with type t = A.t list = struct
  type t = A.t list
  let empty = []
  let append = ( @ )
  let concat = List.concat
end

(* ── 6. Functor-based generic programming ──────────────────── *)

(* "print_list" works for any type with a Show instance *)
module PrintList (S : SHOW) = struct
  let print_list xs =
    let module SL = ShowList(S) in
    print_endline (SL.show xs)
end

(* "sort" works for any type with an Ord instance *)
module Sort (O : ORD) = struct
  let sort xs =
    List.sort (fun a b ->
      match O.compare a b with
      | O.Lt -> -1
      | O.Eq -> 0
      | O.Gt -> 1
    ) xs
end

(* "fold_map" works for any Monoid *)
module FoldMap (M : MONOID) = struct
  let fold_map f xs =
    M.concat (List.map f xs)
end

(* ── 7. First-class modules for runtime dispatch ──────────── *)

let show_value (type a) (module S : SHOW with type t = a) (x : a) =
  S.show x

let () =
  (* Using first-class modules *)
  print_endline (show_value (module ShowInt) 42);
  print_endline (show_value (module ShowFloat) 3.14);
  print_endline (show_value (module ShowString) "hello");
  print_endline (show_value (module ShowBool) true);

  (* Derived instances *)
  let module SIL = ShowList(ShowInt) in
  print_endline (SIL.show [1; 2; 3; 4; 5]);

  let module SFL = ShowList(ShowFloat) in
  print_endline (SFL.show [1.1; 2.2; 3.3]);

  (* Nested derived instances: Show for list of lists *)
  let module SILL = ShowList(ShowList(ShowInt)) in
  print_endline (SILL.show [[1;2]; [3;4]; [5]]);

  (* Using functor-based generic sort *)
  let module SI = Sort(OrdInt) in
  let sorted = SI.sort [5; 3; 8; 1; 9; 2; 7] in
  let module PIL = PrintList(ShowInt) in
  PIL.print_list sorted;

  (* Monoid fold_map *)
  let module FM = FoldMap(MonoidString) in
  let result = FM.fold_map string_of_int [1; 2; 3; 4; 5] in
  print_endline ("fold_map concat: " ^ result);

  let module FMS = FoldMap(MonoidIntSum) in
  let total = FMS.fold_map (fun x -> x * x) [1; 2; 3; 4; 5] in
  print_endline ("fold_map sum of squares: " ^ string_of_int total);

  print_endline "\nType class emulation demo complete!"
