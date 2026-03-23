(* Ring Buffer (Circular Buffer) Implementation
 *
 * A fixed-capacity, mutable circular buffer supporting O(1) push/pop
 * from both ends, iteration, bulk operations, and fold/map.
 *
 * Usage:
 *   let rb = RingBuffer.create 8 0 in
 *   RingBuffer.push_back rb 42;
 *   RingBuffer.push_back rb 99;
 *   Printf.printf "front = %d\n" (RingBuffer.peek_front rb);
 *   Printf.printf "back  = %d\n" (RingBuffer.peek_back rb);
 *   RingBuffer.iter (Printf.printf "%d ") rb;
 *   print_newline ()
 *)

module RingBuffer = struct
  type 'a t = {
    mutable data : 'a array;
    mutable head : int;    (* index of first element *)
    mutable len  : int;    (* number of elements stored *)
    cap          : int;    (* fixed capacity *)
  }

  let create cap default_val =
    if cap <= 0 then invalid_arg "RingBuffer.create: capacity must be > 0";
    { data = Array.make cap default_val; head = 0; len = 0; cap }

  let capacity rb = rb.cap
  let length rb = rb.len
  let is_empty rb = rb.len = 0
  let is_full rb = rb.len = rb.cap

  let clear rb = rb.head <- 0; rb.len <- 0

  (* internal index helper *)
  let idx rb i = (rb.head + i) mod rb.cap

  let push_back rb x =
    if rb.len = rb.cap then begin
      (* overwrite oldest element, advance head *)
      rb.data.(idx rb rb.len) <- x;
      rb.head <- (rb.head + 1) mod rb.cap
    end else begin
      rb.data.(idx rb rb.len) <- x;
      rb.len <- rb.len + 1
    end

  let push_front rb x =
    rb.head <- (rb.head - 1 + rb.cap) mod rb.cap;
    rb.data.(rb.head) <- x;
    if rb.len < rb.cap then rb.len <- rb.len + 1
    (* if full, tail element is silently dropped *)

  let pop_front rb =
    if rb.len = 0 then failwith "RingBuffer.pop_front: empty";
    let v = rb.data.(rb.head) in
    rb.head <- (rb.head + 1) mod rb.cap;
    rb.len <- rb.len - 1;
    v

  let pop_back rb =
    if rb.len = 0 then failwith "RingBuffer.pop_back: empty";
    rb.len <- rb.len - 1;
    rb.data.(idx rb rb.len)

  let peek_front rb =
    if rb.len = 0 then failwith "RingBuffer.peek_front: empty";
    rb.data.(rb.head)

  let peek_back rb =
    if rb.len = 0 then failwith "RingBuffer.peek_back: empty";
    rb.data.(idx rb (rb.len - 1))

  let get rb i =
    if i < 0 || i >= rb.len then invalid_arg "RingBuffer.get: index out of bounds";
    rb.data.(idx rb i)

  let set rb i x =
    if i < 0 || i >= rb.len then invalid_arg "RingBuffer.set: index out of bounds";
    rb.data.(idx rb i) <- x

  (* Iteration *)
  let iter f rb =
    for i = 0 to rb.len - 1 do
      f rb.data.(idx rb i)
    done

  let iteri f rb =
    for i = 0 to rb.len - 1 do
      f i rb.data.(idx rb i)
    done

  let fold_left f acc rb =
    let r = ref acc in
    for i = 0 to rb.len - 1 do
      r := f !r rb.data.(idx rb i)
    done;
    !r

  let to_list rb =
    let result = ref [] in
    for i = rb.len - 1 downto 0 do
      result := rb.data.(idx rb i) :: !result
    done;
    !result

  let to_array rb =
    if rb.len = 0 then [||]
    else begin
      let arr = Array.make rb.len rb.data.(rb.head) in
      for i = 0 to rb.len - 1 do
        arr.(i) <- rb.data.(idx rb i)
      done;
      arr
    end

  let of_list cap default_val lst =
    let rb = create cap default_val in
    List.iter (push_back rb) lst;
    rb

  let map f rb =
    if rb.len = 0 then create rb.cap (Obj.magic 0)
    else begin
      let first = f rb.data.(rb.head) in
      let new_rb = create rb.cap first in
      new_rb.data.(0) <- first;
      for i = 1 to rb.len - 1 do
        new_rb.data.(i) <- f rb.data.(idx rb i)
      done;
      new_rb.len <- rb.len;
      new_rb
    end

  let exists pred rb =
    let found = ref false in
    let i = ref 0 in
    while !i < rb.len && not !found do
      if pred rb.data.(idx rb !i) then found := true;
      incr i
    done;
    !found

  let for_all pred rb =
    let ok = ref true in
    let i = ref 0 in
    while !i < rb.len && !ok do
      if not (pred rb.data.(idx rb !i)) then ok := false;
      incr i
    done;
    !ok

  let find_opt pred rb =
    let result = ref None in
    let i = ref 0 in
    while !i < rb.len && !result = None do
      let v = rb.data.(idx rb !i) in
      if pred v then result := Some v;
      incr i
    done;
    !result

  (* Pretty-print *)
  let pp printer rb =
    Printf.printf "[|";
    iteri (fun i x ->
      if i > 0 then Printf.printf "; ";
      printer x
    ) rb;
    Printf.printf "|] (len=%d, cap=%d)" rb.len rb.cap

  let pp_int = pp (Printf.printf "%d")
  let pp_string = pp (Printf.printf "%S")
end

(* ── Demo ────────────────────────────────────────────────────────── *)

let () =
  Printf.printf "=== Ring Buffer Demo ===\n\n";

  (* Basic push/pop *)
  let rb = RingBuffer.create 5 0 in
  List.iter (RingBuffer.push_back rb) [10; 20; 30; 40; 50];
  Printf.printf "After pushing 10..50 (cap=5): ";
  RingBuffer.pp_int rb; print_newline ();

  (* Overflow — oldest dropped *)
  RingBuffer.push_back rb 60;
  RingBuffer.push_back rb 70;
  Printf.printf "After pushing 60, 70 (overflow): ";
  RingBuffer.pp_int rb; print_newline ();

  Printf.printf "front = %d, back = %d\n"
    (RingBuffer.peek_front rb) (RingBuffer.peek_back rb);

  (* Pop from front *)
  let v = RingBuffer.pop_front rb in
  Printf.printf "Popped front: %d → " v;
  RingBuffer.pp_int rb; print_newline ();

  (* push_front *)
  RingBuffer.push_front rb 99;
  Printf.printf "After push_front 99: ";
  RingBuffer.pp_int rb; print_newline ();

  (* to_list / to_array *)
  Printf.printf "to_list: [%s]\n"
    (String.concat "; " (List.map string_of_int (RingBuffer.to_list rb)));

  (* fold *)
  let sum = RingBuffer.fold_left ( + ) 0 rb in
  Printf.printf "Sum via fold_left: %d\n" sum;

  (* map *)
  let doubled = RingBuffer.map (fun x -> x * 2) rb in
  Printf.printf "Doubled: ";
  RingBuffer.pp_int doubled; print_newline ();

  (* exists / for_all *)
  Printf.printf "exists (>50): %b\n" (RingBuffer.exists (fun x -> x > 50) rb);
  Printf.printf "for_all (>0): %b\n" (RingBuffer.for_all (fun x -> x > 0) rb);

  (* of_list *)
  let rb2 = RingBuffer.of_list 4 0 [1; 2; 3; 4; 5; 6] in
  Printf.printf "\nof_list [1..6] cap=4: ";
  RingBuffer.pp_int rb2; print_newline ();

  Printf.printf "\n=== Done ===\n"
