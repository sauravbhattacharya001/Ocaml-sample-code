(* gap_buffer.ml — Gap Buffer text-editing data structure *)
(* ------------------------------------------------------------------ *)
(* A gap buffer is the data structure that classic text editors (most *)
(* famously GNU Emacs) use to represent the text being edited. It      *)
(* keeps the text in a single mutable byte buffer ([bytes]) split into  *)
(* three logical regions:                                              *)
(*                                                                     *)
(*     [ before-gap | == GAP == | after-gap ]                          *)
(*       0..gap_lo     gap_lo..    gap_hi..cap                          *)
(*                     gap_hi                                           *)
(*                                                                     *)
(* The cursor sits exactly at the left edge of the gap. Because edits  *)
(* in a text editor cluster around the cursor, insertion and deletion  *)
(* at the cursor are amortised O(1): we just consume / release one     *)
(* gap cell. The only non-trivial work is *moving* the cursor, which   *)
(* shuffles characters across the gap (O(distance)), and *growing* the *)
(* buffer when the gap is exhausted (amortised O(1) via doubling).     *)
(*                                                                     *)
(* This is a nice complement to [rope.ml] (a persistent, tree-based    *)
(* text structure) — the gap buffer is the mutable, cache-friendly,    *)
(* "single cursor" cousin that real editors reach for first.          *)
(*                                                                     *)
(* Concepts: imperative arrays, mutable records, amortised analysis,   *)
(* invariant maintenance, Bytes.blit, cursor/locality optimisation.    *)
(* ------------------------------------------------------------------ *)

module GapBuffer = struct

  type t = {
    mutable data   : bytes;  (* backing store; gap contents are garbage *)
    mutable gap_lo : int;    (* start of the gap = cursor position      *)
    mutable gap_hi : int;    (* one past the end of the gap (exclusive) *)
  }
  (* Invariants (always restored before any function returns):
       0 <= gap_lo <= gap_hi <= Bytes.length data
     Logical text length        = Bytes.length data - (gap_hi - gap_lo)
     Cursor (caret) position     = gap_lo
     Character i of the logical text lives at:
       data[i]                       if i < gap_lo
       data[i + (gap_hi - gap_lo)]   if i >= gap_lo                     *)

  let min_capacity = 8

  (* ---- Construction ---- *)

  (** [create ()] builds an empty buffer with a small initial gap. *)
  let create () =
    { data = Bytes.create min_capacity; gap_lo = 0; gap_hi = min_capacity }

  (** [of_string s] builds a buffer holding [s] with the cursor at the
      end (the natural place a caret lands after opening a document). *)
  let of_string s =
    let n = String.length s in
    let cap = if n < min_capacity then min_capacity else n in
    let data = Bytes.create cap in
    Bytes.blit_string s 0 data 0 n;
    (* Text occupies [0, n); the gap is everything after it. *)
    { data; gap_lo = n; gap_hi = cap }

  (* ---- Queries ---- *)

  let capacity buf = Bytes.length buf.data

  (** Size of the gap (free cells available for insertion). *)
  let gap_size buf = buf.gap_hi - buf.gap_lo

  (** Number of characters of actual text stored. *)
  let length buf = capacity buf - gap_size buf

  let is_empty buf = length buf = 0

  (** Current cursor position, in [0, length]. *)
  let cursor buf = buf.gap_lo

  (** Map a logical text index to its physical index in [data]. *)
  let phys_index buf i =
    if i < buf.gap_lo then i else i + gap_size buf

  (** [char_at buf i] returns the [i]-th character of the text.
      @raise Invalid_argument if [i] is out of range. *)
  let char_at buf i =
    if i < 0 || i >= length buf then
      invalid_arg "GapBuffer.char_at: index out of bounds";
    Bytes.get buf.data (phys_index buf i)

  (** Materialise the whole text as a string (excludes the gap). *)
  let to_string buf =
    let left_len = buf.gap_lo in
    let right_len = capacity buf - buf.gap_hi in
    let out = Bytes.create (left_len + right_len) in
    Bytes.blit buf.data 0 out 0 left_len;
    Bytes.blit buf.data buf.gap_hi out left_len right_len;
    Bytes.unsafe_to_string out

  (** Substring of the logical text: [sub buf start len].
      @raise Invalid_argument if the range is out of bounds. *)
  let sub buf start len =
    if start < 0 || len < 0 || start + len > length buf then
      invalid_arg "GapBuffer.sub: range out of bounds";
    let out = Bytes.create len in
    for k = 0 to len - 1 do
      Bytes.set out k (Bytes.get buf.data (phys_index buf (start + k)))
    done;
    Bytes.unsafe_to_string out

  (** Iterate over the text left-to-right. *)
  let iter f buf =
    for i = 0 to length buf - 1 do
      f (char_at buf i)
    done

  (** Left fold over the text. *)
  let fold_left f init buf =
    let acc = ref init in
    for i = 0 to length buf - 1 do
      acc := f !acc (char_at buf i)
    done;
    !acc

  (* ---- Internal: gap maintenance ---- *)

  (* Grow the backing store so the gap can hold at least [needed] more
     characters. Capacity at least doubles, keeping amortised O(1)
     insertion. The text on either side of the gap is preserved. *)
  let grow buf needed =
    let text_len = length buf in
    let right_len = capacity buf - buf.gap_hi in
    let new_cap =
      let c = ref (max min_capacity (capacity buf * 2)) in
      while !c - text_len < needed do c := !c * 2 done;
      !c
    in
    let data = Bytes.create new_cap in
    (* Copy the before-gap part verbatim ... *)
    Bytes.blit buf.data 0 data 0 buf.gap_lo;
    (* ... and push the after-gap part flush to the new right edge. *)
    let new_gap_hi = new_cap - right_len in
    Bytes.blit buf.data buf.gap_hi data new_gap_hi right_len;
    buf.data <- data;
    buf.gap_hi <- new_gap_hi
    (* gap_lo is unchanged: the cursor stays put. *)

  (** [reserve buf n] guarantees the gap can absorb [n] more chars. *)
  let reserve buf n =
    if gap_size buf < n then grow buf n

  (* ---- Cursor movement ---- *)

  (** Move the cursor to absolute position [pos] (clamped to range),
      shuffling characters across the gap as needed. O(distance moved). *)
  let move_to buf pos =
    let pos = if pos < 0 then 0 else if pos > length buf then length buf else pos in
    if pos < buf.gap_lo then begin
      (* Cursor moves left: shift [pos, gap_lo) chars to the gap's right. *)
      let count = buf.gap_lo - pos in
      Bytes.blit buf.data pos buf.data (buf.gap_hi - count) count;
      buf.gap_lo <- buf.gap_lo - count;
      buf.gap_hi <- buf.gap_hi - count
    end else if pos > buf.gap_lo then begin
      (* Cursor moves right: shift chars after the gap to the gap's left.
         [count] logical chars starting at gap_lo live at gap_hi.. *)
      let count = pos - buf.gap_lo in
      Bytes.blit buf.data buf.gap_hi buf.data buf.gap_lo count;
      buf.gap_lo <- buf.gap_lo + count;
      buf.gap_hi <- buf.gap_hi + count
    end
    (* pos = gap_lo: nothing to do. *)

  let move_left buf = move_to buf (buf.gap_lo - 1)
  let move_right buf = move_to buf (buf.gap_lo + 1)
  let move_to_start buf = move_to buf 0
  let move_to_end buf = move_to buf (length buf)

  (* ---- Editing at the cursor ---- *)

  (** Insert a single character at the cursor; cursor advances past it. *)
  let insert_char buf c =
    reserve buf 1;
    Bytes.set buf.data buf.gap_lo c;
    buf.gap_lo <- buf.gap_lo + 1

  (** Insert a whole string at the cursor; cursor ends after it. *)
  let insert_string buf s =
    let n = String.length s in
    if n > 0 then begin
      reserve buf n;
      Bytes.blit_string s 0 buf.data buf.gap_lo n;
      buf.gap_lo <- buf.gap_lo + n
    end

  (** Backspace: delete the character immediately *before* the cursor.
      Returns [true] if a character was removed, [false] at start. *)
  let delete_before buf =
    if buf.gap_lo > 0 then begin
      buf.gap_lo <- buf.gap_lo - 1;  (* simply enlarge the gap leftward *)
      true
    end else false

  (** Forward delete: remove the character immediately *after* the
      cursor. Returns [true] if a character was removed. *)
  let delete_after buf =
    if buf.gap_hi < capacity buf then begin
      buf.gap_hi <- buf.gap_hi + 1;  (* enlarge the gap rightward *)
      true
    end else false

  (** Delete up to [n] characters forward from the cursor.
      Returns the number actually deleted. *)
  let delete buf n =
    let avail = capacity buf - buf.gap_hi in
    let k = if n < 0 then 0 else if n > avail then avail else n in
    buf.gap_hi <- buf.gap_hi + k;
    k

  (** Reset to an empty buffer (keeps existing capacity). *)
  let clear buf =
    buf.gap_lo <- 0;
    buf.gap_hi <- capacity buf

  (* ---- Higher-level convenience ---- *)

  (** Insert [s] at absolute position [pos] (moves cursor there first). *)
  let insert_at buf pos s =
    move_to buf pos;
    insert_string buf s

  (** Delete [len] characters starting at absolute position [pos].
      Returns the number actually deleted. *)
  let delete_range buf pos len =
    move_to buf pos;
    delete buf len

  (** First index of substring [pat] in the text, or [None].
      Naive O(n*m) scan — fine for an illustrative editor structure. *)
  let find ?(start = 0) buf pat =
    let n = length buf and m = String.length pat in
    if m = 0 then Some (if start < 0 then 0 else min start n)
    else begin
      let from = if start < 0 then 0 else start in
      let result = ref None in
      let i = ref from in
      let limit = n - m in
      while !result = None && !i <= limit do
        let j = ref 0 in
        while !j < m && char_at buf (!i + !j) = String.get pat !j do
          incr j
        done;
        if !j = m then result := Some !i else incr i
      done;
      !result
    end

  (** Replace every (non-overlapping, left-to-right) occurrence of
      [pat] with [rep]. Returns the number of replacements made.
      A no-op when [pat] is empty. Cursor is left at end of text. *)
  let replace_all buf pat rep =
    if String.length pat = 0 then 0
    else begin
      let src = to_string buf in
      let m = String.length pat in
      let count = ref 0 in
      let out = Buffer.create (String.length src) in
      let i = ref 0 in
      let len = String.length src in
      while !i <= len - m do
        if String.sub src !i m = pat then begin
          Buffer.add_string out rep;
          incr count;
          i := !i + m
        end else begin
          Buffer.add_char out src.[!i];
          incr i
        end
      done;
      (* Copy the tail that was too short to match. *)
      Buffer.add_string out (String.sub src !i (len - !i));
      if !count > 0 then begin
        let s = Buffer.contents out in
        let cap = if String.length s < min_capacity then min_capacity
                  else String.length s in
        let data = Bytes.create cap in
        Bytes.blit_string s 0 data 0 (String.length s);
        buf.data <- data;
        buf.gap_lo <- String.length s;
        buf.gap_hi <- cap
      end;
      !count
    end

  (** Diagnostic snapshot: (text_length, capacity, gap_size, cursor). *)
  let stats buf = (length buf, capacity buf, gap_size buf, cursor buf)

  (** Render the buffer with the cursor shown as '|' — handy for demos
      and debugging. E.g. "hel|lo" means the caret is after 'l'. *)
  let to_string_with_cursor buf =
    let left = Bytes.sub_string buf.data 0 buf.gap_lo in
    let right_len = capacity buf - buf.gap_hi in
    let right = Bytes.sub_string buf.data buf.gap_hi right_len in
    left ^ "|" ^ right

end

(* ------------------------------------------------------------------ *)
(* Demo                                                                *)
(* ------------------------------------------------------------------ *)

let () =
  let open GapBuffer in
  Printf.printf "=== Gap Buffer demo ===\n\n";

  (* Type "Hello" one character at a time. *)
  let b = create () in
  String.iter (fun c -> insert_char b c) "Hello";
  Printf.printf "After typing 'Hello':            %S\n" (to_string b);
  Printf.printf "  cursor view:                   %s\n" (to_string_with_cursor b);

  (* Move the cursor back to the start and insert a greeting. *)
  move_to_start b;
  insert_string b ">> ";
  Printf.printf "Insert '>> ' at start:           %S\n" (to_string b);
  Printf.printf "  cursor view:                   %s\n" (to_string_with_cursor b);

  (* Jump to the end and append. *)
  move_to_end b;
  insert_string b ", world!";
  Printf.printf "Append ', world!':               %S\n" (to_string b);

  (* Backspace twice: removes '!' then 'd' from the end. *)
  ignore (delete_before b);
  ignore (delete_before b);
  Printf.printf "Two backspaces:                  %S\n" (to_string b);

  (* Forward-delete the leading ">> " from position 0. *)
  let removed = delete_range b 0 3 in
  Printf.printf "Delete %d chars at pos 0:         %S\n" removed (to_string b);

  (* Substring + char_at. *)
  Printf.printf "sub 0 5:                         %S\n" (sub b 0 5);
  Printf.printf "char_at 1:                       %c\n" (char_at b 1);

  (* Search. *)
  (match find b "world" with
   | Some i -> Printf.printf "find \"world\":                    at index %d\n" i
   | None   -> Printf.printf "find \"world\":                    not found\n");

  (* Replace. *)
  let n = replace_all b "l" "L" in
  Printf.printf "replace_all 'l'->'L' (%d hits):   %S\n" n (to_string b);

  (* of_string + stats. *)
  let doc = of_string "edit me" in
  let (len, cap, gap, cur) = stats doc in
  Printf.printf "\nof_string \"edit me\" -> text=%S\n" (to_string doc);
  Printf.printf "  stats: length=%d capacity=%d gap=%d cursor=%d\n"
    len cap gap cur;

  (* Stress the growth path: insert past the initial capacity. *)
  let big = create () in
  for i = 1 to 100 do insert_char big (Char.chr (Char.code 'a' + (i mod 26))) done;
  Printf.printf "\nInserted 100 chars; length=%d capacity=%d\n"
    (length big) (capacity big);
  Printf.printf "  to_string length matches:      %b\n"
    (String.length (to_string big) = length big);

  Printf.printf "\n=== Done ===\n"
