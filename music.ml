(* music.ml - Algorithmic Music Composition
 *
 * Features:
 * - Music theory: notes, intervals, scales, chords
 * - Melody generation: random, Markov chain, L-system
 * - Chord progression generation (circle of fifths, common patterns)
 * - Rhythm patterns and time signatures
 * - ABC notation export for playback/sharing
 * - MIDI-like event representation
 * - Transposition, inversion, retrograde transformations
 *
 * Usage: ocaml music.ml
 *)

(* ==================== Core Types ==================== *)

type pitch_class = C | Cs | D | Ds | E | F | Fs | G | Gs | A | As | B

type note = {
  pitch : pitch_class;
  octave : int;
  duration : float;  (* in beats: 1.0 = quarter note *)
  velocity : int;    (* 0-127 *)
}

type rest = { rest_duration : float }

type music_event =
  | Note of note
  | Rest of rest
  | Chord of note list

type scale_type =
  | Major | Minor | HarmonicMinor | MelodicMinor
  | Dorian | Phrygian | Lydian | Mixolydian | Aeolian | Locrian
  | PentatonicMajor | PentatonicMinor | Blues
  | WholeTone | Chromatic | Diminished | Augmented

type chord_quality = MajChord | MinChord | Dom7 | Maj7 | Min7 | Dim | Aug | Sus2 | Sus4

type time_sig = { beats_per_measure : int; beat_value : int }

type melody = {
  events : music_event list;
  tempo : int;
  time_signature : time_sig;
  key : pitch_class;
  scale : scale_type;
}

(* ==================== Pitch Utilities ==================== *)

let pitch_to_int = function
  | C -> 0 | Cs -> 1 | D -> 2 | Ds -> 3 | E -> 4 | F -> 5
  | Fs -> 6 | G -> 7 | Gs -> 8 | A -> 9 | As -> 10 | B -> 11

let int_to_pitch n =
  match ((n mod 12) + 12) mod 12 with
  | 0 -> C | 1 -> Cs | 2 -> D | 3 -> Ds | 4 -> E | 5 -> F
  | 6 -> Fs | 7 -> G | 8 -> Gs | 9 -> A | 10 -> As | _ -> B

let pitch_to_string = function
  | C -> "C" | Cs -> "C#" | D -> "D" | Ds -> "D#" | E -> "E" | F -> "F"
  | Fs -> "F#" | G -> "G" | Gs -> "G#" | A -> "A" | As -> "A#" | B -> "B"

let pitch_to_abc = function
  | C -> "C" | Cs -> "^C" | D -> "D" | Ds -> "^D" | E -> "E" | F -> "F"
  | Fs -> "^F" | G -> "G" | Gs -> "^G" | A -> "A" | As -> "^A" | B -> "B"

let note_to_midi n = (n.octave + 1) * 12 + pitch_to_int n.pitch

let midi_to_note ?(duration=1.0) ?(velocity=80) midi =
  let octave = midi / 12 - 1 in
  let pitch = int_to_pitch (midi mod 12) in
  { pitch; octave; duration; velocity }

(* ==================== Scales ==================== *)

let scale_intervals = function
  | Major -> [2;2;1;2;2;2;1]
  | Minor -> [2;1;2;2;1;2;2]
  | HarmonicMinor -> [2;1;2;2;1;3;1]
  | MelodicMinor -> [2;1;2;2;2;2;1]
  | Dorian -> [2;1;2;2;2;1;2]
  | Phrygian -> [1;2;2;2;1;2;2]
  | Lydian -> [2;2;2;1;2;2;1]
  | Mixolydian -> [2;2;1;2;2;1;2]
  | Aeolian -> [2;1;2;2;1;2;2]
  | Locrian -> [1;2;2;1;2;2;2]
  | PentatonicMajor -> [2;2;3;2;3]
  | PentatonicMinor -> [3;2;2;3;2]
  | Blues -> [3;2;1;1;3;2]
  | WholeTone -> [2;2;2;2;2;2]
  | Chromatic -> [1;1;1;1;1;1;1;1;1;1;1;1]
  | Diminished -> [2;1;2;1;2;1;2;1]
  | Augmented -> [3;1;3;1;3;1]

let scale_name = function
  | Major -> "Major" | Minor -> "Natural Minor" | HarmonicMinor -> "Harmonic Minor"
  | MelodicMinor -> "Melodic Minor" | Dorian -> "Dorian" | Phrygian -> "Phrygian"
  | Lydian -> "Lydian" | Mixolydian -> "Mixolydian" | Aeolian -> "Aeolian"
  | Locrian -> "Locrian" | PentatonicMajor -> "Pentatonic Major"
  | PentatonicMinor -> "Pentatonic Minor" | Blues -> "Blues"
  | WholeTone -> "Whole Tone" | Chromatic -> "Chromatic"
  | Diminished -> "Diminished" | Augmented -> "Augmented"

let build_scale root scale_t =
  let intervals = scale_intervals scale_t in
  let root_int = pitch_to_int root in
  let rec aux acc current = function
    | [] -> List.rev acc
    | i :: rest -> aux (int_to_pitch current :: acc) (current + i) rest
  in
  aux [root] (root_int + List.hd intervals) (List.tl intervals)

let scale_degree root scale_t degree =
  let notes = build_scale root scale_t in
  let len = List.length notes in
  List.nth notes ((degree - 1) mod len)

(* ==================== Chords ==================== *)

let chord_intervals = function
  | MajChord -> [0; 4; 7]
  | MinChord -> [0; 3; 7]
  | Dom7 -> [0; 4; 7; 10]
  | Maj7 -> [0; 4; 7; 11]
  | Min7 -> [0; 3; 7; 10]
  | Dim -> [0; 3; 6]
  | Aug -> [0; 4; 8]
  | Sus2 -> [0; 2; 7]
  | Sus4 -> [0; 5; 7]

let chord_name = function
  | MajChord -> "" | MinChord -> "m" | Dom7 -> "7" | Maj7 -> "maj7"
  | Min7 -> "m7" | Dim -> "dim" | Aug -> "aug" | Sus2 -> "sus2" | Sus4 -> "sus4"

let build_chord root octave quality duration =
  let root_midi = (octave + 1) * 12 + pitch_to_int root in
  let intervals = chord_intervals quality in
  List.map (fun i ->
    midi_to_note ~duration ~velocity:70 (root_midi + i)
  ) intervals

(* Diatonic chords for a scale *)
let diatonic_chords root scale_t =
  let major_pattern = [MajChord; MinChord; MinChord; MajChord; MajChord; MinChord; Dim] in
  let minor_pattern = [MinChord; Dim; MajChord; MinChord; MinChord; MajChord; MajChord] in
  let pattern = match scale_t with
    | Major | Lydian | Mixolydian -> major_pattern
    | Minor | Aeolian | Dorian | Phrygian -> minor_pattern
    | _ -> major_pattern
  in
  let scale_notes = build_scale root scale_t in
  List.mapi (fun i q ->
    if i < List.length scale_notes then
      (List.nth scale_notes i, q)
    else (root, MajChord)
  ) pattern

(* ==================== Chord Progressions ==================== *)

(* Common progressions as scale degree sequences *)
let progression_patterns = [
  ("I-IV-V-I", [1;4;5;1]);
  ("I-V-vi-IV", [1;5;6;4]);
  ("ii-V-I", [2;5;1]);
  ("I-vi-IV-V", [1;6;4;5]);
  ("I-IV-vi-V", [1;4;6;5]);
  ("vi-IV-I-V", [6;4;1;5]);
  ("I-V-IV-V", [1;5;4;5]);
  ("I-iii-IV-V", [1;3;4;5]);
  ("12-bar blues", [1;1;1;1;4;4;1;1;5;4;1;5]);
]

let build_progression root scale_t degrees octave duration =
  let chords = diatonic_chords root scale_t in
  List.map (fun deg ->
    let idx = ((deg - 1) mod List.length chords + List.length chords) mod List.length chords in
    let (chord_root, quality) = List.nth chords idx in
    Chord (build_chord chord_root octave quality duration)
  ) degrees

(* ==================== Random & Generation Utilities ==================== *)

let () = Random.self_init ()

let random_element lst =
  List.nth lst (Random.int (List.length lst))

let weighted_random weights =
  let total = List.fold_left (+.) 0.0 (List.map snd weights) in
  let r = Random.float total in
  let rec pick acc = function
    | [] -> fst (List.hd weights)
    | (v, w) :: rest ->
      let acc' = acc +. w in
      if r < acc' then v else pick acc' rest
  in
  pick 0.0 weights

(* ==================== Melody Generation ==================== *)

(* Random walk melody *)
let generate_random_walk ?(octave=4) ?(velocity=80) root scale_t num_notes =
  let scale = build_scale root scale_t in
  let scale_len = List.length scale in
  let durations = [0.25; 0.5; 0.5; 1.0; 1.0; 1.0; 2.0] in
  let rec gen acc pos remaining =
    if remaining <= 0 then List.rev acc
    else
      let step = Random.int 5 - 2 in (* -2 to +2 *)
      let new_pos = max 0 (min (scale_len * 2 - 1) (pos + step)) in
      let scale_idx = new_pos mod scale_len in
      let oct = octave + new_pos / scale_len in
      let pitch = List.nth scale scale_idx in
      let dur = random_element durations in
      let n = Note { pitch; octave = oct; duration = dur; velocity } in
      gen (n :: acc) new_pos (remaining - 1)
  in
  gen [] (scale_len / 2) num_notes

(* Markov chain melody from seed pattern *)
let generate_markov ?(octave=4) ?(velocity=80) root scale_t seed_length num_notes =
  let scale = build_scale root scale_t in
  let scale_len = List.length scale in
  (* Build transition probabilities favoring stepwise motion *)
  let weights step =
    let abs_step = abs step in
    if abs_step = 0 then 0.1
    else if abs_step = 1 then 0.35
    else if abs_step = 2 then 0.25
    else if abs_step = 3 then 0.15
    else 0.05
  in
  let gen_next current_idx =
    let candidates = List.init 11 (fun i -> i - 5) in
    let w = List.map (fun s -> (s, weights s)) candidates in
    let step = weighted_random w in
    max 0 (min (scale_len * 2 - 1) (current_idx + step))
  in
  let durations = [
    (0.25, 0.15); (0.5, 0.3); (1.0, 0.35); (1.5, 0.1); (2.0, 0.1)
  ] in
  let _ = seed_length in
  let rec gen acc pos remaining =
    if remaining <= 0 then List.rev acc
    else
      let new_pos = gen_next pos in
      let scale_idx = new_pos mod scale_len in
      let oct = octave + new_pos / scale_len in
      let pitch = List.nth scale scale_idx in
      let dur = weighted_random durations in
      (* Occasional rest *)
      if Random.float 1.0 < 0.1 then
        gen (Rest { rest_duration = dur } :: acc) new_pos (remaining - 1)
      else
        let n = Note { pitch; octave = oct; duration = dur; velocity } in
        gen (n :: acc) new_pos (remaining - 1)
  in
  gen [] (scale_len / 2) num_notes

(* L-system melody generation *)
type lsystem_rule = char -> string

let lindenmayer axiom rules iterations =
  let apply_rules s =
    String.concat "" (List.init (String.length s) (fun i ->
      let c = s.[i] in
      try rules c
      with _ -> String.make 1 c
    ))
  in
  let rec iterate s n =
    if n <= 0 then s
    else iterate (apply_rules s) (n - 1)
  in
  iterate axiom iterations

let generate_lsystem ?(octave=4) ?(velocity=80) root scale_t iterations =
  let scale = build_scale root scale_t in
  let scale_len = List.length scale in
  (* Musical L-system rules *)
  let rules = function
    | 'A' -> "AB"
    | 'B' -> "ACA"
    | 'C' -> "BD"
    | 'D' -> "CA"
    | c -> String.make 1 c
  in
  let result = lindenmayer "A" rules iterations in
  let pos = ref (scale_len / 2) in
  List.init (String.length result) (fun i ->
    let step = match result.[i] with
      | 'A' -> 1 | 'B' -> 2 | 'C' -> -1 | 'D' -> -2 | _ -> 0
    in
    pos := max 0 (min (scale_len * 2 - 1) (!pos + step));
    let scale_idx = !pos mod scale_len in
    let oct = octave + !pos / scale_len in
    let pitch = List.nth scale scale_idx in
    let dur = match result.[i] with
      | 'A' -> 1.0 | 'B' -> 0.5 | 'C' -> 0.5 | 'D' -> 1.5 | _ -> 1.0
    in
    Note { pitch; octave = oct; duration = dur; velocity }
  )

(* ==================== Transformations ==================== *)

let transpose semitones event =
  match event with
  | Note n ->
    let midi = note_to_midi n + semitones in
    Note (midi_to_note ~duration:n.duration ~velocity:n.velocity midi)
  | Chord notes ->
    Chord (List.map (fun n ->
      let midi = note_to_midi n + semitones in
      midi_to_note ~duration:n.duration ~velocity:n.velocity midi
    ) notes)
  | Rest _ as r -> r

let retrograde events = List.rev events

let invert pivot events =
  List.map (fun event ->
    match event with
    | Note n ->
      let midi = note_to_midi n in
      let inverted = 2 * pivot - midi in
      Note (midi_to_note ~duration:n.duration ~velocity:n.velocity inverted)
    | Chord notes ->
      Chord (List.map (fun n ->
        let midi = note_to_midi n in
        let inverted = 2 * pivot - midi in
        midi_to_note ~duration:n.duration ~velocity:n.velocity inverted
      ) notes)
    | Rest _ as r -> r
  ) events

let augment factor events =
  List.map (fun event ->
    match event with
    | Note n -> Note { n with duration = n.duration *. factor }
    | Chord notes -> Chord (List.map (fun n -> { n with duration = n.duration *. factor }) notes)
    | Rest r -> Rest { rest_duration = r.rest_duration *. factor }
  ) events

(* ==================== Rhythm Generation ==================== *)

let euclidean_rhythm pulses steps =
  (* Bjorklund's algorithm for Euclidean rhythms *)
  if pulses >= steps then List.init steps (fun _ -> true)
  else if pulses <= 0 then List.init steps (fun _ -> false)
  else begin
    let pattern = Array.make steps false in
    let bucket = ref 0 in
    for i = 0 to steps - 1 do
      bucket := !bucket + pulses;
      if !bucket >= steps then begin
        pattern.(i) <- true;
        bucket := !bucket - steps
      end
    done;
    Array.to_list pattern
  end

let apply_rhythm scale_notes rhythm duration =
  List.map2 (fun pitch hit ->
    if hit then
      Note { pitch; octave = 4; duration; velocity = 80 }
    else
      Rest { rest_duration = duration }
  ) scale_notes rhythm

(* ==================== ABC Notation Export ==================== *)

let duration_to_abc dur =
  if dur <= 0.25 then "/4"
  else if dur <= 0.5 then "/2"
  else if dur <= 1.0 then ""
  else if dur <= 1.5 then "3/2"
  else if dur <= 2.0 then "2"
  else if dur <= 3.0 then "3"
  else "4"

let note_to_abc_str n =
  let p = if n.octave >= 5 then
    String.lowercase_ascii (pitch_to_abc n.pitch)
  else
    pitch_to_abc n.pitch
  in
  let octave_marks =
    if n.octave >= 6 then String.make (n.octave - 5) '\''
    else if n.octave <= 3 then String.make (4 - n.octave) ','
    else ""
  in
  p ^ octave_marks ^ duration_to_abc n.duration

let event_to_abc = function
  | Note n -> note_to_abc_str n
  | Rest r -> "z" ^ duration_to_abc r.rest_duration
  | Chord notes ->
    "[" ^ String.concat "" (List.map note_to_abc_str notes) ^ "]"

let melody_to_abc mel title =
  let buf = Buffer.create 256 in
  Buffer.add_string buf (Printf.sprintf "X:1\nT:%s\n" title);
  Buffer.add_string buf (Printf.sprintf "M:%d/%d\n" mel.time_signature.beats_per_measure mel.time_signature.beat_value);
  Buffer.add_string buf (Printf.sprintf "L:1/4\nQ:1/4=%d\n" mel.tempo);
  Buffer.add_string buf (Printf.sprintf "K:%s\n" (pitch_to_string mel.key));
  let notes_per_bar = float_of_int mel.time_signature.beats_per_measure in
  let bar_acc = ref 0.0 in
  let count = ref 0 in
  List.iter (fun event ->
    let dur = match event with
      | Note n -> n.duration | Rest r -> r.rest_duration
      | Chord notes -> (match notes with n :: _ -> n.duration | [] -> 1.0)
    in
    if !bar_acc +. dur > notes_per_bar +. 0.001 then begin
      Buffer.add_string buf " | ";
      bar_acc := 0.0;
      incr count;
      if !count mod 4 = 0 then Buffer.add_char buf '\n'
    end;
    Buffer.add_string buf (event_to_abc event);
    Buffer.add_char buf ' ';
    bar_acc := !bar_acc +. dur
  ) mel.events;
  Buffer.add_string buf " |]\n";
  Buffer.contents buf

(* ==================== Analysis ==================== *)

let melody_range events =
  let midis = List.filter_map (fun e ->
    match e with Note n -> Some (note_to_midi n) | _ -> None
  ) events in
  match midis with
  | [] -> (0, 0)
  | _ ->
    let lo = List.fold_left min 127 midis in
    let hi = List.fold_left max 0 midis in
    (lo, hi)

let total_duration events =
  List.fold_left (fun acc e ->
    acc +. match e with
    | Note n -> n.duration
    | Rest r -> r.rest_duration
    | Chord notes -> (match notes with n :: _ -> n.duration | [] -> 0.0)
  ) 0.0 events

let note_count events =
  List.fold_left (fun acc e ->
    match e with Note _ -> acc + 1 | Chord ns -> acc + List.length ns | _ -> acc
  ) 0 events

let rest_count events =
  List.fold_left (fun acc e ->
    match e with Rest _ -> acc + 1 | _ -> acc
  ) 0 events

let interval_histogram events =
  let midis = List.filter_map (fun e ->
    match e with Note n -> Some (note_to_midi n) | _ -> None
  ) events in
  let rec pairs = function
    | a :: b :: rest -> (b - a) :: pairs (b :: rest)
    | _ -> []
  in
  let intervals = pairs midis in
  let tbl = Hashtbl.create 16 in
  List.iter (fun i ->
    let key = abs i in
    let count = try Hashtbl.find tbl key with Not_found -> 0 in
    Hashtbl.replace tbl key (count + 1)
  ) intervals;
  Hashtbl.fold (fun k v acc -> (k, v) :: acc) tbl []
  |> List.sort (fun (_, a) (_, b) -> compare b a)

(* ==================== Pretty Printing ==================== *)

let print_scale root scale_t =
  let notes = build_scale root scale_t in
  Printf.printf "  %s %s: " (pitch_to_string root) (scale_name scale_t);
  List.iter (fun p -> Printf.printf "%s " (pitch_to_string p)) notes;
  print_newline ()

let print_chord_symbol root quality =
  Printf.printf "%s%s" (pitch_to_string root) (chord_name quality)

let print_progression root scale_t degrees =
  let chords = diatonic_chords root scale_t in
  Printf.printf "  ";
  List.iter (fun deg ->
    let idx = ((deg - 1) mod List.length chords + List.length chords) mod List.length chords in
    let (chord_root, quality) = List.nth chords idx in
    print_chord_symbol chord_root quality;
    Printf.printf "  "
  ) degrees;
  print_newline ()

let print_piano_roll events width =
  let midis = List.filter_map (fun e ->
    match e with Note n -> Some (note_to_midi n, n.duration) | _ -> None
  ) events in
  match midis with
  | [] -> ()
  | _ ->
    let lo = List.fold_left (fun acc (m, _) -> min acc m) 127 midis in
    let hi = List.fold_left (fun acc (m, _) -> max acc m) 0 midis in
    let total = total_duration events in
    for pitch = hi downto lo do
      let note = midi_to_note pitch in
      Printf.printf "  %s%d |" (pitch_to_string note.pitch) note.octave;
      let time = ref 0.0 in
      List.iter (fun e ->
        let col = int_of_float (!time /. total *. float_of_int width) in
        (match e with
        | Note n when note_to_midi n = pitch ->
          let dur_cols = max 1 (int_of_float (n.duration /. total *. float_of_int width)) in
          let padding = col - (int_of_float ((!time -. 0.001) /. total *. float_of_int width)) in
          if padding > 0 then Printf.printf "%s" (String.make padding ' ');
          Printf.printf "%s" (String.make dur_cols '#')
        | _ -> ());
        let d = match e with
          | Note n -> n.duration | Rest r -> r.rest_duration
          | Chord ns -> (match ns with n :: _ -> n.duration | [] -> 0.0)
        in
        time := !time +. d
      ) events;
      print_newline ()
    done

let print_analysis events =
  let (lo, hi) = melody_range events in
  let lo_note = midi_to_note lo in
  let hi_note = midi_to_note hi in
  Printf.printf "  Notes: %d | Rests: %d | Duration: %.1f beats\n"
    (note_count events) (rest_count events) (total_duration events);
  Printf.printf "  Range: %s%d (%d) to %s%d (%d) = %d semitones\n"
    (pitch_to_string lo_note.pitch) lo_note.octave lo
    (pitch_to_string hi_note.pitch) hi_note.octave hi
    (hi - lo);
  let hist = interval_histogram events in
  Printf.printf "  Top intervals: ";
  List.iter (fun (interval, count) ->
    Printf.printf "%dst=%d " interval count
  ) (List.filteri (fun i _ -> i < 5) hist);
  print_newline ()

let print_euclidean pulses steps =
  let rhythm = euclidean_rhythm pulses steps in
  Printf.printf "  E(%d,%d): " pulses steps;
  List.iter (fun hit -> Printf.printf "%s" (if hit then "X" else ".")) rhythm;
  print_newline ()

(* ==================== Demo ==================== *)

let () =
  Printf.printf "╔══════════════════════════════════════════════════════════╗\n";
  Printf.printf "║         🎵 OCaml Algorithmic Music Composer 🎵          ║\n";
  Printf.printf "╚══════════════════════════════════════════════════════════╝\n\n";

  (* Scales *)
  Printf.printf "═══ Scales ═══\n";
  List.iter (fun s -> print_scale C s) [Major; Minor; Blues; PentatonicMinor; Dorian; Lydian];
  print_newline ();

  (* Chords *)
  Printf.printf "═══ Diatonic Chords (C Major) ═══\n";
  let chords = diatonic_chords C Major in
  Printf.printf "  ";
  List.iteri (fun i (root, quality) ->
    Printf.printf "%d:" (i + 1);
    print_chord_symbol root quality;
    Printf.printf "  "
  ) chords;
  print_newline ();
  print_newline ();

  (* Chord Progressions *)
  Printf.printf "═══ Chord Progressions ═══\n";
  List.iter (fun (name, degrees) ->
    Printf.printf "  %-16s → " name;
    let chords = diatonic_chords C Major in
    List.iter (fun deg ->
      let idx = ((deg - 1) mod List.length chords + List.length chords) mod List.length chords in
      let (r, q) = List.nth chords idx in
      print_chord_symbol r q; Printf.printf " "
    ) degrees;
    print_newline ()
  ) progression_patterns;
  print_newline ();

  (* Euclidean Rhythms *)
  Printf.printf "═══ Euclidean Rhythms ═══\n";
  List.iter (fun (p, s) -> print_euclidean p s)
    [(3,8); (4,12); (5,8); (5,16); (7,12); (7,16); (9,16)];
  print_newline ();

  (* Random Walk Melody *)
  Printf.printf "═══ Random Walk Melody (C Minor) ═══\n";
  let walk = generate_random_walk C Minor 16 in
  print_analysis walk;
  Printf.printf "\n  Piano Roll:\n";
  print_piano_roll walk 50;
  let walk_mel = {
    events = walk; tempo = 120;
    time_signature = { beats_per_measure = 4; beat_value = 4 };
    key = C; scale = Minor
  } in
  Printf.printf "\n  ABC Notation:\n%s\n" (melody_to_abc walk_mel "Random Walk in C Minor");

  (* Markov Melody *)
  Printf.printf "═══ Markov Chain Melody (G Major) ═══\n";
  let markov = generate_markov G Major 4 16 in
  print_analysis markov;
  Printf.printf "\n  Piano Roll:\n";
  print_piano_roll markov 50;
  let markov_mel = {
    events = markov; tempo = 100;
    time_signature = { beats_per_measure = 3; beat_value = 4 };
    key = G; scale = Major
  } in
  Printf.printf "\n  ABC Notation:\n%s\n" (melody_to_abc markov_mel "Markov Waltz in G");

  (* L-System Melody *)
  Printf.printf "═══ L-System Melody (D Dorian, 4 iterations) ═══\n";
  let lsys = generate_lsystem D Dorian 4 in
  print_analysis lsys;
  Printf.printf "\n  Piano Roll:\n";
  print_piano_roll lsys 60;
  print_newline ();

  (* Transformations *)
  Printf.printf "═══ Transformations ═══\n";
  let motif = [
    Note { pitch = C; octave = 4; duration = 1.0; velocity = 80 };
    Note { pitch = E; octave = 4; duration = 0.5; velocity = 80 };
    Note { pitch = G; octave = 4; duration = 0.5; velocity = 80 };
    Note { pitch = A; octave = 4; duration = 1.0; velocity = 80 };
  ] in
  Printf.printf "  Original:    ";
  List.iter (fun e -> Printf.printf "%s " (event_to_abc e)) motif;
  print_newline ();
  Printf.printf "  Transposed +5: ";
  List.iter (fun e -> Printf.printf "%s " (event_to_abc e)) (List.map (transpose 5) motif);
  print_newline ();
  Printf.printf "  Retrograde:  ";
  List.iter (fun e -> Printf.printf "%s " (event_to_abc e)) (retrograde motif);
  print_newline ();
  Printf.printf "  Inverted:    ";
  List.iter (fun e -> Printf.printf "%s " (event_to_abc e)) (invert 60 motif);
  print_newline ();
  Printf.printf "  Augmented 2x: ";
  List.iter (fun e -> Printf.printf "%s " (event_to_abc e)) (augment 2.0 motif);
  print_newline ();
  print_newline ();

  (* Chord Progression with melody *)
  Printf.printf "═══ Full Composition: Blues in A ═══\n";
  let blues_prog = build_progression A Major [1;1;1;1;4;4;1;1;5;4;1;5] 3 4.0 in
  let blues_melody = generate_markov A Blues 4 48 in
  let blues = {
    events = blues_melody;
    tempo = 110;
    time_signature = { beats_per_measure = 4; beat_value = 4 };
    key = A; scale = Blues
  } in
  Printf.printf "  Progression: ";
  List.iter (fun e -> Printf.printf "%s " (event_to_abc e)) blues_prog;
  print_newline ();
  Printf.printf "\n  Melody Analysis:\n";
  print_analysis blues_melody;
  Printf.printf "\n  ABC Notation:\n%s\n" (melody_to_abc blues "12-Bar Blues in A");

  Printf.printf "═══════════════════════════════════════════════════════════\n";
  Printf.printf "  Features: scales, chords, progressions, Euclidean rhythms,\n";
  Printf.printf "  random walk / Markov / L-system generators, transformations\n";
  Printf.printf "  (transpose, retrograde, invert, augment), piano roll display,\n";
  Printf.printf "  interval analysis, and ABC notation export.\n";
  Printf.printf "═══════════════════════════════════════════════════════════\n"
