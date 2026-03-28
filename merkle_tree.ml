(* ============================================================
   Merkle Tree — Cryptographic Hash Trees in OCaml
   ============================================================

   A Merkle tree is a binary tree of hashes used for efficient and
   secure verification of data integrity. Each leaf holds the hash
   of a data block; each internal node holds the hash of its two
   children concatenated. This enables O(log n) membership proofs.

   Features:
   - Build a Merkle tree from a list of data blocks
   - Compute the root hash (fingerprint of all data)
   - Generate inclusion proofs (audit paths)
   - Verify proofs against a root hash
   - Pretty-print the tree structure
   - Supports arbitrary hash functions (default: simple DJB2)

   Usage:
     ocamlfind ocamlopt -package str -linkpkg merkle_tree.ml -o merkle_tree
     ./merkle_tree

   Or interpreted:
     ocaml merkle_tree.ml
   ============================================================ *)

(* --- Hash function -------------------------------------------------- *)

(** DJB2 hash → hex string. Simple, deterministic, no dependencies. *)
let djb2_hash (s : string) : string =
  let h = ref 5381 in
  String.iter (fun c -> h := !h * 33 + Char.code c) s;
  (* Mask to 32-bit unsigned *)
  let u = Int32.logand (Int32.of_int !h) 0xFFFF_FFFFl in
  Printf.sprintf "%08lx" u

(* Pluggable hasher – default DJB2; swap in SHA-256 etc. if desired *)
let hash_fn = ref djb2_hash

let set_hash_function f = hash_fn := f

let hash s = !hash_fn s

(* --- Tree type ------------------------------------------------------ *)

type tree =
  | Leaf of { data : string; hash : string }
  | Node of { left : tree; right : tree; hash : string }

(* --- Build ---------------------------------------------------------- *)

let make_leaf data =
  Leaf { data; hash = hash data }

(** Pad the list to the next power-of-two length by duplicating the
    last element (standard Merkle tree convention). *)
let rec next_pow2 n =
  if n <= 1 then 1
  else
    let p = ref 1 in
    while !p < n do p := !p * 2 done;
    !p

let pad_to_pow2 lst =
  match lst with
  | [] -> []
  | _ ->
    let len = List.length lst in
    let target = next_pow2 len in
    let last = List.nth lst (len - 1) in
    lst @ List.init (target - len) (fun _ -> last)

(** Build tree bottom-up from a list of leaves. *)
let build (blocks : string list) : tree option =
  match blocks with
  | [] -> None
  | _ ->
    let padded = pad_to_pow2 blocks in
    let leaves = List.map make_leaf padded in
    let rec combine = function
      | [t] -> t
      | nodes ->
        let rec pairs = function
          | [] -> []
          | [x] -> [x]  (* shouldn't happen after padding *)
          | a :: b :: rest ->
            let h = hash (root_hash a ^ root_hash b) in
            Node { left = a; right = b; hash = h } :: pairs rest
        in
        combine (pairs nodes)
    in
    Some (combine leaves)

and root_hash = function
  | Leaf { hash; _ } -> hash
  | Node { hash; _ } -> hash

(* --- Root hash convenience ------------------------------------------ *)

let root t = root_hash t

(* --- Inclusion proof ------------------------------------------------ *)

type direction = Left | Right

type proof_step = {
  direction : direction;
  sibling_hash : string;
}

type proof = proof_step list

(** Generate a proof that [target_data] is in the tree. Returns None if
    the data is not present. *)
let prove (t : tree) (target_data : string) : proof option =
  let target_hash = hash target_data in
  let rec go = function
    | Leaf { hash; _ } ->
      if hash = target_hash then Some []
      else None
    | Node { left; right; _ } ->
      (match go left with
       | Some path ->
         Some (path @ [{ direction = Left; sibling_hash = root_hash right }])
       | None ->
         match go right with
         | Some path ->
           Some (path @ [{ direction = Right; sibling_hash = root_hash left }])
         | None -> None)
  in
  go t

(** Verify a proof against an expected root hash. *)
let verify ~(root_hash_expected : string) ~(data : string) (proof : proof) : bool =
  let current = ref (hash data) in
  List.iter (fun step ->
    match step.direction with
    | Left  -> current := hash (!current ^ step.sibling_hash)
    | Right -> current := hash (step.sibling_hash ^ !current)
  ) proof;
  !current = root_hash_expected

(* --- Pretty print --------------------------------------------------- *)

let rec pp_tree indent = function
  | Leaf { data; hash } ->
    Printf.printf "%s🍃 \"%s\" [%s]\n" indent data hash
  | Node { left; right; hash } ->
    Printf.printf "%s🔗 [%s]\n" indent hash;
    pp_tree (indent ^ "  ├─") left;
    pp_tree (indent ^ "  └─") right

let print_tree t = pp_tree "" t

(* --- Tree stats ----------------------------------------------------- *)

let rec depth = function
  | Leaf _ -> 0
  | Node { left; _ } -> 1 + depth left

let rec leaf_count = function
  | Leaf _ -> 1
  | Node { left; right; _ } -> leaf_count left + leaf_count right

(* --- Diff: find which leaves differ between two trees --------------- *)

let rec diff t1 t2 =
  match t1, t2 with
  | Leaf l1, Leaf l2 ->
    if l1.hash = l2.hash then []
    else [(l1.data, l2.data)]
  | Node n1, Node n2 ->
    if n1.hash = n2.hash then []  (* subtree identical — skip *)
    else diff n1.left n2.left @ diff n1.right n2.right
  | _ -> [("<structure mismatch>", "<structure mismatch>")]

(* === Demo =========================================================== *)

let () =
  Printf.printf "═══════════════════════════════════════════\n";
  Printf.printf "  Merkle Tree — OCaml Implementation\n";
  Printf.printf "═══════════════════════════════════════════\n\n";

  (* Build a tree *)
  let blocks = ["alpha"; "bravo"; "charlie"; "delta"; "echo"] in
  Printf.printf "📦 Data blocks: [%s]\n\n"
    (String.concat "; " (List.map (Printf.sprintf "\"%s\"") blocks));

  match build blocks with
  | None -> Printf.printf "No data!\n"
  | Some tree ->
    Printf.printf "🌳 Tree structure:\n";
    print_tree tree;
    Printf.printf "\n🔑 Root hash: %s\n" (root tree);
    Printf.printf "📊 Depth: %d  |  Leaves: %d\n\n" (depth tree) (leaf_count tree);

    (* Prove membership *)
    let target = "charlie" in
    Printf.printf "🔍 Proving \"%s\" is in the tree...\n" target;
    (match prove tree target with
     | None -> Printf.printf "   ❌ Not found!\n"
     | Some proof ->
       Printf.printf "   ✅ Proof generated (%d steps)\n" (List.length proof);
       List.iteri (fun i step ->
         let dir = match step.direction with Left -> "←" | Right -> "→" in
         Printf.printf "      Step %d: %s sibling=%s\n" (i+1) dir step.sibling_hash
       ) proof;

       (* Verify *)
       let valid = verify ~root_hash_expected:(root tree) ~data:target proof in
       Printf.printf "   🔐 Verification: %s\n\n"
         (if valid then "PASS ✓" else "FAIL ✗"));

    (* Tamper detection *)
    Printf.printf "🛡️  Tamper detection demo:\n";
    let tampered = List.map (fun b -> if b = "charlie" then "TAMPERED" else b) blocks in
    (match build tampered with
     | None -> ()
     | Some tree2 ->
       Printf.printf "   Original root:  %s\n" (root tree);
       Printf.printf "   Tampered root:  %s\n" (root tree2);
       Printf.printf "   Roots match: %b\n\n" (root tree = root tree2);

       (* Diff *)
       let diffs = diff tree tree2 in
       Printf.printf "   Changed blocks:\n";
       List.iter (fun (a, b) ->
         Printf.printf "     \"%s\" → \"%s\"\n" a b
       ) diffs);

    Printf.printf "\n═══════════════════════════════════════════\n";
    Printf.printf "  Done! Merkle trees enable O(log n)\n";
    Printf.printf "  integrity proofs — used in Git,\n";
    Printf.printf "  blockchains, and certificate transparency.\n";
    Printf.printf "═══════════════════════════════════════════\n"
