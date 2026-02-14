# OCaml Sample Code

A collection of small OCaml programs demonstrating core language features.

## Programs

| File | Description |
|------|-------------|
| `a.ml` | Hello world — basic output with `print_endline` |
| `b.ml` | Second hello world example |
| `factor.ml` | Prime factorization using recursive trial division |
| `list_last_elem.ml` | Find the last element of a list using pattern matching |
| `bst.ml` | Binary search tree with algebraic data types and pattern matching (insert, delete, member, min/max, size, depth) |
| `mergesort.ml` | Merge sort using higher-order functions and list splitting |

## Building & Running

Requires [OCaml](https://ocaml.org/) installed on your system.

### Using Make

```bash
# Build all programs
make

# Build and run all programs
make run

# Clean build artifacts
make clean
```

### Manual

```bash
# Compile and run a single file
ocamlopt -o factor factor.ml && ./factor

# Or use the OCaml toplevel (REPL)
ocaml
# then: #use "factor.ml";;
```

## Examples

### Prime Factorization (`factor.ml`)

```ocaml
(* factors 12 returns [2; 2; 3] *)
let factors n =
  let rec aux d n =
    if n = 1 then [] else
      if n mod d = 0 then d :: aux d (n / d) else aux (d+1) n
  in
  aux 2 n;;
```

### Last Element of a List (`list_last_elem.ml`)

```ocaml
(* last [1; 2; 3] returns Some 3 *)
let rec last = function
  | [] -> None
  | [x] -> Some x
  | _ :: t -> last t;;
```

### Binary Search Tree (`bst.ml`)

```ocaml
type 'a tree =
  | Leaf
  | Node of 'a tree * 'a * 'a tree

let rec insert x = function
  | Leaf -> Node (Leaf, x, Leaf)
  | Node (left, v, right) ->
    if x < v then Node (insert x left, v, right)
    else if x > v then Node (left, v, insert x right)
    else Node (left, v, right)
```

### Merge Sort (`mergesort.ml`)

```ocaml
(* Parameterized by a comparison function for flexibility *)
let rec mergesort cmp = function
  | ([] | [_]) as l -> l
  | lst ->
    let (left, right) = split lst in
    merge cmp (mergesort cmp left) (mergesort cmp right)

(* Sort ascending or descending by swapping the comparator *)
mergesort compare [38; 27; 43; 3; 9; 82; 10]
(* => [3; 9; 10; 27; 38; 43; 82] *)
```

## License

MIT License — see [LICENSE](LICENSE) for details.
