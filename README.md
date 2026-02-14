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

## Building & Running

Requires [OCaml](https://ocaml.org/) installed on your system.

```bash
# Compile and run a file
ocamlfind ocamlc -o factor factor.ml && ./factor

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

## License

MIT License — see [LICENSE](LICENSE) for details.
