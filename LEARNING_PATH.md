# 📚 Learning Path

A guided order for studying the examples in this repository. Each file builds on concepts from the previous ones.

## Stage 1: Foundations

### [`hello.ml`](hello.ml) — Start Here

**Concepts:** `let` bindings, type inference, `Printf`, string concatenation, pipe operator (`|>`)

OCaml infers types without annotations. The pipe operator chains transformations left-to-right, making data pipelines readable:

```ocaml
[1; 2; 3; 4; 5]
|> List.filter (fun x -> x mod 2 = 0)   (* keep evens *)
|> List.map (fun x -> x * x)             (* square them *)
|> List.fold_left (+) 0                   (* sum *)
(* Result: 20 *)
```

**Key takeaway:** OCaml code reads like math. No semicolons, no type declarations, no `return` keyword.

---

## Stage 2: Core Patterns

### [`list_last_elem.ml`](list_last_elem.ml) — Safe List Traversal

**Concepts:** `option` types, pattern matching, recursion

OCaml uses `Option` instead of null. This function never crashes — it returns `None` for empty lists and `Some x` for the last element:

```ocaml
let rec last = function
  | [] -> None
  | [x] -> Some x
  | _ :: t -> last t
```

**Key takeaway:** Pattern matching replaces `if/else` chains and is exhaustive — the compiler warns if you miss a case.

### [`factor.ml`](factor.ml) — Recursive Algorithms

**Concepts:** recursion, mutual recursion (`and`), input validation (`invalid_arg`)

Builds on recursion from `list_last_elem.ml`. Introduces mutually recursive functions (`extract_twos` and `odd_factors` defined with `and`) and shows how OCaml handles errors without exceptions in the happy path.

**Key takeaway:** Mutual recursion with `let rec ... and ...` is a natural way to express multi-phase algorithms.

---

## Stage 3: Data Structures

### [`bst.ml`](bst.ml) — Algebraic Data Types

**Concepts:** variant types, polymorphism (`'a`), structural recursion, accumulators

This is where OCaml shines. Algebraic data types let you model tree structures in 3 lines:

```ocaml
type 'a tree =
  | Leaf
  | Node of 'a tree * 'a * 'a tree
```

The `'a` means the tree works with any type — integers, strings, custom records. Pattern matching on trees feels natural.

**Key takeaway:** Algebraic data types + pattern matching = elegant data structure code. The accumulator pattern in `inorder` converts O(n²) to O(n).

---

## Stage 4: Higher-Order Functions

### [`mergesort.ml`](mergesort.ml) — Functions as Arguments

**Concepts:** higher-order functions, polymorphism, tail recursion, tuple destructuring

The sort function takes a comparison function as a parameter — sort ascending, descending, or by any custom criteria:

```ocaml
mergesort compare data           (* ascending *)
mergesort (fun a b -> compare b a) data  (* descending *)
mergesort String.compare words   (* strings! *)
```

Both `split` and `merge` are tail-recursive to handle large inputs without stack overflow.

**Key takeaway:** Passing functions as arguments makes code reusable. Tail recursion makes it production-ready.

---

## Stage 5: Imperative OCaml

### [`fibonacci.ml`](fibonacci.ml) — Mutable State When You Need It

**Concepts:** hash tables (`Hashtbl`), closures, memoization, `Sys.time` benchmarking

OCaml is primarily functional, but supports mutable state. The memoized Fibonacci uses a closure over a hash table — the cache persists between calls but is invisible to the outside world:

```ocaml
let fib_memo =
  let cache = Hashtbl.create 64 in
  let rec fib n = ...
  in fib  (* only the function escapes; cache is private *)
```

Compares three approaches: naive (exponential), memoized (linear), and iterative (constant space). Demonstrates that choosing the right approach matters more than micro-optimization.

**Key takeaway:** OCaml lets you use mutable state locally while keeping your public API pure. Closures are a powerful encapsulation mechanism.

---

## Stage 6: Modules & Graph Algorithms

### [`graph.ml`](graph.ml) — Modules, Records, and Classic Algorithms

**Concepts:** functor-generated modules (`Map.Make`, `Set.Make`), record types, imperative queues (`Queue`), BFS, DFS, topological sort, cycle detection

This example brings together everything from earlier stages. It uses OCaml's `Map.Make` functor to create a type-safe adjacency list, records for structured data, and both functional recursion and imperative queues:

```ocaml
module IntMap = Map.Make(Int)

type graph = {
  adj: int list IntMap.t;
  directed: bool;
}
```

BFS uses `Queue` for O(1) operations; DFS uses natural recursion. Cycle detection uses a 3-color scheme (White/Gray/Black) — a `Gray` back-edge means a cycle. Topological sort uses Kahn's in-degree algorithm.

**Key takeaway:** OCaml modules and functors let you build type-safe abstractions. Real-world OCaml combines functional and imperative styles — use whichever fits the algorithm.

---

## Stage 7: Persistent Data Structures

### [`heap.ml`](heap.ml) — Purely Functional Priority Queue

**Concepts:** rank-annotated algebraic data types, persistent (immutable) data structures, merge-based design, custom comparators, bottom-up construction

A leftist heap is a priority queue where every operation creates a new heap — the original is preserved. This is "persistence" — a hallmark of functional programming. The key insight is that **everything is built on `merge`**:

```ocaml
type 'a heap =
  | Empty
  | Node of int * 'a * 'a heap * 'a heap

let rec merge cmp h1 h2 =
  match h1, h2 with
  | Empty, h | h, Empty -> h
  | Node (_, x, a1, b1), Node (_, y, _, _) ->
    if cmp x y <= 0 then make_node x a1 (merge cmp b1 h2)
    else merge cmp h2 h1
```

Insert is `merge` with a singleton. Delete-min is `merge` of the two children. The "rank" annotation keeps the right spine short (O(log n)), guaranteeing efficient operations.

Also demonstrates bottom-up O(n) heap construction via pairwise merging, heap sort, and top-k extraction.

**Key takeaway:** Persistent data structures let you "undo" operations for free — the old version still exists. The merge-based design pattern shows how one well-designed operation can power an entire API.

---

## Stage 8: Tries & String Algorithms

### [`trie.ml`](trie.ml) — Prefix Tree for String Storage

**Concepts:** `Map.Make` functor (character-indexed children), recursive record types, persistence, string-to-char-list conversion, tree pruning, prefix-based retrieval

A trie stores strings as paths through a tree where each edge is a character. Words sharing prefixes share nodes — making prefix search and auto-complete natural O(m) operations (m = query length). Like the heap, every operation returns a new trie — the original is preserved.

```ocaml
module CharMap = Map.Make(Char)

type trie = {
  is_word: bool;               (* does a word end at this node? *)
  children: trie CharMap.t;    (* children keyed by character *)
}
```

The `CharMap` (created via `Map.Make(Char)`) gives us sorted character keys for free — `all_words` returns results in lexicographic order without explicit sorting. Deletion prunes dead-end nodes automatically.

Key operations: `insert`, `member`, `delete`, `has_prefix`, `words_with_prefix` (auto-complete), `longest_common_prefix`, ASCII visualization.

**Key takeaway:** Choosing the right data structure turns hard problems into simple ones. Prefix search in a trie is trivial — just navigate to the prefix node and collect descendants. The `Map.Make` functor pattern for character-indexed children is reusable for any alphabet.

---

## Stage 9: Parser Combinators

### [`parser.ml`](parser.ml) — Building Parsers from Small Pieces

**Concepts:** higher-order functions (functions returning functions), closures, monadic bind (`>>=`), function composition, recursive descent, operator precedence, algebraic data types for ASTs

Parser combinators are *the* quintessential functional programming pattern. Each parser is a function; you build complex parsers by combining simple ones with operators:

```ocaml
type 'a parser = string -> int -> 'a result

(* Monadic bind: sequence two parsers *)
let bind p f = fun input pos ->
  match p input pos with
  | Error _ as e -> e
  | Ok (a, pos') -> (f a) input pos'
```

The library includes 15+ combinators (`bind`, `map`, `choice`, `many`, `sep_by`, `between`, `chainl1`, `chainr1`, etc.) and three complete parsers:

- **Arithmetic expressions** with correct operator precedence (`+`, `-`, `*`, `/`, `^`, parentheses)
- **Integer lists** (`[1, 2, 3]`)
- **Key-value pairs** (`name = "Alice", age = "30"`)

The expression parser demonstrates how layered grammar rules naturally encode precedence:

```ocaml
let expr  = chainl1 term  add_op   (* lowest: + - *)
let term  = chainl1 power mul_op   (* middle: * / *)
let power = chainr1 atom  pow_op   (* highest: ^  *)
let atom  = integer <|> parens     (* base cases *)
```

**Key takeaway:** Monadic composition (`>>=`) is the most powerful functional pattern — it lets you thread state (parse position) through a chain of operations while keeping each step independent and composable. The same pattern appears in I/O, error handling, async programming, and more.

---

## What's Next?

After working through these examples, try:

1. **Modify an example** — Add `find` to the BST, or make merge sort stable
2. **Write a new one** — Implement a stack, queue, or graph traversal
3. **Read the manual** — [OCaml.org docs](https://ocaml.org/docs) cover modules, functors, and the standard library
4. **Try Real World OCaml** — [dev.realworldocaml.org](https://dev.realworldocaml.org/) for production patterns

## Concept Index

| Concept | Files |
|---------|-------|
| Let bindings & type inference | `hello.ml` |
| Pattern matching | `list_last_elem.ml`, `bst.ml`, `factor.ml`, `graph.ml` |
| Option types | `list_last_elem.ml`, `bst.ml`, `graph.ml` |
| Recursion | All files |
| Tail recursion | `mergesort.ml`, `fibonacci.ml` |
| Algebraic data types | `bst.ml`, `graph.ml`, `heap.ml`, `parser.ml` |
| Polymorphism (`'a`) | `bst.ml`, `mergesort.ml`, `heap.ml`, `parser.ml` |
| Higher-order functions | `mergesort.ml`, `hello.ml`, `heap.ml`, `parser.ml` |
| Pipe operator (`\|>`) | `hello.ml` |
| Hash tables & mutability | `fibonacci.ml`, `graph.ml` |
| Closures | `fibonacci.ml`, `parser.ml` |
| Accumulators | `bst.ml`, `mergesort.ml` |
| Input validation | `factor.ml` |
| Mutual recursion | `factor.ml` |
| Benchmarking | `fibonacci.ml` |
| Modules & functors | `graph.ml`, `trie.ml` |
| Record types | `graph.ml`, `trie.ml` |
| Imperative queues | `graph.ml` |
| Graph algorithms (BFS/DFS) | `graph.ml` |
| Persistent data structures | `heap.ml`, `trie.ml` |
| Priority queues / heaps | `heap.ml` |
| Custom comparators | `mergesort.ml`, `heap.ml` |
| Monadic composition (bind) | `parser.ml` |
| Parser combinators | `parser.ml` |
| Recursive descent parsing | `parser.ml` |
| Operator precedence | `parser.ml` |
| Tries & prefix search | `trie.ml` |
| String manipulation | `trie.ml` |
| Tree pruning | `trie.ml` |
