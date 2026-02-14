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
| Pattern matching | `list_last_elem.ml`, `bst.ml`, `factor.ml` |
| Option types | `list_last_elem.ml`, `bst.ml` |
| Recursion | All files |
| Tail recursion | `mergesort.ml`, `fibonacci.ml` |
| Algebraic data types | `bst.ml` |
| Polymorphism (`'a`) | `bst.ml`, `mergesort.ml` |
| Higher-order functions | `mergesort.ml`, `hello.ml` |
| Pipe operator (`\|>`) | `hello.ml` |
| Hash tables & mutability | `fibonacci.ml` |
| Closures | `fibonacci.ml` |
| Accumulators | `bst.ml`, `mergesort.ml` |
| Input validation | `factor.ml` |
| Mutual recursion | `factor.ml` |
| Benchmarking | `fibonacci.ml` |
