# Theo

Theo is a high-performance **Binary Decision Diagram (BDD)** library for OCaml. It provides efficient boolean logic manipulation with support for theory reasoning over **linear orders and equality** (including booleans, strings, integers, and semantic versions).

## Documentation

The API documentation is available online at: [https://vouillon.github.io/theo/theo/Theo/](https://vouillon.github.io/theo/theo/Theo/)

## Features

*   **Generic Theory Support**: Create BDDs for any domain by implementing the `Theory` interface.
*   **Combinators**: Easily combine multiple theories (e.g., `String + Version`) using the `Combine` functor.
*   **Core BDD Operations**: AND, OR, NOT, IMPLIES, EQUIV, XOR, quantifiers (`exists`/`forall`).
*   **Optimization**:
    *   Hash-consing for structural sharing.
    *   Efficient `restrict` operations for partial evaluation.
    *   Negative edge optimizations (canonical form).
*   **Introspection**: Inspect and pattern match on constraints.
*   **Verification**: Comprehensive test suite including property-based fuzzing.

## Installation

### Prerequisites

*   OCaml >= 4.08
*   Dune >= 3.17

### Building from Source

```bash
git clone https://github.com/yourusername/theo.git
cd theo
dune build
```

### Installing via Opam

To install the library and its dependencies:

```bash
opam install .
```

### Running Tests

```bash
dune runtest
```

## Architecture

The library is built around a few core concepts:

- `Make`: The core BDD engine functor. It takes a `Theory` as input and produces a BDD module.
- `Theory`: An interface for values that can be part of the BDD.
- `Combine`: A functor to combine two theories into one sum theory.
- `Primitive_theory`: Standard theories builders like `Leq` (linear order) and `Eq` (equality).

## Usage

### 1. Simple Boolean Logic

Use `Theo.Void` for standard BDDs without extra theories.

```ocaml
module BDD = Theo.Make(Theo.Void)
let open BDD.Syntax

let () =
  let x = BDD.var () in
  let y = BDD.var () in

  (* Construct expressions *)
  let expr = (BDD.bool x) && (not (BDD.bool y)) in

  (* Check tautology/satisfiability *)
  let is_sat = BDD.is_satisfiable expr in (* true *)
  let is_taut = BDD.is_tautology expr in   (* false *)
  Printf.printf "Sat: %b\n" is_sat
```

### 2. Combining Theories

You can combine multiple theories (e.g., String equality and Version comparisons) in the same BDD.

```ocaml
(* 1. Define your atomic types *)
module StringAtom = struct 
  include String 
  let to_string s = s 
  let hash = Hashtbl.hash 
end
module VersionAtom = struct 
  type t = { major: int; minor: int; patch: int }
  let compare = compare
  let equal = (=)
  let hash = Hashtbl.hash
  let to_string v = Printf.sprintf "%d.%d.%d" v.major v.minor v.patch
end

(* 2. Instantiate primitive theories *)
module StringEq = Theo.Eq(StringAtom)
module VersionLeq = Theo.Leq(VersionAtom)

(* 3. Combine them into a single theory *)
module MyTheory = Theo.Combine(VersionLeq)(StringEq)

(* 4. Create the BDD module *)
module MyBDD = Theo.Make(MyTheory)

(* 5. Instantiate syntax helpers for convenient construction *)
module V = VersionLeq.Syntax(MyTheory.Left(MyBDD))
module S = StringEq.Syntax(MyTheory.Right(MyBDD))

let () =
  (* 6. Now you can mix them! *)
  let v_var = MyBDD.var () in
  let s_var = MyBDD.var () in
  
  let v = { VersionAtom.major = 1; minor = 0; patch = 0 } in
  let s = "production" in
  
  (* Use infix operators: V.(...) and S.(...) *)
  let expr = MyBDD.and_ V.(v_var < v) S.(s_var = s) in
  (* "Version < 1.0.0 AND String = 'production'" *)
  ()
```

### 3. Working with Constraints

You can build constraints for `restrict` or inspect them using pattern matching.

```ocaml
(* 1. Build constraint syntax helpers *)
(* Pass MyBDD.Constraint instead of MyBDD *)
module V_cstr = VersionLeq.Syntax(MyTheory.Left(MyBDD.Constraint))
module S_cstr = StringEq.Syntax(MyTheory.Right(MyBDD.Constraint))

let () =
  (* 2. Create constraints *)
  let c1 = V_cstr.(v_var < v) in 
  
  (* 3. Restrict a BDD *)
  (* assert that v < 1.0.0 *)
  let restricted_expr = MyBDD.restrict expr c1 in
  
  (* 4. Introspection *)
  let match_constraint (c : MyBDD.atomic_constraint) =
    match MyBDD.view_constraint c with
    | MyBDD.Constraint { var; payload = Bool; value } ->
        Printf.printf "Bool var %b" value
    | MyBDD.Constraint { var; payload = Theory desc; value } ->
        match desc with
        | MyTheory.Left (VersionLeq.Bound { limit; inclusive }) ->
            Printf.printf "Version <= %s is %b" (VersionAtom.to_string limit) value
        | MyTheory.Right (StringEq.Const s) ->
            Printf.printf "String = %s is %b" s value
  in 
  ()
```

## Project Structure

*   `src/lib-theo/`: Core library implementation.
    *   `theo.ml`: Main BDD engine and theory functors.
    *   `theo.mli`: Public API documentation.
*   `test/`: Unit tests, properties, and benchmarks.

## License

MIT License.
