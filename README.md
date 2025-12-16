# Theo

Theo is a high-performance **Boolean Decision Diagram (BDD)** library for OCaml. It provides efficient boolean logic manipulation with support for advanced atomic constraints, including strings and version number comparisons.

> [!NOTE]
> **Work in Progress**: This library is currently in early development and has not been released yet. The theory extension mechanism (Strings, Versions) is currently hardcoded but is planned to be made pluggable in future versions.

## Features

*   **Core BDD Operations**: AND, OR, NOT, IMPLIES, EQUIV, XOR.
*   **Rich Atom Support**:
    *   **Booleans**: Standard boolean variables.
    *   **Strings**: Equality `(=)` and Inequality `(!=)` constraints.
    *   **Versions**: Semantic version comparisons (`<`, `<=`, `>`, `>=`) using `{ major; minor; patch }`.
*   **Optimization**:
    *   Hash-consing for structural sharing.
    *   Efficient `restrict` operations for partial evaluation.
    *   Negative edge optimizations (canonical form with positive `low` branches).
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

## Usage

### Basic Boolean Logic

```ocaml
open Theo.Syntax (* Operators like &&, ||, not *)

let () =
  let x = Theo.var Boolean in
  let y = Theo.var Boolean in
  
  (* Construct expressions *)
  let expr = (atom x) && (not (atom y)) in
  
  (* Check tautology/satisfiability *)
  let is_sat = is_satisfiable expr in (* true *)
  let is_taut = is_tautology expr in   (* false *)
  ()
```

### Advanced Constraints (Versions)

```ocaml
let () =
  let v = Theo.var Version in
  
  (* Define a version constraint: v < 2.0.0 *)
  let v_lt_2 = v < { major=2; minor=0; patch=0 } in
  
  (* Define another: v >= 1.5.0 *)
  let v_ge_1_5 = v >= { major=1; minor=5; patch=0 } in
  
  (* Combine: 1.5.0 <= v < 2.0.0 *)
  let valid_range = v_lt_2 && v_ge_1_5 in
  
  (* Restrict with specific constraint *)
  let constraints = [ Version(v, `Lt, { major=1; minor=0; patch=0 }) ] in
  let res = restrict valid_range constraints in
  (* res should be FALSE because range 1.5-2.0 is disjoint from v < 1.0 *)
  ()
```

## Project Structure

*   `src/lib-theo/`: Core library implementation (`theo.ml`).
*   `test/`: Unit tests and benchmarks.

## License

MIT License.
