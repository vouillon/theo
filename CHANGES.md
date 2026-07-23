# Changelog

## Unreleased

- Add a Monolith-based fuzzing harness (`fuzz/`) that tests Theo against a
  trusted truth-table reference model over arbitrary sequences of API calls
  (optionally driven by afl-fuzz), targeting history-dependence bugs through the
  shared hash-consing tables and memo caches. The reference model lives in a
  shared `theo_test_support` library and is unit-tested against Theo by
  `test/test_model.ml`. `monolith` is a dev-only dependency; `dune build` and
  `dune runtest` remain green without it. A second pass adds the `and_list` /
  `or_list` batch operations to the vocabulary and a `shortest_sat` length check
  (`length(shortest_sat f) <= length(sat f)`, since the documented shortest BDD
  path is not the semantically minimal cube).
- Fix warning 8 (partial-match) on OCaml >= 5.5: define the `positive` and
  `negative` phantom types as private polymorphic variant abbreviations, since
  the exhaustiveness checker no longer assumes abstract types are distinct
- Pin the ocamlformat version to 0.29.0
- Fix type-safety hole: `bool` and `Constraint.bool` now require a
  `bool Var.t`, so a theory variable can no longer double as a boolean atom
  (which produced incorrect `restrict` results)
- Fix `of_cube`/`sop_to_bdd` on constraints built through the `Constraint`
  module: atoms are now re-interned, preserving the hash-consing invariant
- Fix the error message of `Constraint.or_`
- Re-export `Var` from `Make` as `MyBDD.Var`
- Fix the code examples in the documentation and compile them as part of the
  test suite (`test/doc_examples.ml`)
- Document that the library is not thread-safe
- Add a CI workflow building and testing on OCaml 4.14 and 5.5

## 0.1.0 (2026-07-16)

Initial release.

- Core BDD engine with hash-consing and canonical negative-edge form
- Boolean operations: AND, OR, NOT, IMPLIES, EQUIV, XOR, and `exists`/`forall` quantifiers
- Pluggable theory support over linear orders and equality (booleans, strings,
  integers, semantic versions), with a `Combine` functor to mix theories
- `restrict` operation for partial evaluation, and constraint introspection via
  pattern matching
- Irredundant sum-of-products (Minato-Morreale) computation
- Property-based test suite
