# Changelog

## Unreleased

- Performance:
  - `restrict` and `exists`/`forall` no longer allocate a 1024-bucket table
    on every call: 15-20x faster on small formulas
  - `restrict` checks the consistency of 2 to 5 constraints pairwise instead
    of building a constraint store: 2x faster on such lists
  - `irredundant_sop` post-processing is linear in the number of cubes
    instead of quadratic (13x faster on an 831-cube cover); the covers are
    unchanged
  - The memoization caches look up each key once instead of twice on a miss,
    and the AND cache keeps all four polarity combinations of a pair in one
    cell (8% faster on 8-queens)
- Fix `print_dot`: escape atom labels, so that a theory whose `to_string`
  produces quotes or backslashes (e.g. strings printed with `%S`) no longer
  yields invalid DOT; and draw low edges dashed, so that they can be told
  apart from high edges, marking negated edges with an `odot` arrowhead
  instead (both used to be solid, and dashed meant negated)
- Fix unsound results with `Combine (A) (A)` (or any `Combine` whose two
  sides share a theory instance, so that one variable can carry atoms of
  both): atoms from different sides were reasoned about as one ordered
  theory, e.g. `Left (v < 5)` was taken to entail `Right (v < 3)`. Atoms
  from different sides are now independent. The low-level `atom` functions
  must now be reached through `Combine`'s `Left`/`Right` lifts (as the
  syntax modules do), since these record which side an atom comes from
- Fuzzing: start every Monolith scenario from a pristine state, which takes
  afl's stability from 64% to 99.8% (the remaining 0.2% is the framework's
  first iteration). The harness prologue calls a new undocumented
  `Make.reset_state` -- which empties the hash-consing tables and caches and
  rewinds the atom/node identifier counters -- followed by `Gc.full_major`,
  needed because the caches are ephemerons and the hash-consing tables weak.
  See `fuzz/README.md` for the measurements. The hash-consing tables now live
  in a reference so that they can be replaced rather than cleared in place.
- CI: run the fuzzing harness in random mode for 60 s on every push/PR, and
  weekly (or on demand) under afl++ with the corpus persisted between runs

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
