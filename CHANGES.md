# Changelog

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
