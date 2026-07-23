# Monolith fuzzing harness for Theo

This directory contains a [Monolith](https://gitlab.inria.fr/fpottier/monolith)
harness that tests Theo against a trusted reference implementation over
*arbitrary sequences of API calls*, optionally driven by `afl-fuzz` for
coverage-guided input generation.

It targets the main blind spot of the QCheck suite in `test/`: **history
dependence through the hash-consing tables and memo caches**. Each QCheck
property builds a fresh expression and checks one thing, so it cannot exercise
the way one operation's cache entries affect a later one. Monolith generates
well-typed call sequences over a *single shared BDD instance* — exactly the
traffic that surfaces cache-interaction bugs — and prints a minimal reproducing
scenario as OCaml code when it finds one.

## Files

- `main.ml` — the Monolith spec: declares the BDD type as an abstract type and
  pairs every operation with its reference implementation.
- `../test/support/model.ml` — the reference implementation (`Model`): formulas
  as truth tables over a finite set of worlds, with every semantic question
  answered by enumeration. It lives in the shared `theo_test_support` library so
  that `test/test_model.ml` can unit-test it against Theo **without** requiring
  monolith (see "Trusting the model" below).
- `Makefile` — includes Monolith's demo Makefile (afl workflow + `random`).

## Requirements

`monolith` is **not** a `with-test` dependency of the package: `dune build` and
`dune build @runtest` work without it, and the harness executable is marked
`(optional)` so dune silently skips it when monolith is absent. In the opam
metadata monolith is declared `{with-dev-setup}`.

To build and run the harness, install monolith in your switch:

```
opam install monolith
```

## Running

### Random mode (smoke test, no afl)

The quickest way — runs on your current switch, feeding the harness from
`/dev/urandom`. Good for a ~60 s smoke test:

```
dune exec fuzz/main.exe -- --timeout 60
```

Useful flags (see `Monolith.mli`): `--fuel N` (max scenario length, default 15),
`--max-scenarios N`, `--timeout SECONDS`, `--show-scenario false`,
`--save-scenario false`. With saving on (the default), discovered scenarios are
written under `fuzz/output/crashes/` in human-readable form. Exit code is 0 when
no discrepancy is found, 1 otherwise.

Scenario length matters for the cache-history bugs this harness targets: they
need several operations to populate a cache and then hit the poisoned entry.
Calibration point: the historical `ITE_constant_cache` polarity collision
(fixed in 94993a9) is *not* found in 4 minutes of random mode at the default
fuel, but `--fuel 25` rediscovers it within a couple of minutes, several times
over. Prefer `--fuel 25` (or more) for random-mode runs.

The `Makefile` also has a `random` target, but it builds in the afl switch
(below); the `dune exec` line above is the switch-agnostic way.

### afl mode (coverage-guided, manual/periodic)

Real coverage-guided fuzzing needs an afl-instrumented switch (one built with
`ocaml-option-afl`, e.g. `4.14.x+options+afl` or `5.x+options` with
`ocaml-option-afl`) and `afl-fuzz` installed. The `Makefile` wraps the standard
Monolith afl workflow. From this directory:

```
make setup                 # create the afl switch (if needed) + install monolith there
make SWITCH=<afl-switch> test        # build in the afl switch and launch afl-fuzz
```

`SWITCH` defaults to `5.5.0+afl`; override it to match your afl switch. Other
targets from Monolith's Makefile: `make random` (afl switch, no afl-fuzz),
`make multicore` / `make tmux` (parallel afl), `make show` / `make summary`
(decode discovered crashes), `make min` (minimise crashing inputs with
`afl-tmin`), `make clean`.

### Reproducing a scenario

Monolith prints a self-describing scenario (a sequence of `let` bindings ending
in the failing observation) both in random mode and, via `make show`, for
afl-found crashes. A saved crash input can be replayed with:

```
dune exec fuzz/main.exe -- fuzz/output/crashes/<id>
```

`afl-tmin` (`make min`) plus Monolith's own scenario shrinking give short repros.

## Trusting the model

If the model is wrong, every fuzz report is noise. So `test/test_model.ml`
(part of the normal `dune runtest`, no monolith needed) checks the model against
Theo with QCheck: for every operation the harness relies on, it verifies that
the model's answer agrees with Theo's on random formulas. The finite-domain
*adequacy argument* — why enumerating a few thousand worlds distinguishes
exactly the formulas the theory semantics distinguishes — is written out next to
the domain definitions in `../test/support/model.ml`.

## Notes / possible extensions

- CI integration is deliberately left to the author. Options: a smoke job that
  runs `dune exec fuzz/main.exe -- --timeout 30` on every PR (guarded by
  monolith being installed), and/or a scheduled (cron) job that runs afl mode
  for longer on an afl switch. Nothing here touches `.github/workflows/`.
- `and_list` / `or_list` are not yet declared. They are compositions of covered
  operations, but their divide-and-conquer order produces different cache
  traffic, so they are worth adding in a second pass.
- `shortest_sat` is checked for *validity* only (a consistent witness that
  implies the formula); comparing its length against the model's minimum is a
  possible future refinement.
