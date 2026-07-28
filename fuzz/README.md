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
`dune build @runtest` work without it, because `fuzz/dune` uses a
`(select ...)` clause that substitutes a stub for the harness when monolith is
absent (the stub prints an installation hint and exits with code 2). In the
opam metadata monolith is declared `{with-dev-setup}`.

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

Useful flags (see `Monolith.mli`): `--fuel N` (max scenario length; the harness
defaults to 25, see `main.fuzz.ml`), `--max-scenarios N`, `--timeout SECONDS`,
`--show-scenario false`, `--save-scenario false`. With saving on (the default),
discovered scenarios are written under `output/crashes/` (relative to the
working directory) in human-readable form.

Scenario length matters for the cache-history bugs this harness targets: a
scenario must populate a cache and then hit the poisoned entry, so very short
scenarios find nothing. Calibration point: the historical `ITE_constant_cache`
polarity collision (fixed in 94993a9) is rediscovered by random mode within a
couple of minutes at fuel 15 or 25 alike (roughly 8-9 failure scenarios in two
minutes either way).

The exit code is 0 when no discrepancy was found and 1 otherwise. When reading
the progress output, note that Monolith *reduces* fuel after each failure it
finds (hunting for shorter scenarios), so a decreasing `fuel = N` in the
progress line means failures have been found even if their reports have already
scrolled by.

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

### Stability: why the harness resets Theo before every scenario

afl runs the harness in **persistent mode**: Monolith's `AflPersistent.run`
executes a thousand scenarios in a single process, without forking in between
(`afl-persistent`, and `waitpid(WUNTRACED)` in the OCaml runtime's forkserver).
Whatever a scenario leaves behind is therefore visible to the next one, and any
such carry-over makes the coverage bitmap a function of the *history of the
process* instead of the current input. afl calls this **stability** (shown in
its UI, and as `stability` in `output/default/fuzzer_stats`) and it matters:
unstable edges make afl mis-attribute coverage to inputs, keep queue entries
that are not really new, and waste its scoring, culling and havoc budgeting.
It also costs reproducibility -- a failure that needs state left by an earlier
scenario would not reproduce from the scenario Monolith prints.

The harness therefore runs a prologue (see `main.fuzz.ml`) before every
scenario, which does two things. Measured on a 120 s run, 16-byte seed, fresh
output directory:

| prologue                                | stability | variable edges | execs/s |
| --------------------------------------- | --------- | -------------- | ------- |
| none (before this was investigated)     | 63.6%     | 1057 / 2902    | 909     |
| `Gc.full_major` alone                   | 62.8%     | 1087 / 2925    | 657     |
| `Theo.reset_state`                      | 74-79%    | 610-764        | 890-1170|
| `reset_state` + `Gc.full_major`         | **99.8%** | **6** / 2801   | 1123    |

- `reset_state` (an undocumented entry point of `Theo.Make`, see `theo.mli`)
  empties the hash-consing tables and the caches and rewinds the atom and node
  identifier counters. The counters are the essential part: the caches are
  keyed on node identifiers, so numbering a scenario's nodes from wherever the
  previous scenario stopped puts them in different buckets and changes the code
  paths taken inside the caches. It is unsound to call it while any BDD built
  earlier is still reachable; the prologue comment explains why that is safe
  here.
- `Gc.full_major` is needed because the caches are ephemerons and the
  hash-consing tables are weak: whether a memoized result is still there when
  it is looked up depends on when the collector last ran, which otherwise
  depends on how much the previous scenarios allocated. Collecting first puts
  the collector in the same state at the start of every scenario. It is not
  slow here, because `reset_state` has just made almost the whole heap
  unreachable.

The 6 edges that still vary are not ours: they are the first iteration of each
process, and Monolith's own `stack` demo shows exactly the same 6
(`var_byte_count : 6`, stability 98.9%). 99.8% is therefore as good as this
framework gets.

The prologue also runs in random mode, where stability is irrelevant but
per-scenario independence still buys reproducibility. It costs roughly half the
scenarios per second there (~1.8K/s to ~0.9K/s) without costing detection
power: with the historical `ITE_constant_cache` polarity bug reintroduced,
60 s of random mode finds it either way (4-8 saved scenarios, prologue or not).

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

- CI runs the harness at two tiers: a 60 s random-mode smoke job on every
  push/PR (`fuzz-smoke` in `.github/workflows/ci.yml`) and a weekly 2 h afl
  job (`.github/workflows/fuzz.yml`, also triggerable manually) whose afl
  state is cached between runs so coverage accumulates across weeks. Beware
  that GitHub disables cron workflows after 60 days without repository
  activity.
- `and_list` / `or_list` are declared (see `main.fuzz.ml`): their argument is a
  `list t`, whose elements Monolith draws from the previously produced BDDs in
  the environment. They are compositions of covered operations, but their
  divide-and-conquer reduction order produces different cache traffic than an
  equivalent fold of `and_`/`or_`, so they are exercised in their own right.
- `shortest_sat` is checked for *validity* (a consistent witness that implies
  the formula), and additionally for the length invariant
  `length(shortest_sat f) <= length(sat f)` via the `shortest_sat_le_sat`
  boolean observation. It is **not** checked for equality against the model's
  brute-force semantic minimum: the library documents `shortest_sat` as the
  shortest *path in the BDD DAG*, which is provably not the semantically minimal
  satisfying cube. For `f = (b0 && b1) || b2` the shortest BDD path has length 2
  (every root-to-true path must traverse the root atom `b0`), yet `{b2}` alone
  implies `f`, so the semantic minimum is 1; an equality check would false-alarm
  on such formulas. The semantic lower bound `model_min <= length(shortest_sat)`
  is sound but toothless — it is already implied by the witness-validity check —
  so it is not added separately. See the extended comment in `main.fuzz.ml`.
