# Teaching Booleans About Versions: A Theory-Augmented BDD Library in OCaml

What if checking whether two formulas with a million nodes are logically
equivalent took exactly one machine instruction? Binary Decision Diagrams (BDDs)
make this possible. They give you a **canonical** representation of boolean
functions — two logically equivalent formulas always produce the exact same
structure — which turns equivalence checking into a pointer comparison.

[Theo](https://github.com/vouillon/theo) is an OCaml library that implements
BDDs with two key extensions: **complement edges** for compact representation,
and **theory support** for reasoning about linear orders and equality. Consider
a package manager checking whether `(ocaml >= 4.14 AND dune >= 3.0) OR
(ocaml >= 5.0)` is compatible with `ocaml < 5.0`. With Theo, you write this
directly using version constraints as atoms, and the engine automatically
simplifies: it knows `ocaml >= 4.14` is redundant when `ocaml >= 5.0` holds,
detects that the second disjunct contradicts `ocaml < 5.0`, and can find the
simplest satisfying assignment (`ocaml >= 4.14, dune >= 3.0`).

This post walks through the main implementation ideas behind Theo: the
complement edge representation, hash-consing via weak tables and ephemeron-based
memoization, theory-aware simplification during BDD construction, and several
algorithmic techniques — contextual restriction, minimal witness extraction, and
zero-allocation entailment checks — that make the library practical.

## From truth tables to shared diagrams

A boolean function over *n* variables can be represented as a truth table with
2^*n* rows, or equivalently as a binary decision tree: at each node, you test a
variable and branch left (false) or right (true), until you reach a leaf (0 or
1). The problem is that this tree is exponentially large.

A **Binary Decision Diagram** (BDD) is a compressed version of this tree,
obtained by two reductions:

1. **Merge identical subtrees.** If two nodes have the same variable, same low
   child, and same high child, keep only one copy.
2. **Eliminate redundant tests.** If a node's low and high children are the same
   subtree, skip the test entirely.

When you additionally fix a **variable ordering** (every path from root to leaf
tests variables in the same order), the result is called a Reduced Ordered BDD
(ROBDD). The key theorem is that ROBDDs are **canonical**: for a given variable
ordering, every boolean function has exactly one ROBDD. Logical equivalence
becomes pointer equality. O(1).

The core operation on BDDs is **ITE** (if-then-else): given three BDDs *f*, *g*,
*h*, compute the BDD for "if *f* then *g* else *h*". Every boolean connective
reduces to ITE:

- `and(f, g) = ite(f, g, 0)`
- `or(f, g)  = ite(f, 1, g)`
- `not(f)    = ite(f, 0, 1)`

The ITE algorithm works by **Shannon decomposition**: pick the topmost variable
*x* across all three inputs, decompose each input into its *x*=true and *x*=false
cofactors, recurse on both branches, and combine the results into a new node.
With memoization, this runs in O(|*f*| * |*g*| * |*h*|) time.

## Negation for free

In a standard BDD, negation requires traversing the entire structure: you walk
every path and flip the terminal nodes. This is O(*n*) where *n* is the number
of nodes. For a data structure built around efficiency, that's disappointing.

**Complement edges** solve this by allowing edges to carry a negation flag. The
idea comes from Brace, Rudell, and Bryant [1]: instead of building a separate
BDD for `not f`, just mark the edge to `f` as complemented.

Negation becomes O(1).

The trick is maintaining canonicity. With unrestricted complement edges, the same
function could be represented in multiple ways. Theo enforces a canonical form
through two invariants:

1. **Only one terminal node.** There is only `False`. But if there's no `True`
   terminal, how do you represent truth? As `Not False`. One terminal, zero
   ambiguity.

2. **The low branch is always positive.** Complement edges appear only on the
   high branch (via `negate_high`) or at the root (via `Not`). This prevents
   multiple representations of the same function.

Here is the actual type definition:

```ocaml
type _ u =
  | False : positive u
  | If : {
      atom : atom;
      high : positive u;
      negate_high : bool;
      low : positive u;
      id : int;
    } -> positive u
  | Not : positive u -> negative u

type t = Bdd : _ u -> t
```

The phantom types `positive` and `negative` enforce at the type level that `If`
nodes store positive (non-complemented) subtrees for both `high` and `low`. The
complement is carried by the `negate_high` boolean for the high branch, and by
the `Not` wrapper at the root.

To see what this buys us, here is `a AND b` in both representations:

```
Standard BDD:           Complement edges:

      a                       a
     / \                     / \
    0   b                   F   b
       / \                     / \~
      0   1                   F   F

Two terminals (0, 1).   One terminal (F).
                        ~ = complement edge: ~F reads as True.
```

Now negate it. In the standard BDD, you'd walk every node and flip the leaves.
With complement edges:

```
NOT (a AND b):

    NOT
     |
     a              Same nodes. Just wrapped in NOT.
    / \
   F   b
      / \~
     F   F
```

In code, negation is just:

```ocaml
let not u =
  match u with
  | Bdd (Not u) -> Bdd u       (* double negation cancels *)
  | Bdd False   -> true_        (* not false = true *)
  | Bdd (If _ as f) -> Bdd (Not f)
```

The `split` helper decomposes any BDD into its polarity and positive core, which
is used throughout the implementation:

```ocaml
let split (Bdd u) =
  match u with
  | Not n  -> (true, n)
  | If _ as n -> (false, n)
  | False as n -> (false, n)
```

Here's where it gets interesting. Since negation is free, De Morgan's law is
free. Which means **Theo has no dedicated OR algorithm.** The entire
implementation is:

```ocaml
let or_ u v = not (and_rec (not u) (not v))
```

Three calls to `not`, each O(1), plus one `and_rec`. One operation eliminated.

This representation also has a consequence for the ITE algorithm: `ite`
normalizes its arguments before recursing — if `f` is negative, swap `g` and
`h`; if `h` is negative, negate the result and recurse with `not g`. This
doesn't affect canonicity (which is guaranteed by hash-consing and the node
invariants), but it ensures that equivalent calls always use the same argument
form, maximizing cache hit rates.

## Same formula, same pointer

Hash-consing is the technique of ensuring that structurally equal values are
represented by a single object in memory. For BDDs, this is what turns the
canonicity guarantee into an O(1) equality check: if two BDDs represent the same
function, they are literally the same pointer.

### Weak tables, strong guarantees

But there's a tension: if you store every node ever created in a global table,
nothing gets garbage-collected. Your BDD library slowly eats all available
memory.

Theo resolves this with OCaml's `Weak.Make`: a hash table that holds **weak
references** to its entries. The GC can reclaim any entry that is no longer
referenced elsewhere. You get structural sharing without memory leaks.

The pattern is the same for atoms and nodes. Here is the node constructor:

```ocaml
let ite atom high negate_high low =
  let id = !next_id in
  let node =
    WeakTbl.merge weak_tbl (If { atom; high; negate_high; low; id })
  in
  match node with
  | If { id = id'; _ } when Int.equal id id' ->
      next_id := !next_id + 1;
      node
  | If _ | False -> node
```

The `merge` function is the key operation: it looks up the candidate node in the
weak table. If an equal node already exists, it returns the existing one (and
the candidate, including its fresh `id`, is discarded). If no equal node exists,
the candidate is inserted and its `id` becomes permanent. The check
`Int.equal id id'` detects which case occurred.

The same pattern applies to atoms (`Atom.WeakTbl`), ensuring that the atom for
"ocaml, less than 5.0" exists at most once in memory. Since atoms are compared
by physical equality everywhere in the BDD engine (`atom == v`), this is what
makes cofactor decomposition fast.

### Caches that forget

BDD operations rely heavily on memoization: without caching, the ITE algorithm
would repeatedly recompute the same subproblems, exploding to exponential time.
The standard approach is a hash table keyed by the operation's inputs.

But now we have a problem. A regular hash table holds strong references to its
keys. If the keys are BDD nodes, the cache keeps them alive — defeating the
whole point of weak hash tables. We'd need manual eviction, which is fragile and
error-prone.

What if the cache could clean up after itself?

This is exactly what **ephemerons** provide. An ephemeron is a key-value pair
where the key is held weakly: if the key object is collected by the GC, the
entire entry (including the value) becomes reclaimable. OCaml's standard library
provides `Ephemeron.K1`, `Ephemeron.K2`, and `Ephemeron.Kn` for ephemerons with
one, two, or *n* keys.

Theo uses three ephemeron-based caches, each with a design tailored to its use
case:

**The ITE cache** (`Ephemeron.Kn.Make` with 3 keys) stores `ite(f, g, h)`
results. Since `g` can appear in either polarity (positive or negative) while
`f` and `h` are always positive after normalization, the cache uses a
**polarity cell** trick: it keys on `(f, |g|, h)` (where `|g|` is the positive
core of `g`) and stores both the positive and negative results in the same cell:

```ocaml
type 'a polarity_cell = {
  mutable pos : 'a option;
  mutable neg : 'a option
}
```

This avoids duplicating cache entries for `ite(f, g, h)` and `ite(f, not g, h)`.

**The binary cache** (`Ephemeron.K2.Make`) takes this further. It stores AND
results for all four polarity combinations of its two operands in a single entry:

```ocaml
type cell = {
  mutable pp : t option;  (* |u| AND |v|     *)
  mutable pn : t option;  (* |u| AND NOT |v| *)
  mutable np : t option;  (* NOT |u| AND |v| *)
  mutable nn : t option;  (* NOT |u| AND NOT |v| *)
}
```

Remember that `or_ u v = not (and_rec (not u) (not v))`? When Theo computes an
OR, it calls `and_rec` on the negated inputs — and this reuses the same cache
entry (in the `nn` slot) as a direct AND would. One cache serves both operations.

**The simplify cache** (`Ephemeron.K1.Make`) stores theory simplification
results keyed by a single BDD node. This is used during theory-aware node
construction, discussed next.

Together, weak tables and ephemerons form a self-managing memory system. BDD
nodes live in weak hash tables: when application code drops all references to a
node, the GC reclaims it. Ephemeron caches hold weak references to those same
nodes as keys: when a node dies, all cache entries that depended on it become
reclaimable too. No manual cache invalidation, no memory leaks, no bookkeeping.
The GC does all the work.

## Beyond booleans

Theo's atoms aren't just booleans — they're constraints like `ocaml < 5.0` or
`name = "foo"`, and the engine knows what that means.

Standard BDDs reason about pure boolean variables. But a package manager needs
to compare version numbers, a type checker tracks string labels, a configuration
system deals with enumerated values. You could encode these as booleans, but you
lose the domain structure and the BDD cannot exploit the semantics. Theo takes a
different approach: atoms carry **theory predicates**, and the engine uses their
semantics to simplify formulas during construction.

### Atoms with meaning

At the type level, a theory is a module implementing comparison, hashing, and
pretty-printing for atom descriptors:

```ocaml
module type Theory = sig
  type _ t
  val equal : _ t -> _ t -> bool
  val compare : _ t -> _ t -> int
  val hash : _ t -> int
  val to_string : _ t -> string
end
```

The BDD engine is parameterized by a theory via the `Make` functor:
`Make(Void)` gives you standard boolean BDDs, while `Make(Leq(Version))` gives
you BDDs that understand version comparisons.

Internally, atoms are tagged with a **category** that tells the engine which
simplification rules apply:

```ocaml
type _ category = Bool | Leq | Eq
```

An atom combines a variable, a category, and a payload:

```ocaml
type atom = Atom : {
  var : 'kind Var.t;
  category : 'kind category;
  payload : 'kind payload;
  id : int;
} -> atom
```

For example, the atom for `ocaml < 5.0.0` would have `category = Leq` and
`payload = Theory (Bound { limit = v5_0_0; inclusive = false })`.

Notice the existential type: `Atom` packs a `'kind` type variable that ties
`var`, `category`, and `payload` together, then hides it. This is a GADT
pattern that lets a single `atom` type hold heterogeneous payloads (boolean
flags, version bounds, string constants) while ensuring at the type level that
a version variable never receives a string payload. The `view_constraint`
function later unpacks the existential for pattern matching.

A crucial design choice is **atom ordering**: atoms are sorted first by variable,
then by payload. For `Leq` atoms, this means all bounds for the same variable
are clustered together and sorted by their bound value. This ordering is what
makes theory simplification possible during BDD construction.

### Pruning what you already know

Here's the key idea. When the BDD engine decomposes a formula along an atom like
`ocaml < 4.14`, it knows that in the **high branch** (where `ocaml < 4.14`
holds), any atom for the same variable with a weaker bound is redundant.
`ocaml < 5.0`? Automatically true. No need to test it.

This is implemented through the `cofactors` function, which computes the high
and low branches of a BDD with respect to a given atom:

```ocaml
let cofactors v (t : t) =
  let negate_t, u = split t in
  match u with
  | If { atom; high; negate_high; low; _ } ->
      if atom == v then
        (* Direct match: decompose normally *)
        let h = ... in
        let l = ... in
        (h, l)
      else
        (* Not a direct match: apply theory simplification *)
        let simplified = prune v u atom high negate_high low negate_t in
        (simplified, t)
  | False -> (t, t)
```

When the top atom of the BDD doesn't directly match the decomposition atom, but
they share the same variable, the `prune` function applies theory-specific
simplification:

```ocaml
let prune (Atom a) (u : positive u) (Atom atom) high
    negate_high low negate_result : t =
  if a.var <> atom.var then with_polarity negate_result u
  else
    match a.category with
    | Bool -> with_polarity negate_result u
    | Leq -> with_polarity (negate_result <> negate_high) high
    | Eq -> with_polarity negate_result (simplify_node (Atom a) low)
```

For the `Leq` category: because atoms for the same variable are sorted by bound
value, if we are decomposing on `ocaml < 4.14` and encounter a node testing
`ocaml < 5.0`, we know the first implies the second. The node can be replaced by
its high branch (the case where `ocaml < 5.0` holds). This is the line
`Leq -> with_polarity (negate_result <> negate_high) high`.

For the `Eq` category: if we know `name = "foo"`, then any node testing
`name = "bar"` is resolved to false (take the low branch). The `simplify_node`
function walks through consecutive atoms of the same variable in the low branch,
skipping them since they are all falsified by the equality constraint.

The `make_node` function, which constructs the actual BDD node, applies a
complementary check: after building the high and low branches, if theory
simplification would make the result equal to the low branch, the new node is
redundant and is eliminated.

**A concrete example.** Consider computing `ocaml < 4.14 AND ocaml < 5.0`:

1. The atoms are ordered: `ocaml < 4.14` comes before `ocaml < 5.0` (smaller
   bound).
2. The AND algorithm finds the top atom across both inputs: `ocaml < 4.14`.
3. Cofactors of the first input w.r.t. `ocaml < 4.14`: high = True, low = False.
4. Cofactors of the second input w.r.t. `ocaml < 4.14`: since `ocaml < 4.14`
   implies `ocaml < 5.0` (same variable, tighter bound), `prune` returns True
   for the high cofactor. The low cofactor remains `ocaml < 5.0`.
5. Recursive calls: `and(True, True) = True` for the high branch;
   `and(False, ocaml < 5.0) = False` for the low branch — the terminal case
   collapses immediately.
6. `make_node (ocaml < 4.14) True False` is simply the BDD for `ocaml < 4.14`.

The simplification happened at step 4: `prune` recognized that `ocaml < 4.14`
implies `ocaml < 5.0` and collapsed the cofactor to True. This turned the low
branch into a trivial `and(False, ...)`, and the final result is just
`ocaml < 4.14`.

Here is the corresponding test from the test suite, proving it:

```ocaml
let v = Theo.Var.fresh () in
let lt_4_14 = V.(v < { major = 4; minor = 14; patch = 0 }) in
let lt_5_0  = V.(v < { major = 5; minor = 0;  patch = 0 }) in
assert (F.equivalent (lt_4_14 && lt_5_0) lt_4_14)
```

### One syntax, two interpretations

Theo provides syntax modules that let you write constraints naturally:

```ocaml
module V = VersionLeq.Syntax(MyTheory.Left(MyBDD))

let expr = V.(ocaml < version_5_0_0)
```

The implementation of `Leq.Syntax` is remarkably concise — twelve lines that
define six operators:

```ocaml
module Syntax (F : Formula with type 'kind desc = 'kind t) = struct
  let lt var limit = F.atom var category (Bound { limit; inclusive = false })
  let le var limit = F.atom var category (Bound { limit; inclusive = true })
  let ( <= ) = le
  let ( < ) = lt
  let ( >= ) v x = F.not (v < x)
  let ( > ) v x = F.not (v <= x)
  let ( = ) v x = F.and_ (v <= x) (v >= x)
  let ( <> ) v x = F.or_ (v < x) (v > x)
end
```

Notice how `>=` is just `not` of `<` (free, thanks to complement edges), and
`=` is `<= AND >=` (two bounds). The theory structure maps directly onto the
syntax.

The `Formula` module type is the key abstraction that makes this work:

```ocaml
module type Formula = sig
  type t
  type _ desc
  val not : t -> t
  val and_ : t -> t -> t
  val or_ : t -> t -> t
  val atom : 'kind Var.t -> 'kind category -> 'kind desc -> t
end
```

Both `Make(T)` (the BDD module) and `Make(T).Constraint` (which builds lists of
atomic constraints for the `restrict` operation) satisfy this interface. So the
same `Syntax` functor works for both — same code, different interpretation:

```ocaml
(* Build BDD formulas *)
module V = VersionLeq.Syntax(MyTheory.Left(MyBDD))
let bdd_expr = V.(ocaml < version_5_0_0)

(* Build constraint lists for restrict *)
module V_cstr = VersionLeq.Syntax(MyTheory.Left(MyBDD.Constraint))
let constraint_expr = V_cstr.(ocaml < version_5_0_0)
```

When multiple theories are combined with `Combine(A)(B)`, the `Left` and
`Right` projections handle the plumbing. `Left(F)` wraps the atom descriptor in
the `Left` constructor of the sum type before passing it to `F.atom`:

```ocaml
module Left (F : Formula with type 'kind desc = 'kind t) = struct
  include F
  type 'kind desc = 'kind A.t
  let atom var cat desc = atom var cat (Left desc)
end
```

This allows the syntax helpers for each theory to be blissfully unaware of the
combination machinery while producing atoms that are correctly tagged for the
combined BDD.

### Eliminating variables

Sometimes you want to ask "does a solution exist regardless of variable *x*?"
without caring about *x*'s value. In our package manager, this might be: "is
there any version of `dune` that makes this formula satisfiable?" This is
**quantifier elimination**: `exists x. f` computes the disjunction of `f` over
all possible values of *x*, effectively projecting *x* out of the formula.

Theo implements both `exists` and `forall` through a single `quantify` function,
parameterized by the combination operator:

```ocaml
let exists v t = quantify or_ v t
let forall v t = quantify and_ v t
```

The `quantify` function walks the BDD, and whenever it encounters an atom for
the target variable, it combines the high and low branches with the given
operator instead of creating a decision node. For theory variables, this
eliminates all atoms mentioning that variable — not just a single boolean test,
but every bound or equality constraint on it.

### Contextual simplification

While `prune` works locally during construction, we sometimes need to simplify an
existing BDD under a set of external constraints. "Simplify this dependency
formula knowing that `ocaml >= 4.14`." This is the job of `restrict`.

Theo implements this using a form of **partial evaluation**. It first converts
the list of constraints into a temporary constraint store — a specialized hash
table index that tracks strict bounds (`<`), loose bounds (`<=`), and equality
sets for every variable.

Then, it walks the BDD. For each node, it asks the store: "Is this atom's value
forced by the constraints?" If the constraints imply `ocaml < 4.14` and the node
tests `ocaml < 5.0`, the store returns `true`, and the traversal skips directly
to the high branch. This allows simplifying complex formulas based on context,
effectively specializing the BDD to a specific environment.

## Optimization as search

Finding *a* satisfying assignment for a BDD is easy: just walk down to `True`.
Finding the *simplest* one — the one that involves the fewest decisions — is
harder. But for error reporting, you want to show the user the smallest set of
constraints that leads to a conflict, not a verbose dump of every variable.

Theo exploits the canonical DAG structure to solve this via **dynamic
programming**. A memoized pass computes the shortest distance from each node to
a satisfying terminal, then a traceback follows the optimal choices. Because
identical subgraphs are shared (hash-consing), each node is visited at most
once. The result is not just any witness, but the minimal one — the shortest
path through the decision graph.

## Zero-allocation queries

Sometimes we want to check a property like logical implication (`A` implies `B`)
or disjointness (`A` and `B` have no intersection) without actually needing the
resulting BDD. Constructing the intermediate BDD for `(not A) or B` just to
check if it is `True` is wasteful: it allocates nodes and pollutes the unique
table with entries that will be immediately discarded.

What if you could traverse the BDD as if computing the result, but never
actually build it?

Theo addresses this with a dedicated `ite_constant` engine. It traverses the
graph as if it were computing `ite(f, g, h)`, but instead of allocating nodes,
it only tracks whether the result is guaranteed to be a boolean constant (`True`
or `False`) or if it depends on variables (`NonConstant`). This powers
`logical_implies`, `is_disjoint`, and `is_exhaustive` — all without constructing
a single intermediate node.

## Balanced construction

When combining a long list of formulas (e.g., `and [f1; f2; ...; fn]`), the
order of operations matters significantly for performance. A naive `fold_left`
tends to produce unbalanced intermediate trees that can grow unnecessarily large.

Theo employs a **balanced reduction** strategy for n-ary operations. It first
sorts the input BDDs by their top variable — a simple heuristic that groups
formulas likely to share structure. It then combines them using a tree-like
reduction (pairwise combination) rather than a linear fold. This minimizes the
size of intermediate results and maximizes cache hit rates.

## The whole is more than the sum of its parts

Theo's design weaves together several ideas that reinforce each other: complement
edges make negation free, which eliminates the need for a dedicated OR algorithm;
hash-consing via weak tables provides canonicity without memory leaks;
ephemeron-based caches give automatic cleanup when nodes become unreachable;
atom ordering by variable and bound value enables theory simplification during
construction; and the `Formula` abstraction unifies BDDs and constraints under
the same syntax. Beyond these foundations, techniques like partial evaluation for
`restrict`, dynamic programming for minimal witnesses, zero-allocation
entailment checks, and balanced reduction for n-ary operations ensure that the
library performs well in practice, not just in theory.

The library is available at
[github.com/vouillon/theo](https://github.com/vouillon/theo), with API
documentation at
[vouillon.github.io/theo](https://vouillon.github.io/theo/theo/Theo/).

## References

[1] Brace, Karl S.; Rudell, Richard L.; Bryant, Randal E. (1990). "Efficient
Implementation of a BDD Package". *Proceedings of the 27th ACM/IEEE Design
Automation Conference (DAC 1990)*. IEEE Computer Society Press. pp. 40–45.
[doi:10.1145/123186.123222](https://doi.org/10.1145/123186.123222).
ISBN 978-0-89791-363-8.
