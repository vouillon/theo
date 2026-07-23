(* A trusted reference ("model") implementation of the BDD API, used by the
   Monolith harness in fuzz/ and unit-tested against Theo by test/test_model.ml.

   The design goal is brutal simplicity: no sharing, no hash-consing, no
   memoization. A formula is represented by its full truth table over a finite
   set of "worlds" (assignments of a value to every variable in the fixed
   pools). Every logical question is then answered by enumeration over that
   table. If this model and the library ever disagree, the library is (almost
   certainly) the one at fault -- which is the whole point.

   The model deliberately mirrors the monomorphised instance used by the tests:
   [Theo.Make (Theo.Combine (Leq(Version)) (Eq(String)))], i.e. version bounds
   (Left) + string equality (Right) + booleans. See test/support/theories.ml. *)

open Theories

(* --------------------------------------------------------------------------
   Fixed pools

   [Var.fresh] is a global mutable counter and is NEVER exposed as a fuzzing
   operation: an unbounded variable pool would make the world enumeration below
   impossible. Instead we allocate a small, fixed set of variables once, here,
   at module-initialisation time, and the fuzzer only ever mentions these.
   -------------------------------------------------------------------------- *)

let n_bool = 4
let n_str = 2
let n_ver = 2
let bool_pool = Array.init n_bool (fun _ -> Theo.Var.fresh ())
let str_pool = Array.init n_str (fun _ -> Theo.Var.fresh ())
let ver_pool = Array.init n_ver (fun _ -> Theo.Var.fresh ())

(* --------------------------------------------------------------------------
   Constant pools and finite value domains

   Adequacy of the finite domains (the one subtle correctness point).

   The model is only trustworthy if enumerating the finite domains below
   distinguishes exactly the formulas that the theory semantics distinguishes.
   The key invariant that makes this hold is:

     Every atom that can ever occur in a BDD produced by the harness uses a
     limit/constant drawn from a FIXED constant set -- [ver_consts] for version
     bounds and [str_consts] for string equalities.

   This is not automatic; it is enforced by the operation vocabulary:
     - the version-atom constructors take their constant from [ver_consts];
     - the string-atom constructors take their constant from [str_consts];
     - and, crucially, the cube literals fed to [restrict] and [of_cube] also
       only ever pin a variable to one of those same constants (see [Ver_pin]
       and [Str_pin] below). A cube never introduces a fresh limit, so [of_cube]
       -- whose result BDD *does* contain the cube's atoms -- cannot widen the
       constant set either.

   Because the constant set is fixed, the values a variable can take split into
   finitely many equivalence classes that agree on every atom, and it suffices
   to keep one representative per class:

     * String (Eq theory, open domain): the atoms are [v = "a" | "b" | "c"].
       Two values outside the pool (e.g. "d" and "e") satisfy no atom and are
       indistinguishable, but [v <> "a" && v <> "b" && v <> "c"] is
       satisfiable, so the domain must contain ONE value outside the pool -- the
       sentinel "other". Domain: {"a"; "b"; "c"; "other"} (4 values).

     * Version (Leq theory, linear order): the atoms are [v < c] and [v <= c]
       for c in [ver_consts] = {1.0.0; 2.0.0}. These constants cut the version
       line into intervals; two values in the same interval agree on every atom.
       An adequate domain keeps one representative per interval: one below all
       constants, each constant itself, one strictly between consecutive
       constants, and one above all constants:
         0.0.0  (below 1.0.0)
         1.0.0  (= the constant)
         1.0.1  (strictly between 1.0.0 and 2.0.0)
         2.0.0  (= the constant)
         2.0.1  (above 2.0.0)
       (5 values). Patch numbers are used to fabricate the "between" and
       "above" midpoints cheaply.

   World count: 2^n_bool * |str_domain|^n_str * |ver_domain|^n_ver
              = 2^4 * 4^2 * 5^2 = 6400 worlds. A full-enumeration equivalence
   check is then a few thousand array reads -- microseconds. Keep the pools
   small; this is a knob to tune, not to grow.
   -------------------------------------------------------------------------- *)

let mk major minor patch = { Version.major; minor; patch }

(* Constants usable in atoms and cube literals. *)
let str_consts = [| "a"; "b"; "c" |]
let ver_consts = [| mk 1 0 0; mk 2 0 0 |]

(* Finite value domains: the constant pool plus the extra representatives that
   the adequacy argument requires. *)
let str_domain = [| "a"; "b"; "c"; "other" |]
let ver_domain = [| mk 0 0 0; mk 1 0 0; mk 1 0 1; mk 2 0 0; mk 2 0 1 |]

(* Domain index of each atom/pin constant, so that pinning a variable to a
   constant selects the matching world value. String constants occupy the first
   positions of [str_domain] by construction. *)
let str_const_domain_index = [| 0; 1; 2 |]
let ver_const_domain_index = [| 1; 3 |]
let n_str_dom = Array.length str_domain
let n_ver_dom = Array.length ver_domain

(* --------------------------------------------------------------------------
   Worlds as a mixed-radix integer encoding

   A world is an assignment of a value to every pooled variable. We enumerate
   worlds by numbering them 0 .. n_worlds-1 in a mixed-radix system, one digit
   per variable:

     digit positions 0 .. n_bool-1                 : boolean vars   (radix 2)
     positions n_bool .. n_bool+n_str-1            : string vars    (radix 4)
     positions .. +n_ver-1                          : version vars   (radix 5)

   [stride.(p)] is the product of the radices of the lower positions, so
   [get_digit id p] extracts digit [p], and overriding a single digit is a cheap
   integer update (see [override_digit] / [apply_pins]). *)

let radices =
  Array.concat
    [
      Array.make n_bool 2;
      Array.make n_str n_str_dom;
      Array.make n_ver n_ver_dom;
    ]

let n_digits = Array.length radices
let str_base = n_bool (* first string digit position *)
let ver_base = n_bool + n_str (* first version digit position *)

let stride =
  let s = Array.make n_digits 1 in
  for p = 1 to n_digits - 1 do
    s.(p) <- s.(p - 1) * radices.(p - 1)
  done;
  s

let n_worlds = stride.(n_digits - 1) * radices.(n_digits - 1)
let get_digit id p = id / stride.(p) mod radices.(p)

(* [override_digit id p k] is the world [id] with digit [p] forced to [k]. *)
let override_digit id p k = id - (get_digit id p * stride.(p)) + (k * stride.(p))

(* --------------------------------------------------------------------------
   The model value: a truth table

   A formula is a [bool array] of length [n_worlds]; entry [id] is the truth
   value of the formula in world [id]. This is the reference-side representation
   of the abstract BDD type. *)

type m = bool array

let init f : m = Array.init n_worlds f

module Ref = struct
  (* Constants and boolean connectives are pointwise over the truth table. *)

  let true_ : m = Array.make n_worlds true
  let false_ : m = Array.make n_worlds false
  let not_ (a : m) : m = Array.map Stdlib.not a
  let and_ (a : m) (b : m) : m = init (fun i -> a.(i) && b.(i))
  let or_ (a : m) (b : m) : m = init (fun i -> a.(i) || b.(i))
  let xor (a : m) (b : m) : m = init (fun i -> a.(i) <> b.(i))
  let iff (a : m) (b : m) : m = init (fun i -> a.(i) = b.(i))
  let implies (a : m) (b : m) : m = init (fun i -> (not a.(i)) || b.(i))

  let ite (f : m) (g : m) (h : m) : m =
    init (fun i -> if f.(i) then g.(i) else h.(i))

  (* Atoms. [atom_bool i] is true where boolean variable [i] is true. The
     version/string atoms evaluate the theory relation of the world value
     against the given constant. *)

  let atom_bool i : m = init (fun id -> get_digit id i = 1)

  let atom_ver i ~strict c : m =
    init (fun id ->
        let cmp = Version.compare ver_domain.(get_digit id (ver_base + i)) c in
        if strict then cmp < 0 else cmp <= 0)

  let atom_str i s : m =
    init (fun id -> String.equal str_domain.(get_digit id (str_base + i)) s)

  (* Observations. *)

  let is_tautology (a : m) = Array.for_all (fun x -> x) a
  let is_satisfiable (a : m) = Array.exists (fun x -> x) a
  let equivalent (a : m) (b : m) = a = b

  let logical_implies (a : m) (b : m) =
    let ok = ref true in
    Array.iteri (fun i x -> if x && not b.(i) then ok := false) a;
    !ok

  let is_disjoint (a : m) (b : m) =
    let ok = ref true in
    Array.iteri (fun i x -> if x && b.(i) then ok := false) a;
    !ok

  let is_exhaustive (a : m) (b : m) =
    let ok = ref true in
    Array.iteri (fun i x -> if (not x) && not b.(i) then ok := false) a;
    !ok

  (* [ite_constant f g h]: whether [ite f g h] is constantly true/false. *)
  let ite_constant (f : m) (g : m) (h : m) : Formula.constant_result =
    let r = ite f g h in
    if is_tautology r then Formula.Constant true
    else if not (is_satisfiable r) then Formula.Constant false
    else Formula.NonConstant

  (* Quantifiers. [exists] over variable at digit position [p] (whose domain has
     [radix] values) is true in world [id] iff some value [k] of that variable
     makes the body true; [forall] iff every value does. Overriding a single
     digit only moves within the [radix] worlds that share the other digits, so
     we walk them directly. *)

  let exists_at p (a : m) : m =
    let radix = radices.(p) in
    init (fun id ->
        let rec any k =
          k < radix && (a.(override_digit id p k) || any (k + 1))
        in
        any 0)

  let forall_at p (a : m) : m =
    let radix = radices.(p) in
    init (fun id ->
        let rec all k =
          k >= radix || (a.(override_digit id p k) && all (k + 1))
        in
        all 0)

  let exists_bool i = exists_at i
  let exists_str i = exists_at (str_base + i)
  let exists_ver i = exists_at (ver_base + i)
  let forall_bool i = forall_at i
  let forall_str i = forall_at (str_base + i)
  let forall_ver i = forall_at (ver_base + i)
end

(* --------------------------------------------------------------------------
   Cubes: consistent conjunctions of literals over the pools

   A [cube] is a list of "pins", each of which fixes one variable to one
   concrete value. This restricted shape is deliberate (see the "restrict with
   contradictory constraints" open question in the plan): by construction a
   cube is always consistent, and, more importantly, its meaning is exactly a
   substitution [w := w with the pinned variables overridden]. That makes the
   model's [restrict] a plain truth-table re-indexing that matches the library
   cofactor semantics precisely, avoiding the delicate case of partial theory
   literals (e.g. asserting only [v <= 3], which pins nothing).

   A version pin uses a constant from [ver_consts] only, so it introduces no
   fresh limit and keeps the adequacy argument intact. Likewise a string pin
   uses a pool constant only (the sentinel "other" is not expressible as an
   equality over the pool, so string vars are simply left free rather than
   pinned to it).
   -------------------------------------------------------------------------- *)

type pin =
  | Bool_pin of int * bool (* var index, value *)
  | Str_pin of int * int (* var index, [str_consts] index *)
  | Ver_pin of int * int (* var index, [ver_consts] index *)

type cube = pin list

(* Reference side: a pin maps to a (digit position, value) override. *)
let override_of_pin id = function
  | Bool_pin (i, b) -> override_digit id i (if b then 1 else 0)
  | Str_pin (i, ci) ->
      override_digit id (str_base + i) str_const_domain_index.(ci)
  | Ver_pin (i, ci) ->
      override_digit id (ver_base + i) ver_const_domain_index.(ci)

let apply_pins id (cube : cube) = List.fold_left override_of_pin id cube
let restrict (a : m) (cube : cube) : m = init (fun id -> a.(apply_pins id cube))

let of_cube (cube : cube) : m =
  (* Conjunction of the pin literals: true where every pinned variable holds its
     pinned value. *)
  let holds id = function
    | Bool_pin (i, b) -> get_digit id i = if b then 1 else 0
    | Str_pin (i, ci) ->
        get_digit id (str_base + i) = str_const_domain_index.(ci)
    | Ver_pin (i, ci) ->
        get_digit id (ver_base + i) = ver_const_domain_index.(ci)
  in
  init (fun id -> List.for_all (holds id) cube)

(* --------------------------------------------------------------------------
   Candidate side: build actual Theo BDDs and constraints

   These are thin wrappers over the library, using the fixed pools above so
   that "variable index [i]" means the same thing on both sides. *)

module Cand = struct
  module F = Formula

  (* Constraint builders, identical to those used by test/test_properties.ml. *)
  let c_bool v b = F.Constraint.bool v b
  let c_str_eq v s = F.Constraint.atom v Eq.category (Right (Eq.Const s))

  let c_ver_le v limit =
    F.Constraint.atom v Leq.category
      (Left (Leq.Bound { limit; inclusive = true }))

  let c_ver_lt v limit =
    F.Constraint.atom v Leq.category
      (Left (Leq.Bound { limit; inclusive = false }))

  let c_ver_ge v limit = F.Constraint.not (c_ver_lt v limit)
  let atom_bool i = F.bool bool_pool.(i)

  let atom_ver i ~strict c =
    if strict then VersionSyntax.(ver_pool.(i) < c)
    else VersionSyntax.(ver_pool.(i) <= c)

  let atom_str i s = StringSyntax.(str_pool.(i) = s)

  (* A version pin [v = c] is the pair of literals [v <= c && v >= c]. *)
  let constraints_of_cube (cube : cube) =
    List.concat_map
      (function
        | Bool_pin (i, b) -> c_bool bool_pool.(i) b
        | Str_pin (i, ci) -> c_str_eq str_pool.(i) str_consts.(ci)
        | Ver_pin (i, ci) ->
            let c = ver_consts.(ci) in
            c_ver_ge ver_pool.(i) c @ c_ver_le ver_pool.(i) c)
      cube

  let restrict bdd cube = F.restrict bdd (constraints_of_cube cube)
  let of_cube cube = F.of_cube (constraints_of_cube cube)
  let exists_bool i = F.exists bool_pool.(i)
  let exists_str i = F.exists str_pool.(i)
  let exists_ver i = F.exists ver_pool.(i)
  let forall_bool i = F.forall bool_pool.(i)
  let forall_str i = F.forall str_pool.(i)
  let forall_ver i = F.forall ver_pool.(i)
end

(* --------------------------------------------------------------------------
   Evaluating a library constraint against a world

   [sat]/[shortest_sat]/[irredundant_sop] hand back literals built by the
   library; to check them we must interpret an [atomic_constraint] as a
   predicate on worlds. We decode it with [view_constraint] and locate the
   variable in its pool. All limits/constants involved are drawn from the fixed
   constant sets, so evaluation stays within the finite domains. *)

let find_index pool v =
  let r = ref (-1) in
  Array.iteri (fun i w -> if Theo.Var.equal w v then r := i) pool;
  assert (!r >= 0);
  !r

let eval_constraint c id =
  match Formula.view_constraint c with
  | Constraint { var; payload = Bool; value } ->
      let i = find_index bool_pool var in
      get_digit id i = 1 = value
  | Constraint { var; payload = Theory (Right (Eq.Const s)); value } ->
      let i = find_index str_pool var in
      String.equal str_domain.(get_digit id (str_base + i)) s = value
  | Constraint
      { var; payload = Theory (Left (Leq.Bound { limit; inclusive })); value }
    ->
      let i = find_index ver_pool var in
      let vv = ver_domain.(get_digit id (ver_base + i)) in
      let atom =
        if inclusive then Version.compare vv limit <= 0
        else Version.compare vv limit < 0
      in
      atom = value

(* Worlds in which every literal of a candidate cube holds. *)
let models_of_literals lits =
  let rec loop id acc =
    if id < 0 then acc
    else
      loop (id - 1)
        (if List.for_all (fun c -> eval_constraint c id) lits then id :: acc
         else acc)
  in
  loop (n_worlds - 1) []

(* [sat_ok a witness]: is [witness] an acceptable result of [sat]/[shortest_sat]
   for the formula whose truth table is [a]? [None] is acceptable iff [a] is
   unsatisfiable; a [Some cube] is acceptable iff the cube is consistent
   (has at least one model) and every model of the cube satisfies [a]. *)
let sat_ok (a : m) witness =
  match witness with
  | None -> not (Ref.is_satisfiable a)
  | Some lits ->
      let ms = models_of_literals lits in
      ms <> [] && List.for_all (fun id -> a.(id)) ms

(* [isop_ok a cover]: is [cover] an acceptable result of [irredundant_sop]? The
   disjunction of the cubes must be logically equivalent to [a]. (Equivalence
   already implies that every cube implies [a], so this single check subsumes
   the "every cube implies f" requirement; full irredundancy/primality is left
   to test/test_isop.ml, per the plan.) *)
let isop_ok (a : m) cover =
  let covered id =
    List.exists
      (fun cube -> List.for_all (fun c -> eval_constraint c id) cube)
      cover
  in
  let m = init covered in
  Ref.equivalent m a

(* --------------------------------------------------------------------------
   A small formula AST + dual interpreters, used only by test/test_model.ml to
   check the model against Theo. It exercises every operation the Monolith
   harness relies on, in one place. *)

type vsel = VBool of int | VStr of int | VVer of int

type expr =
  | True
  | False
  | ABool of int
  | AVer of int * int * bool (* var, [ver_consts] index, strict *)
  | AStr of int * int (* var, [str_consts] index *)
  | Not of expr
  | And of expr * expr
  | Or of expr * expr
  | Xor of expr * expr
  | Iff of expr * expr
  | Implies of expr * expr
  | Ite of expr * expr * expr
  | Restrict of expr * cube
  | OfCube of cube
  | Exists of vsel * expr
  | Forall of vsel * expr

let rec eval : expr -> m = function
  | True -> Ref.true_
  | False -> Ref.false_
  | ABool i -> Ref.atom_bool i
  | AVer (i, ci, strict) -> Ref.atom_ver i ~strict ver_consts.(ci)
  | AStr (i, ci) -> Ref.atom_str i str_consts.(ci)
  | Not e -> Ref.not_ (eval e)
  | And (a, b) -> Ref.and_ (eval a) (eval b)
  | Or (a, b) -> Ref.or_ (eval a) (eval b)
  | Xor (a, b) -> Ref.xor (eval a) (eval b)
  | Iff (a, b) -> Ref.iff (eval a) (eval b)
  | Implies (a, b) -> Ref.implies (eval a) (eval b)
  | Ite (f, g, h) -> Ref.ite (eval f) (eval g) (eval h)
  | Restrict (e, cube) -> restrict (eval e) cube
  | OfCube cube -> of_cube cube
  | Exists (VBool i, e) -> Ref.exists_bool i (eval e)
  | Exists (VStr i, e) -> Ref.exists_str i (eval e)
  | Exists (VVer i, e) -> Ref.exists_ver i (eval e)
  | Forall (VBool i, e) -> Ref.forall_bool i (eval e)
  | Forall (VStr i, e) -> Ref.forall_str i (eval e)
  | Forall (VVer i, e) -> Ref.forall_ver i (eval e)

let rec to_bdd : expr -> Formula.t =
  let module F = Formula in
  function
  | True -> F.true_
  | False -> F.false_
  | ABool i -> Cand.atom_bool i
  | AVer (i, ci, strict) -> Cand.atom_ver i ~strict ver_consts.(ci)
  | AStr (i, ci) -> Cand.atom_str i str_consts.(ci)
  | Not e -> F.not (to_bdd e)
  | And (a, b) -> F.and_ (to_bdd a) (to_bdd b)
  | Or (a, b) -> F.or_ (to_bdd a) (to_bdd b)
  | Xor (a, b) -> F.xor (to_bdd a) (to_bdd b)
  | Iff (a, b) -> F.iff (to_bdd a) (to_bdd b)
  | Implies (a, b) -> F.implies (to_bdd a) (to_bdd b)
  | Ite (f, g, h) -> F.ite (to_bdd f) (to_bdd g) (to_bdd h)
  | Restrict (e, cube) -> Cand.restrict (to_bdd e) cube
  | OfCube cube -> Cand.of_cube cube
  | Exists (VBool i, e) -> Cand.exists_bool i (to_bdd e)
  | Exists (VStr i, e) -> Cand.exists_str i (to_bdd e)
  | Exists (VVer i, e) -> Cand.exists_ver i (to_bdd e)
  | Forall (VBool i, e) -> Cand.forall_bool i (to_bdd e)
  | Forall (VStr i, e) -> Cand.forall_str i (to_bdd e)
  | Forall (VVer i, e) -> Cand.forall_ver i (to_bdd e)
