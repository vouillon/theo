(* Monolith fuzzing harness for Theo.

   This declares the Theo BDD API to Monolith, pairing each operation with its
   reference implementation in [Model] (test/support/model.ml). Monolith then
   generates arbitrary well-typed sequences of these operations over a single
   shared BDD instance and, at every observation, checks that Theo agrees with
   the model. When it finds a disagreement it prints a minimal reproducing
   scenario as OCaml code.

   Why sequences over a shared instance: the QCheck suite builds a fresh
   expression per property, so it never exercises history dependence through the
   hash-consing tables and memo caches. Monolith reuses previously produced BDDs
   as arguments to later operations, which is exactly the traffic that can
   surface cache-interaction bugs.

   The model is trusted; it is validated independently against Theo by
   test/test_model.ml (Phase 1). See test/support/model.ml for the finite-domain
   adequacy argument and the "consistent cubes only" decision. *)

open Monolith
module M = Model
module F = Theories.Formula

(* The BDD type, as an abstract type: reference values are truth tables
   ([Model.m]), candidate values are Theo BDDs ([Formula.t]). Monolith maintains
   the correspondence and feeds previously built values back into later
   operations. *)
let t = declare_abstract_type ()

(* Index specifications, one per variable pool. *)
let bool_ix = semi_open_interval 0 M.n_bool
let str_ix = semi_open_interval 0 M.n_str
let ver_ix = semi_open_interval 0 M.n_ver
let str_const_ix = semi_open_interval 0 (Array.length M.str_consts)
let ver_const_ix = semi_open_interval 0 (Array.length M.ver_consts)

(* Cubes are a constructible input type built directly from the pools (not an
   abstract type). The generator pins each variable at most once, so every cube
   is consistent by construction; see [Model.cube]. *)
let gen_cube : M.cube Gen.gen =
 fun () ->
  let pins = ref [] in
  for i = M.n_bool - 1 downto 0 do
    if Gen.bool () then pins := M.Bool_pin (i, Gen.bool ()) :: !pins
  done;
  for i = M.n_str - 1 downto 0 do
    if Gen.bool () then
      pins := M.Str_pin (i, Gen.int (Array.length M.str_consts) ()) :: !pins
  done;
  for i = M.n_ver - 1 downto 0 do
    if Gen.bool () then
      pins := M.Ver_pin (i, Gen.int (Array.length M.ver_consts) ()) :: !pins
  done;
  !pins

let doc_of_pin = function
  | M.Bool_pin (i, b) -> PPrint.string (Printf.sprintf "b%d:=%b" i b)
  | M.Str_pin (i, ci) ->
      PPrint.string (Printf.sprintf "s%d:=%S" i M.str_consts.(ci))
  | M.Ver_pin (i, ci) ->
      PPrint.string
        (Printf.sprintf "v%d:=%s" i
           (Theories.Version.to_string M.ver_consts.(ci)))

let cube = easily_constructible gen_cube (Print.list doc_of_pin)

(* [ite_constant] is deterministic, so it is a plain deconstructible result. *)
let print_constant_result = function
  | F.Constant b -> PPrint.string (Printf.sprintf "Constant %b" b)
  | F.NonConstant -> PPrint.string "NonConstant"

let constant_result = deconstructible print_constant_result

(* Explanation attached to a rejected nondeterministic result. *)
let invalid msg = Invalid (fun _observed -> Print.comment (PPrint.string msg))

let () =
  (* Constants. *)
  declare "true_" t M.Ref.true_ F.true_;
  declare "false_" t M.Ref.false_ F.false_;

  (* Atoms. Only the constructors and constants from the fixed pools are
     exposed; [Var.fresh] is never a fuzzing operation. *)
  declare "bool" (bool_ix ^> t) M.Ref.atom_bool M.Cand.atom_bool;
  declare "ver_atom"
    (ver_ix ^> ver_const_ix ^> bool ^> t)
    (fun i ci strict -> M.Ref.atom_ver i ~strict M.ver_consts.(ci))
    (fun i ci strict -> M.Cand.atom_ver i ~strict M.ver_consts.(ci));
  declare "str_atom"
    (str_ix ^> str_const_ix ^> t)
    (fun i ci -> M.Ref.atom_str i M.str_consts.(ci))
    (fun i ci -> M.Cand.atom_str i M.str_consts.(ci));

  (* Connectives. *)
  declare "not" (t ^> t) M.Ref.not_ F.not;
  declare "and_" (t ^> t ^> t) M.Ref.and_ F.and_;
  declare "or_" (t ^> t ^> t) M.Ref.or_ F.or_;
  declare "xor" (t ^> t ^> t) M.Ref.xor F.xor;
  declare "iff" (t ^> t ^> t) M.Ref.iff F.iff;
  declare "implies" (t ^> t ^> t) M.Ref.implies F.implies;
  declare "ite" (t ^> t ^> t ^> t) M.Ref.ite F.ite;

  (* Batch conjunction/disjunction. These are compositions of covered ops, but
     their divide-and-conquer reduction order produces different cache traffic
     than an equivalent fold of [and_]/[or_], so they are exercised in their own
     right. [list t] draws its elements from the previously produced BDDs in the
     environment; the reference mirror folds (see [Model.Ref.and_list]). *)
  declare "and_list" (list t ^> t) M.Ref.and_list M.Cand.and_list;
  declare "or_list" (list t ^> t) M.Ref.or_list M.Cand.or_list;

  (* Restrict / of_cube over consistent cubes. *)
  declare "restrict" (t ^> cube ^> t) M.restrict M.Cand.restrict;
  declare "of_cube" (cube ^> t) M.of_cube M.Cand.of_cube;

  (* Quantifiers, one operation per variable pool. *)
  declare "exists_bool" (bool_ix ^> t ^> t) M.Ref.exists_bool M.Cand.exists_bool;
  declare "exists_str" (str_ix ^> t ^> t) M.Ref.exists_str M.Cand.exists_str;
  declare "exists_ver" (ver_ix ^> t ^> t) M.Ref.exists_ver M.Cand.exists_ver;
  declare "forall_bool" (bool_ix ^> t ^> t) M.Ref.forall_bool M.Cand.forall_bool;
  declare "forall_str" (str_ix ^> t ^> t) M.Ref.forall_str M.Cand.forall_str;
  declare "forall_ver" (ver_ix ^> t ^> t) M.Ref.forall_ver M.Cand.forall_ver;

  (* Boolean observations, compared by value. *)
  declare "is_tautology" (t ^> bool) M.Ref.is_tautology F.is_tautology;
  declare "is_satisfiable" (t ^> bool) M.Ref.is_satisfiable F.is_satisfiable;
  declare "equivalent" (t ^> t ^> bool) M.Ref.equivalent F.equivalent;
  declare "logical_implies"
    (t ^> t ^> bool)
    M.Ref.logical_implies F.logical_implies;
  declare "is_disjoint" (t ^> t ^> bool) M.Ref.is_disjoint F.is_disjoint;
  declare "is_exhaustive" (t ^> t ^> bool) M.Ref.is_exhaustive F.is_exhaustive;

  (* Deterministic non-boolean observation. *)
  declare "ite_constant"
    (t ^> t ^> t ^> constant_result)
    M.Ref.ite_constant F.ite_constant;

  (* Nondeterministic observations: witnesses/covers are not comparable across
     implementations, so the reference checks the candidate result for validity
     (see [Model.sat_ok] / [Model.isop_ok]) rather than for equality. *)
  declare "sat" (t ^?> ignored)
    (fun a c ->
      if M.sat_ok a c then Valid c
      else invalid "sat: witness does not imply the formula (or is spurious)")
    F.sat;
  declare "shortest_sat" (t ^?> ignored)
    (fun a c ->
      if M.sat_ok a c then Valid c
      else
        invalid
          "shortest_sat: witness does not imply the formula (or is spurious)")
    F.shortest_sat;
  declare "irredundant_sop" (t ^?> ignored)
    (fun a cover ->
      if M.isop_ok a cover then Valid cover
      else invalid "irredundant_sop: cover is not equivalent to the formula")
    F.irredundant_sop;

  (* shortest_sat minimality.

     [shortest_sat] is documented (theo.mli) as the shortest *path in the BDD
     DAG*, which is NOT the semantically minimal satisfying cube -- the two
     provably differ. Concrete counterexample, reachable by the fuzzer:
     for [f = (b0 && b1) || b2] the shortest BDD path has length 2 (every
     root-to-true path must first traverse the root atom b0), yet the
     single-literal cube {b2} already implies f, so the semantic minimum is 1.
     Comparing [shortest_sat]'s length against the model's brute-force semantic
     minimum would therefore raise false alarms, so we do NOT check equality.
     (The semantic lower bound "model minimum <= length(shortest_sat f)" is
     sound but has no teeth: it is already implied by the witness-validity check
     on [shortest_sat] above, since any valid cube is at least as long as the
     minimal valid cube.)

     The teeth-bearing invariant we *can* check soundly is the upper bound: the
     shortest path is never longer than the greedy path returned by [sat] (which
     is one particular path). This distinguishes a correct minimiser from one
     that returns a non-shortest path. We express it as a boolean observation
     computed candidate-side (the Monolith nondeterministic checker only sees the
     model value and the witness, not [sat f]); the reference answer is the
     constant [true]. Both functions return [None] exactly when unsatisfiable. *)
  let sat_len f = Option.map List.length (F.sat f) in
  let shortest_len f = Option.map List.length (F.shortest_sat f) in
  declare "shortest_sat_le_sat" (t ^> bool)
    (fun _ -> true)
    (fun f ->
      match (shortest_len f, sat_len f) with
      | Some s, Some p -> s <= p
      | None, None -> true
      | Some _, None | None, Some _ -> false)

(* Fuel is the maximum scenario length. The cache-history bugs this harness
   targets need scenarios long enough to populate a cache and then hit the
   poisoned entry, so we default a little above Monolith's usual 15; in afl
   mode this cap also bounds how long the sequences grown by the corpus
   evolution can get. The command line can override it (--fuel N). *)
let () = main 25
