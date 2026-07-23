(* Phase 1 self-tests: check the reference model in test/support/model.ml
   against Theo itself.

   The Monolith harness in fuzz/ trusts [Model] as an oracle: if the model is
   wrong, every fuzz report is noise. So, before building anything on top of it,
   we generate random formulas (and cubes, and quantified variables) with QCheck
   and check that, for the operation the Monolith harness relies on, the model's
   answer agrees with Theo's. This exercises atoms, every connective, the batch
   operations [and_list]/[or_list], [restrict], [of_cube], the quantifiers, and
   the nondeterministic observations [sat], [shortest_sat] and [irredundant_sop]
   -- all against the same [expr] AST that feeds the harness. These tests do not
   depend on monolith. *)

open QCheck
module M = Model
module F = Theories.Formula

(* Generators over the fixed pools. *)

(* Generate only CONSISTENT cubes: each variable is pinned at most once (to a
   single value), so a cube never asserts contradictory literals. This is the
   choice the plan settles on for the "restrict with contradictory constraints"
   open question -- see the comment on [Model.cube]. *)
let gen_cube =
  let open Gen in
  let maybe_pin mk n_val i =
    oneof [ return None; map (fun v -> Some (mk i v)) (int_bound (n_val - 1)) ]
  in
  let collect gens = map (List.filter_map Fun.id) (flatten_list gens) in
  let bools =
    List.init M.n_bool (fun i ->
        maybe_pin (fun i b -> M.Bool_pin (i, b = 1)) 2 i)
  in
  let strs =
    List.init M.n_str (fun i ->
        maybe_pin (fun i ci -> M.Str_pin (i, ci)) (Array.length M.str_consts) i)
  in
  let vers =
    List.init M.n_ver (fun i ->
        maybe_pin (fun i ci -> M.Ver_pin (i, ci)) (Array.length M.ver_consts) i)
  in
  collect (bools @ strs @ vers)

let gen_vsel =
  let open Gen in
  oneof
    [
      map (fun i -> M.VBool i) (int_bound (M.n_bool - 1));
      map (fun i -> M.VStr i) (int_bound (M.n_str - 1));
      map (fun i -> M.VVer i) (int_bound (M.n_ver - 1));
    ]

let gen_atom =
  let open Gen in
  oneof
    [
      return M.True;
      return M.False;
      map (fun i -> M.ABool i) (int_bound (M.n_bool - 1));
      map3
        (fun i ci s -> M.AVer (i, ci, s))
        (int_bound (M.n_ver - 1))
        (int_bound (Array.length M.ver_consts - 1))
        bool;
      map2
        (fun i ci -> M.AStr (i, ci))
        (int_bound (M.n_str - 1))
        (int_bound (Array.length M.str_consts - 1));
    ]

let rec gen_expr depth =
  let open Gen in
  if depth <= 0 then gen_atom
  else
    let sub = gen_expr (depth - 1) in
    let sub2 = gen_expr (depth / 2) in
    oneof
      [
        gen_atom;
        map (fun e -> M.Not e) sub;
        map2 (fun a b -> M.And (a, b)) sub2 sub2;
        map2 (fun a b -> M.Or (a, b)) sub2 sub2;
        map2 (fun a b -> M.Xor (a, b)) sub2 sub2;
        map2 (fun a b -> M.Iff (a, b)) sub2 sub2;
        map2 (fun a b -> M.Implies (a, b)) sub2 sub2;
        map3 (fun f g h -> M.Ite (f, g, h)) sub2 sub2 sub2;
        map2 (fun e c -> M.Restrict (e, c)) sub gen_cube;
        map (fun c -> M.OfCube c) gen_cube;
        map2 (fun v e -> M.Exists (v, e)) gen_vsel sub;
        map2 (fun v e -> M.Forall (v, e)) gen_vsel sub;
      ]

let expr = make ~print:(fun _ -> "<expr>") (gen_expr 4)

(* Small lists of expressions, for the batch operations [and_list]/[or_list]. *)
let expr_list =
  make
    ~print:(fun _ -> "<expr list>")
    (Gen.list_size (Gen.int_bound 5) (gen_expr 3))

let count = 1000

(* Unary observations. *)

let prop_tautology =
  Test.make ~name:"model is_tautology = Theo is_tautology" ~count expr (fun e ->
      M.Ref.is_tautology (M.eval e) = F.is_tautology (M.to_bdd e))

let prop_satisfiable =
  Test.make ~name:"model is_satisfiable = Theo is_satisfiable" ~count expr
    (fun e -> M.Ref.is_satisfiable (M.eval e) = F.is_satisfiable (M.to_bdd e))

let prop_ite_constant =
  Test.make ~name:"model ite_constant = Theo ite_constant" ~count
    (triple expr expr expr) (fun (f, g, h) ->
      let ref_r = M.Ref.ite_constant (M.eval f) (M.eval g) (M.eval h) in
      let cand_r = F.ite_constant (M.to_bdd f) (M.to_bdd g) (M.to_bdd h) in
      match (ref_r, cand_r) with
      | F.Constant a, F.Constant b -> a = b
      | F.NonConstant, F.NonConstant -> true
      | _ -> false)

(* Batch operations. The model folds [and_]/[or_]; the library reduces with a
   divide-and-conquer strategy. Check that the model and Theo classify every
   world identically (via is_tautology/is_satisfiable), and anchor Theo's batch
   result against the plain fold (which the connective tests already trust). *)

let prop_and_list =
  Test.make ~name:"model and_list agrees with Theo and_list" ~count expr_list
    (fun es ->
      let ms = List.map M.eval es in
      let bdds = List.map M.to_bdd es in
      M.Ref.is_tautology (M.Ref.and_list ms) = F.is_tautology (F.and_list bdds)
      && M.Ref.is_satisfiable (M.Ref.and_list ms)
         = F.is_satisfiable (F.and_list bdds)
      && F.equivalent (F.and_list bdds) (List.fold_left F.and_ F.true_ bdds))

let prop_or_list =
  Test.make ~name:"model or_list agrees with Theo or_list" ~count expr_list
    (fun es ->
      let ms = List.map M.eval es in
      let bdds = List.map M.to_bdd es in
      M.Ref.is_tautology (M.Ref.or_list ms) = F.is_tautology (F.or_list bdds)
      && M.Ref.is_satisfiable (M.Ref.or_list ms)
         = F.is_satisfiable (F.or_list bdds)
      && F.equivalent (F.or_list bdds) (List.fold_left F.or_ F.false_ bdds))

(* Binary observations. *)

let prop_equivalent =
  Test.make ~name:"model equivalent = Theo equivalent" ~count (pair expr expr)
    (fun (a, b) ->
      M.Ref.equivalent (M.eval a) (M.eval b)
      = F.equivalent (M.to_bdd a) (M.to_bdd b))

let prop_logical_implies =
  Test.make ~name:"model logical_implies = Theo logical_implies" ~count
    (pair expr expr) (fun (a, b) ->
      M.Ref.logical_implies (M.eval a) (M.eval b)
      = F.logical_implies (M.to_bdd a) (M.to_bdd b))

let prop_is_disjoint =
  Test.make ~name:"model is_disjoint = Theo is_disjoint" ~count (pair expr expr)
    (fun (a, b) ->
      M.Ref.is_disjoint (M.eval a) (M.eval b)
      = F.is_disjoint (M.to_bdd a) (M.to_bdd b))

let prop_is_exhaustive =
  Test.make ~name:"model is_exhaustive = Theo is_exhaustive" ~count
    (pair expr expr) (fun (a, b) ->
      M.Ref.is_exhaustive (M.eval a) (M.eval b)
      = F.is_exhaustive (M.to_bdd a) (M.to_bdd b))

(* Nondeterministic observations: check the library result is acceptable to the
   model's validity oracle (the same oracle the harness uses). *)

let prop_sat =
  Test.make ~name:"Theo sat witness accepted by model" ~count expr (fun e ->
      M.sat_ok (M.eval e) (F.sat (M.to_bdd e)))

let prop_shortest_sat =
  Test.make ~name:"Theo shortest_sat witness accepted by model" ~count expr
    (fun e -> M.sat_ok (M.eval e) (F.shortest_sat (M.to_bdd e)))

let prop_irredundant_sop =
  Test.make ~name:"Theo irredundant_sop cover accepted by model" ~count expr
    (fun e -> M.isop_ok (M.eval e) (F.irredundant_sop (M.to_bdd e)))

(* The shortest_sat minimality invariant checked by the harness: the shortest
   BDD path is never longer than the greedy [sat] path, and both return [None]
   exactly when unsatisfiable. This is a library invariant (no model value is
   involved), but it is cheap to guard here too. See the extended comment in
   fuzz/main.fuzz.ml for why length equality against a semantic minimum would
   false-alarm. *)
let prop_shortest_sat_le_sat =
  Test.make ~name:"Theo shortest_sat no longer than sat" ~count expr (fun e ->
      let f = M.to_bdd e in
      let len o = Option.map List.length o in
      match (len (F.shortest_sat f), len (F.sat f)) with
      | Some s, Some p -> s <= p
      | None, None -> true
      | Some _, None | None, Some _ -> false)

let () =
  QCheck_runner.run_tests_main
    [
      prop_tautology;
      prop_satisfiable;
      prop_ite_constant;
      prop_and_list;
      prop_or_list;
      prop_equivalent;
      prop_logical_implies;
      prop_is_disjoint;
      prop_is_exhaustive;
      prop_sat;
      prop_shortest_sat;
      prop_irredundant_sop;
      prop_shortest_sat_le_sat;
    ]
