open Theo
open QCheck

(* Generators *)

let bool_var_pool = Array.init 10 (fun _ -> Theo.new_var Boolean)
let str_var_pool = Array.init 5 (fun _ -> Theo.new_var String)
let ver_var_pool = Array.init 5 (fun _ -> Theo.new_var Version)
let gen_str_val = Gen.oneofl [ "a"; "b"; "c" ]

let gen_ver_val =
  Gen.map3
    (fun x y z -> { major = x; minor = y; patch = z })
    (Gen.int_bound 5) (Gen.int_bound 5) (Gen.int_bound 5)

let gen_atom =
  Gen.oneof
    [
      Gen.map (fun i -> Theo.atom bool_var_pool.(i)) (Gen.int_bound 9);
      Gen.map2
        (fun i s -> Theo.is_equal str_var_pool.(i) s)
        (Gen.int_bound 4) gen_str_val;
      Gen.map2
        (fun i v -> Theo.is_lt ver_var_pool.(i) v)
        (Gen.int_bound 4) gen_ver_val;
      Gen.map2
        (fun i v -> Theo.is_le ver_var_pool.(i) v)
        (Gen.int_bound 4) gen_ver_val;
    ]

let rec gen_expr depth =
  if depth = 0 then gen_atom
  else
    Gen.oneof
      [
        gen_atom;
        Gen.map (fun e -> Theo.not e) (gen_expr (depth - 1));
        Gen.map2
          (fun a b -> Theo.and_ a b)
          (gen_expr (depth / 2))
          (gen_expr (depth / 2));
        Gen.map2
          (fun a b -> Theo.or_ a b)
          (gen_expr (depth / 2))
          (gen_expr (depth / 2));
      ]

let bdd_arbitrary = make (gen_expr 5) ~print:Theo.to_string

(* Properties *)

let prop_and_commits =
  Test.make ~name:"AND is commutative" ~count:2000
    (pair bdd_arbitrary bdd_arbitrary) (fun (a, b) ->
      Theo.equivalent (Theo.and_ a b) (Theo.and_ b a))

let prop_or_commits =
  Test.make ~name:"OR is commutative" ~count:2000
    (pair bdd_arbitrary bdd_arbitrary) (fun (a, b) ->
      Theo.equivalent (Theo.or_ a b) (Theo.or_ b a))

let prop_and_assoc =
  Test.make ~name:"AND is associative" ~count:2000
    (triple bdd_arbitrary bdd_arbitrary bdd_arbitrary) (fun (a, b, c) ->
      Theo.equivalent
        (Theo.and_ a (Theo.and_ b c))
        (Theo.and_ (Theo.and_ a b) c))

let prop_or_assoc =
  Test.make ~name:"OR is associative" ~count:2000
    (triple bdd_arbitrary bdd_arbitrary bdd_arbitrary) (fun (a, b, c) ->
      Theo.equivalent (Theo.or_ a (Theo.or_ b c)) (Theo.or_ (Theo.or_ a b) c))

let prop_distributivity_and_over_or =
  Test.make ~name:"Distributivity: a && (b || c) = (a && b) || (a && c)"
    ~count:2000 (triple bdd_arbitrary bdd_arbitrary bdd_arbitrary)
    (fun (a, b, c) ->
      Theo.equivalent
        (Theo.and_ a (Theo.or_ b c))
        (Theo.or_ (Theo.and_ a b) (Theo.and_ a c)))

let prop_distributivity_or_over_and =
  Test.make ~name:"Distributivity: a || (b && c) = (a || b) && (a || c)"
    ~count:2000 (triple bdd_arbitrary bdd_arbitrary bdd_arbitrary)
    (fun (a, b, c) ->
      Theo.equivalent
        (Theo.or_ a (Theo.and_ b c))
        (Theo.and_ (Theo.or_ a b) (Theo.or_ a c)))

let prop_absorption_1 =
  Test.make ~name:"Absorption: a || (a && b) = a" ~count:2000
    (pair bdd_arbitrary bdd_arbitrary) (fun (a, b) ->
      Theo.equivalent (Theo.or_ a (Theo.and_ a b)) a)

let prop_absorption_2 =
  Test.make ~name:"Absorption: a && (a || b) = a" ~count:2000
    (pair bdd_arbitrary bdd_arbitrary) (fun (a, b) ->
      Theo.equivalent (Theo.and_ a (Theo.or_ a b)) a)

let prop_identity_and =
  Test.make ~name:"Identity AND: a && true = a" ~count:2000 bdd_arbitrary
    (fun a -> Theo.equivalent (Theo.and_ a Theo.true_) a)

let prop_identity_or =
  Test.make ~name:"Identity OR: a || false = a" ~count:2000 bdd_arbitrary
    (fun a -> Theo.equivalent (Theo.or_ a Theo.false_) a)

let prop_implies_reflexivity =
  Test.make ~name:"Implies Reflexivity: a -> a" ~count:2000 bdd_arbitrary
    (fun a -> Theo.(is_tautology (implies a a)))

let prop_implies_consistency =
  Test.make ~name:"Implies Consistency: (a -> b) <=> (not a || b)" ~count:2000
    (pair bdd_arbitrary bdd_arbitrary) (fun (a, b) ->
      let impl = Theo.implies a b in
      let equiv_expr = Theo.or_ (Theo.not a) b in
      Theo.equivalent impl equiv_expr)

let prop_de_morgan_1 =
  Test.make ~name:"De Morgan: not (a && b) = (not a) || (not b)" ~count:2000
    (pair bdd_arbitrary bdd_arbitrary) (fun (a, b) ->
      Theo.equivalent
        (Theo.not (Theo.and_ a b))
        (Theo.or_ (Theo.not a) (Theo.not b)))

(* Set-Theoretic Properties *)

let prop_subset_transitivity =
  Test.make ~name:"Transitivity: (A <= B) && (B <= C) => (A <= C)" ~count:2000
    (triple bdd_arbitrary bdd_arbitrary bdd_arbitrary) (fun (a, b, c) ->
      if
        Stdlib.( && )
          (Theo.is_tautology (Theo.implies a b))
          (Theo.is_tautology (Theo.implies b c))
      then Theo.is_tautology (Theo.implies a c)
      else true)

let prop_subset_antisymmetry =
  Test.make ~name:"Antisymmetry: (A <= B) && (B <= A) => (A = B)" ~count:2000
    (pair bdd_arbitrary bdd_arbitrary) (fun (a, b) ->
      if
        Stdlib.( && )
          (Theo.is_tautology (Theo.implies a b))
          (Theo.is_tautology (Theo.implies b a))
      then Theo.equivalent a b
      else true)

let prop_difference_disjoint =
  Test.make ~name:"Difference: (A \\ B) && B = Empty" ~count:2000
    (pair bdd_arbitrary bdd_arbitrary) (fun (a, b) ->
      (* A \ B is A && (not B) *)
      let diff = Theo.and_ a (Theo.not b) in
      Theo.equivalent (Theo.and_ diff b) Theo.false_)

let prop_union_superset =
  Test.make ~name:"Union Superset: A <= (A U B)" ~count:2000
    (pair bdd_arbitrary bdd_arbitrary) (fun (a, b) ->
      Theo.is_tautology (Theo.implies a (Theo.or_ a b)))

let prop_intersection_subset =
  Test.make ~name:"Intersection Subset: (A ^ B) <= A" ~count:2000
    (pair bdd_arbitrary bdd_arbitrary) (fun (a, b) ->
      Theo.is_tautology (Theo.implies (Theo.and_ a b) a))

let prop_idempotence_and =
  Test.make ~name:"Idempotence AND: a && a = a" ~count:2000 bdd_arbitrary
    (fun a -> Theo.equivalent (Theo.and_ a a) a)

let prop_idempotence_or =
  Test.make ~name:"Idempotence OR: a || a = a" ~count:2000 bdd_arbitrary
    (fun a -> Theo.equivalent (Theo.or_ a a) a)

let prop_complement =
  Test.make ~name:"Complement: a && (not a) = false" ~count:2000 bdd_arbitrary
    (fun a -> Theo.equivalent (Theo.and_ a (Theo.not a)) Theo.false_)

(* Theory-Specific Properties *)

let idx_arb = make (Gen.int_bound 4) ~print:string_of_int

let ver_arb =
  make gen_ver_val ~print:(fun { major; minor; patch } ->
      Printf.sprintf "(%d,%d,%d)" major minor patch)

let str_arb = make gen_str_val ~print:(fun s -> s)

let prop_version_transitivity =
  Test.make ~name:"Version Transitivity: v < c1 && c1 < c2 => v < c2"
    ~count:2000
    (pair idx_arb (pair ver_arb ver_arb))
    (fun (idx, (v1, v2)) ->
      if v1 < v2 then
        let atom1 = Theo.is_lt ver_var_pool.(idx) v1 in
        let atom2 = Theo.is_lt ver_var_pool.(idx) v2 in
        (* v < v1 => v < v2 given v1 < v2 *)
        Theo.(is_tautology (implies atom1 atom2))
      else true)

let prop_version_consistency =
  Test.make ~name:"Version Consistency: v < c => v <= c" ~count:2000
    (pair idx_arb ver_arb) (fun (idx, v) ->
      let lt = Theo.is_lt ver_var_pool.(idx) v in
      let le = Theo.is_le ver_var_pool.(idx) v in
      Theo.(is_tautology (implies lt le)))

let prop_version_partition =
  Test.make ~name:"Version Partition: v < c || v = c || v > c is True"
    ~count:2000 (pair idx_arb ver_arb) (fun (idx, v) ->
      let lt = Theo.is_lt ver_var_pool.(idx) v in
      let le = Theo.is_le ver_var_pool.(idx) v in
      let eq = Theo.and_ le (Theo.not lt) in
      let gt = Theo.not le in
      Theo.(is_tautology (or_list [ lt; eq; gt ])))

let prop_string_mutual_exclusive =
  Test.make ~name:"String Mutually Exclusive: s=a && s=b => False (if a!=b)"
    ~count:2000 (triple idx_arb str_arb str_arb) (fun (idx, s1, s2) ->
      if s1 <> s2 then
        let eq1 = Theo.is_equal str_var_pool.(idx) s1 in
        let eq2 = Theo.is_equal str_var_pool.(idx) s2 in
        Theo.(equivalent (and_ eq1 eq2) false_)
      else true)

let prop_interval_union_order =
  Test.make
    ~name:
      "Interval Union Order: or_list (shuffle intervals) = or_list intervals"
    ~count:2000
    (pair idx_arb (small_list (pair ver_arb ver_arb)))
    (fun (idx, intervals) ->
      let make_interval (v1, v2) =
        if v1 < v2 then
          (* v > v1, wait, we want v >= v1 *)
          (* Actually let's use: v >= v1 && v < v2 *)
          (* v >= v1 is not (v < v1) *)
          let ge_v1 = Theo.not (Theo.is_lt ver_var_pool.(idx) v1) in
          let lt_v2 = Theo.is_lt ver_var_pool.(idx) v2 in
          Theo.and_ ge_v1 lt_v2
        else Theo.false_
      in
      let exprs = List.map make_interval intervals in
      let reversed_exprs = List.rev exprs in
      Theo.equivalent (Theo.or_list exprs) (Theo.or_list reversed_exprs))

let prop_sat_model =
  Test.make ~name:"SAT Model Check: sat(f) -> m => (m implies f)" ~count:2000
    bdd_arbitrary (fun expr ->
      match Theo.sat expr with
      | Some constraints ->
          let model_expr =
            List.map
              (function
                | Theo.Boolean (v, b) ->
                    if b then Theo.atom v else Theo.not (Theo.atom v)
                | Theo.String (v, op, s) -> (
                    match op with
                    | `Eq -> Theo.is_equal v s
                    | `Ne -> Theo.not (Theo.is_equal v s))
                | Theo.Version (v, op, ver) -> (
                    match op with
                    | `Lt -> Theo.is_lt v ver
                    | `Le -> Theo.is_le v ver
                    | `Gt -> Theo.not (Theo.is_le v ver)
                    | `Ge -> Theo.not (Theo.is_lt v ver)))
              constraints
            |> Theo.and_list
          in
          Theo.is_tautology (Theo.implies model_expr expr)
      | None -> Theo.equivalent expr Theo.false_)

(* Fuzzing: Naive Representation vs BDD *)

type naive_atom =
  | NBool of bool var
  | NStrEq of string var * string
  | NStrNe of string var * string
  | NVerLt of version var * version
  | NVerLe of version var * version
  | NVerGt of version var * version
  | NVerGe of version var * version

type naive_expr =
  | NAtom of naive_atom
  | NNot of naive_expr
  | NAnd of naive_expr * naive_expr
  | NOr of naive_expr * naive_expr
  | NTrue
  | NFalse

let rec naive_to_bdd = function
  | NAtom (NBool v) -> Theo.atom v
  | NAtom (NStrEq (v, s)) -> Theo.is_equal v s
  | NAtom (NStrNe (v, s)) -> Theo.is_not_equal v s
  | NAtom (NVerLt (v, ver)) -> Theo.is_lt v ver
  | NAtom (NVerLe (v, ver)) -> Theo.is_le v ver
  | NAtom (NVerGt (v, ver)) -> Theo.is_gt v ver
  | NAtom (NVerGe (v, ver)) -> Theo.is_ge v ver
  | NNot e -> Theo.not (naive_to_bdd e)
  | NAnd (e1, e2) -> Theo.and_ (naive_to_bdd e1) (naive_to_bdd e2)
  | NOr (e1, e2) -> Theo.or_ (naive_to_bdd e1) (naive_to_bdd e2)
  | NTrue -> Theo.true_
  | NFalse -> Theo.false_

(* World Generation *)
type world = {
  bools : (bool var, bool) Hashtbl.t;
  strs : (string var, string) Hashtbl.t;
  vers : (version var, version) Hashtbl.t;
}

let gen_world =
  Gen.map3
    (fun bls strs vers ->
      let w =
        {
          bools = Hashtbl.create 16;
          strs = Hashtbl.create 16;
          vers = Hashtbl.create 16;
        }
      in
      Array.iteri
        (fun i v -> Hashtbl.replace w.bools v (List.nth bls i))
        bool_var_pool;
      Array.iteri
        (fun i v -> Hashtbl.replace w.strs v (List.nth strs i))
        str_var_pool;
      Array.iteri
        (fun i v -> Hashtbl.replace w.vers v (List.nth vers i))
        ver_var_pool;
      w)
    (Gen.list_size (Gen.return (Array.length bool_var_pool)) Gen.bool)
    (Gen.list_size (Gen.return (Array.length str_var_pool)) gen_str_val)
    (Gen.list_size (Gen.return (Array.length ver_var_pool)) gen_ver_val)

let compare_raw_version ({ major; minor; patch } : version)
    ({ major = major'; minor = minor'; patch = patch' } : version) =
  let c = Int.compare major major' in
  if c <> 0 then c
  else
    let c = Int.compare minor minor' in
    if c <> 0 then c else Int.compare patch patch'

let eval_atom_in_world (a : naive_atom) (w : world) =
  let get_bool v = Option.value (Hashtbl.find_opt w.bools v) ~default:false in
  let get_str v = Option.value (Hashtbl.find_opt w.strs v) ~default:"" in
  let get_ver v =
    Option.value
      (Hashtbl.find_opt w.vers v)
      ~default:{ major = 0; minor = 0; patch = 0 }
  in
  match a with
  | NBool v -> get_bool v
  | NStrEq (v, s) -> String.equal (get_str v) s
  | NStrNe (v, s) -> Stdlib.not (String.equal (get_str v) s)
  | NVerLt (v, ver) -> compare_raw_version (get_ver v) ver < 0
  | NVerLe (v, ver) -> compare_raw_version (get_ver v) ver <= 0
  | NVerGt (v, ver) -> compare_raw_version (get_ver v) ver > 0
  | NVerGe (v, ver) -> compare_raw_version (get_ver v) ver >= 0

let rec eval_naive expr w =
  match expr with
  | NAtom a -> eval_atom_in_world a w
  | NNot e -> Stdlib.not (eval_naive e w)
  | NAnd (e1, e2) -> eval_naive e1 w && eval_naive e2 w
  | NOr (e1, e2) -> eval_naive e1 w || eval_naive e2 w
  | NTrue -> true
  | NFalse -> false

let world_to_constraints w =
  let constraints = ref [] in
  (* Strategy change: Iterate over all variables in our pools.
     If they are in the world map, add constraint. *)
  let add_bool_constraints () =
    Array.iter
      (fun v ->
        match Hashtbl.find_opt w.bools v with
        | Some b -> constraints := Theo.Boolean (v, b) :: !constraints
        | None -> ())
      bool_var_pool
  in
  let add_str_constraints () =
    Array.iter
      (fun v ->
        match Hashtbl.find_opt w.strs v with
        | Some s -> constraints := Theo.String (v, `Eq, s) :: !constraints
        | None -> ())
      str_var_pool
  in
  let add_ver_constraints () =
    Array.iter
      (fun v ->
        match Hashtbl.find_opt w.vers v with
        | Some ver ->
            constraints := Theo.Version (v, `Ge, ver) :: !constraints;
            constraints := Theo.Version (v, `Le, ver) :: !constraints
        | None -> ())
      ver_var_pool
  in
  add_bool_constraints ();
  add_str_constraints ();
  add_ver_constraints ();
  !constraints

let gen_naive_atom =
  Gen.oneof
    [
      Gen.map (fun i -> NBool bool_var_pool.(i)) (Gen.int_bound 9);
      Gen.map2
        (fun i s -> NStrEq (str_var_pool.(i), s))
        (Gen.int_bound 4) gen_str_val;
      Gen.map2
        (fun i s -> NStrNe (str_var_pool.(i), s))
        (Gen.int_bound 4) gen_str_val;
      Gen.map2
        (fun i v -> NVerLt (ver_var_pool.(i), v))
        (Gen.int_bound 4) gen_ver_val;
      Gen.map2
        (fun i v -> NVerLe (ver_var_pool.(i), v))
        (Gen.int_bound 4) gen_ver_val;
      Gen.map2
        (fun i v -> NVerGt (ver_var_pool.(i), v))
        (Gen.int_bound 4) gen_ver_val;
      Gen.map2
        (fun i v -> NVerGe (ver_var_pool.(i), v))
        (Gen.int_bound 4) gen_ver_val;
    ]

let rec gen_naive_expr depth =
  if depth = 0 then
    Gen.oneof
      [
        Gen.map (fun a -> NAtom a) gen_naive_atom;
        Gen.return NTrue;
        Gen.return NFalse;
      ]
  else
    Gen.oneof
      [
        Gen.map (fun a -> NAtom a) gen_naive_atom;
        Gen.return NTrue;
        Gen.return NFalse;
        Gen.map (fun e -> NNot e) (gen_naive_expr (depth - 1));
        Gen.map2
          (fun e1 e2 -> NAnd (e1, e2))
          (gen_naive_expr (depth / 2))
          (gen_naive_expr (depth / 2));
        Gen.map2
          (fun e1 e2 -> NOr (e1, e2))
          (gen_naive_expr (depth / 2))
          (gen_naive_expr (depth / 2));
      ]

let prop_fuzz_evaluation =
  Test.make ~name:"Fuzzing: Naive Eval = BDD Restrict" ~count:10000
    (pair (make (gen_naive_expr 4)) (make gen_world))
    (fun (naive, world) ->
      let bdd = naive_to_bdd naive in
      let expected_bool = eval_naive naive world in
      let constraints = world_to_constraints world in
      let restricted_bdd = Theo.restrict bdd constraints in
      if expected_bool then Theo.equivalent restricted_bdd Theo.true_
      else Theo.equivalent restricted_bdd Theo.false_)

let bdd_arbitrary = make (Gen.map naive_to_bdd (gen_naive_expr 4))

let prop_ite_constant_consistent =
  Test.make ~name:"ite_constant consistent with ite" ~count:2000
    (triple bdd_arbitrary bdd_arbitrary bdd_arbitrary) (fun (f, g, h) ->
      let res_ite = Theo.ite f g h in
      let res_const = Theo.ite_constant f g h in
      let ite_is_true = Theo.equivalent res_ite Theo.true_ in
      let ite_is_false = Theo.equivalent res_ite Theo.false_ in
      match res_const with
      | Theo.Constant true -> ite_is_true
      | Theo.Constant false -> ite_is_false
      | Theo.NonConstant -> Stdlib.not ite_is_true && Stdlib.not ite_is_false)

let prop_quantifier_duality =
  Test.make ~name:"Quantifier Duality: exists x. f <=> not (forall x. not f)"
    ~count:2000 (pair idx_arb bdd_arbitrary) (fun (idx, f) ->
      let v = bool_var_pool.(idx) in
      let lhs = Theo.exists v f in
      let rhs = Theo.not (Theo.forall v (Theo.not f)) in
      Theo.equivalent lhs rhs)

let prop_quantifier_distributivity_exists_or =
  Test.make
    ~name:
      "Quantifier Distributivity: exists x. (f || g) <=> (exists x. f) || \
       (exists x. g)" ~count:2000 (triple idx_arb bdd_arbitrary bdd_arbitrary)
    (fun (idx, f, g) ->
      let v = bool_var_pool.(idx) in
      let lhs = Theo.exists v (Theo.or_ f g) in
      let rhs = Theo.or_ (Theo.exists v f) (Theo.exists v g) in
      Theo.equivalent lhs rhs)

let prop_quantifier_distributivity_forall_and =
  Test.make
    ~name:
      "Quantifier Distributivity: forall x. (f && g) <=> (forall x. f) && \
       (forall x. g)" ~count:2000 (triple idx_arb bdd_arbitrary bdd_arbitrary)
    (fun (idx, f, g) ->
      let v = bool_var_pool.(idx) in
      let lhs = Theo.forall v (Theo.and_ f g) in
      let rhs = Theo.and_ (Theo.forall v f) (Theo.forall v g) in
      Theo.equivalent lhs rhs)

let () =
  QCheck_runner.run_tests_main
    [
      prop_and_commits;
      prop_or_commits;
      prop_and_assoc;
      prop_or_assoc;
      prop_distributivity_and_over_or;
      prop_distributivity_or_over_and;
      prop_absorption_1;
      prop_absorption_2;
      prop_identity_and;
      prop_identity_or;
      prop_implies_reflexivity;
      prop_implies_consistency;
      prop_de_morgan_1;
      prop_idempotence_and;
      prop_idempotence_or;
      prop_complement;
      prop_subset_transitivity;
      prop_subset_antisymmetry;
      prop_difference_disjoint;
      prop_union_superset;
      prop_intersection_subset;
      prop_version_transitivity;
      prop_version_consistency;
      prop_version_partition;
      prop_string_mutual_exclusive;
      prop_interval_union_order;
      prop_sat_model;
      prop_ite_constant_consistent;
      prop_fuzz_evaluation;
      prop_quantifier_duality;
      prop_quantifier_distributivity_exists_or;
      prop_quantifier_distributivity_forall_and;
    ]
