open Theories
open QCheck

(* Use F for Formula to avoid shadowing Theo library *)
module F = Formula

(* Constraint construction helpers *)
let c_bool v b = F.Constraint.bool v b
let c_str_eq v s = F.Constraint.atom v Eq.category (Right (Eq.Const s))

let c_ver_le v limit =
  F.Constraint.atom v Leq.category
    (Left (Leq.Bound { limit; inclusive = true }))

let c_ver_lt v limit =
  F.Constraint.atom v Leq.category
    (Left (Leq.Bound { limit; inclusive = false }))

let c_ver_ge v limit = F.Constraint.not (c_ver_lt v limit)

(* Generators *)

let bool_var_pool = Array.init 10 (fun _ -> Theo.Var.fresh ())
let str_var_pool = Array.init 5 (fun _ -> Theo.Var.fresh ())
let ver_var_pool = Array.init 5 (fun _ -> Theo.Var.fresh ())
let gen_str_val = Gen.oneofl [ "a"; "b"; "c" ]

let gen_ver_val =
  QCheck.Gen.(
    map
      (fun (major, minor, patch) -> { Version.major; minor; patch })
      (triple (int_bound 5) (int_bound 5) (int_bound 5)))

(* Helper to access syntax locally *)
module Syn = Formula.Syntax
module VerSyn = VersionSyntax
module StrSyn = StringSyntax

let gen_atom =
  Gen.oneof
    [
      Gen.map (fun i -> Syn.bool bool_var_pool.(i)) (Gen.int_bound 9);
      Gen.map2
        (fun i s -> StrSyn.(str_var_pool.(i) = s))
        (Gen.int_bound 4) gen_str_val;
      Gen.map2
        (fun i v -> VerSyn.(ver_var_pool.(i) < v))
        (Gen.int_bound 4) gen_ver_val;
      Gen.map2
        (fun i v -> VerSyn.(ver_var_pool.(i) <= v))
        (Gen.int_bound 4) gen_ver_val;
    ]

let rec gen_expr depth =
  if depth = 0 then gen_atom
  else
    Gen.oneof
      [
        gen_atom;
        Gen.map (fun e -> Syn.not e) (gen_expr (depth - 1));
        Gen.map2
          (fun a b -> Syn.( && ) a b)
          (gen_expr (depth / 2))
          (gen_expr (depth / 2));
        Gen.map2
          (fun a b -> Syn.( || ) a b)
          (gen_expr (depth / 2))
          (gen_expr (depth / 2));
      ]

let bdd_arbitrary = make (gen_expr 5) ~print:F.to_string

(* Properties *)

let prop_and_commits =
  Test.make ~name:"AND is commutative" ~count:2000
    (pair bdd_arbitrary bdd_arbitrary) (fun (a, b) ->
      F.equivalent (F.and_ a b) (F.and_ b a))

let prop_or_commits =
  Test.make ~name:"OR is commutative" ~count:2000
    (pair bdd_arbitrary bdd_arbitrary) (fun (a, b) ->
      F.equivalent (F.or_ a b) (F.or_ b a))

let prop_and_assoc =
  Test.make ~name:"AND is associative" ~count:2000
    (triple bdd_arbitrary bdd_arbitrary bdd_arbitrary) (fun (a, b, c) ->
      F.equivalent (F.and_ a (F.and_ b c)) (F.and_ (F.and_ a b) c))

let prop_or_assoc =
  Test.make ~name:"OR is associative" ~count:2000
    (triple bdd_arbitrary bdd_arbitrary bdd_arbitrary) (fun (a, b, c) ->
      F.equivalent (F.or_ a (F.or_ b c)) (F.or_ (F.or_ a b) c))

let prop_distributivity_and_over_or =
  Test.make ~name:"Distributivity: a && (b || c) = (a && b) || (a && c)"
    ~count:2000 (triple bdd_arbitrary bdd_arbitrary bdd_arbitrary)
    (fun (a, b, c) ->
      F.equivalent (F.and_ a (F.or_ b c)) (F.or_ (F.and_ a b) (F.and_ a c)))

let prop_distributivity_or_over_and =
  Test.make ~name:"Distributivity: a || (b && c) = (a || b) && (a || c)"
    ~count:2000 (triple bdd_arbitrary bdd_arbitrary bdd_arbitrary)
    (fun (a, b, c) ->
      F.equivalent (F.or_ a (F.and_ b c)) (F.and_ (F.or_ a b) (F.or_ a c)))

let prop_absorption_1 =
  Test.make ~name:"Absorption: a || (a && b) = a" ~count:2000
    (pair bdd_arbitrary bdd_arbitrary) (fun (a, b) ->
      F.equivalent (F.or_ a (F.and_ a b)) a)

let prop_absorption_2 =
  Test.make ~name:"Absorption: a && (a || b) = a" ~count:2000
    (pair bdd_arbitrary bdd_arbitrary) (fun (a, b) ->
      F.equivalent (F.and_ a (F.or_ a b)) a)

let prop_identity_and =
  Test.make ~name:"Identity AND: a && true = a" ~count:2000 bdd_arbitrary
    (fun a -> F.equivalent (F.and_ a F.true_) a)

let prop_identity_or =
  Test.make ~name:"Identity OR: a || false = a" ~count:2000 bdd_arbitrary
    (fun a -> F.equivalent (F.or_ a F.false_) a)

let prop_implies_reflexivity =
  Test.make ~name:"Implies Reflexivity: a -> a" ~count:2000 bdd_arbitrary
    (fun a -> F.is_tautology (F.implies a a))

let prop_implies_consistency =
  Test.make ~name:"Implies Consistency: (a -> b) <=> (not a || b)" ~count:2000
    (pair bdd_arbitrary bdd_arbitrary) (fun (a, b) ->
      let impl = F.implies a b in
      let equiv_expr = F.or_ (F.not a) b in
      F.equivalent impl equiv_expr)

let prop_de_morgan_1 =
  Test.make ~name:"De Morgan: not (a && b) = (not a) || (not b)" ~count:2000
    (pair bdd_arbitrary bdd_arbitrary) (fun (a, b) ->
      F.equivalent (F.not (F.and_ a b)) (F.or_ (F.not a) (F.not b)))

(* Set-Theoretic Properties *)

let prop_subset_transitivity =
  Test.make ~name:"Transitivity: (A <= B) && (B <= C) => (A <= C)" ~count:2000
    (triple bdd_arbitrary bdd_arbitrary bdd_arbitrary) (fun (a, b, c) ->
      if
        Stdlib.( && )
          (F.is_tautology (F.implies a b))
          (F.is_tautology (F.implies b c))
      then F.is_tautology (F.implies a c)
      else true)

let prop_subset_antisymmetry =
  Test.make ~name:"Antisymmetry: (A <= B) && (B <= A) => (A = B)" ~count:2000
    (pair bdd_arbitrary bdd_arbitrary) (fun (a, b) ->
      if
        Stdlib.( && )
          (F.is_tautology (F.implies a b))
          (F.is_tautology (F.implies b a))
      then F.equivalent a b
      else true)

let prop_difference_disjoint =
  Test.make ~name:"Difference: (A \\ B) && B = Empty" ~count:2000
    (pair bdd_arbitrary bdd_arbitrary) (fun (a, b) ->
      (* A \ B is A && (not B) *)
      let diff = F.and_ a (F.not b) in
      F.equivalent (F.and_ diff b) F.false_)

let prop_union_superset =
  Test.make ~name:"Union Superset: A <= (A U B)" ~count:2000
    (pair bdd_arbitrary bdd_arbitrary) (fun (a, b) ->
      F.is_tautology (F.implies a (F.or_ a b)))

let prop_intersection_subset =
  Test.make ~name:"Intersection Subset: (A ^ B) <= A" ~count:2000
    (pair bdd_arbitrary bdd_arbitrary) (fun (a, b) ->
      F.is_tautology (F.implies (F.and_ a b) a))

let prop_idempotence_and =
  Test.make ~name:"Idempotence AND: a && a = a" ~count:2000 bdd_arbitrary
    (fun a -> F.equivalent (F.and_ a a) a)

let prop_idempotence_or =
  Test.make ~name:"Idempotence OR: a || a = a" ~count:2000 bdd_arbitrary
    (fun a -> F.equivalent (F.or_ a a) a)

let prop_complement =
  Test.make ~name:"Complement: a && (not a) = false" ~count:2000 bdd_arbitrary
    (fun a -> F.equivalent (F.and_ a (F.not a)) F.false_)

(* Theory-Specific Properties *)

let idx_arb = make (Gen.int_bound 4) ~print:string_of_int

let ver_arb =
  make gen_ver_val ~print:(fun { Version.major; minor; patch } ->
      Printf.sprintf "(%d,%d,%d)" major minor patch)

let str_arb = make gen_str_val ~print:(fun s -> s)

let prop_version_transitivity =
  Test.make ~name:"Version Transitivity: v < c1 && c1 < c2 => v < c2"
    ~count:2000
    (pair idx_arb (pair ver_arb ver_arb))
    (fun (idx, (v1, v2)) ->
      if Version.compare v1 v2 < 0 then
        let atom1 = VerSyn.(ver_var_pool.(idx) < v1) in
        let atom2 = VerSyn.(ver_var_pool.(idx) < v2) in
        (* v < v1 => v < v2 given v1 < v2 *)
        F.is_tautology (F.implies atom1 atom2)
      else true)

let prop_version_consistency =
  Test.make ~name:"Version Consistency: v < c => v <= c" ~count:2000
    (pair idx_arb ver_arb) (fun (idx, c) ->
      let lt = VerSyn.(ver_var_pool.(idx) < c) in
      let le = VerSyn.(ver_var_pool.(idx) <= c) in
      let res = F.is_tautology (F.implies lt le) in
      if not res then (
        Printf.printf "Check Consist FAILURE: v%d < %s => v%d <= %s\n" idx
          (Version.to_string c) idx (Version.to_string c);
        Printf.printf "LT: %s\nLE: %s\n" (F.to_string lt) (F.to_string le);
        let imp = F.implies lt le in
        Printf.printf "Implies BDD: %s\n" (F.to_string imp));
      res)

let prop_version_partition =
  Test.make ~name:"Version Partition: v < c || v = c || v > c is True"
    ~count:2000 (pair idx_arb ver_arb) (fun (idx, v) ->
      let lt = VerSyn.(ver_var_pool.(idx) < v) in
      let le = VerSyn.(ver_var_pool.(idx) <= v) in
      let eq = F.and_ le (F.not lt) in
      let gt = F.not le in
      F.is_tautology (F.or_list [ lt; eq; gt ]))

let prop_string_mutual_exclusive =
  Test.make ~name:"String Mutually Exclusive: s=a && s=b => False (if a!=b)"
    ~count:2000 (triple idx_arb str_arb str_arb) (fun (idx, s1, s2) ->
      if s1 <> s2 then
        let eq1 = StrSyn.(str_var_pool.(idx) = s1) in
        let eq2 = StrSyn.(str_var_pool.(idx) = s2) in
        F.equivalent (F.and_ eq1 eq2) F.false_
      else true)

let prop_interval_union_order =
  Test.make
    ~name:
      "Interval Union Order: or_list (shuffle intervals) = or_list intervals"
    ~count:2000
    (pair idx_arb (small_list (pair ver_arb ver_arb)))
    (fun (idx, intervals) ->
      let make_interval (v1, v2) =
        if Version.compare v1 v2 < 0 then
          let ge_v1 = VerSyn.(ver_var_pool.(idx) >= v1) in
          let lt_v2 = VerSyn.(ver_var_pool.(idx) < v2) in
          F.and_ ge_v1 lt_v2
        else F.false_
      in
      let exprs = List.map make_interval intervals in
      let reversed_exprs = List.rev exprs in
      F.equivalent (F.or_list exprs) (F.or_list reversed_exprs))

let prop_sat_model =
  Test.make ~name:"SAT Model Check: sat(f) -> m => (m implies f)" ~count:2000
    bdd_arbitrary (fun expr ->
      match F.sat expr with
      | Some constraints ->
          let model_expr =
            List.map
              (fun c ->
                match F.view_constraint c with
                | Constraint { var; payload = Bool; value } ->
                    if value then Syn.bool var else Syn.not (Syn.bool var)
                | Constraint
                    { var; payload = Theory (Right (Eq.Const s)); value } ->
                    (* Right is String *)
                    let eq = StrSyn.(var = s) in
                    if value then eq else Syn.not eq
                | Constraint
                    {
                      var;
                      payload = Theory (Left (Leq.Bound { limit; inclusive }));
                      value;
                    } ->
                    (* Left is Version *)
                    let atom =
                      VerSyn.(if inclusive then var <= limit else var < limit)
                    in
                    if value then atom else Syn.not atom)
              constraints
            |> F.and_list
          in
          F.is_tautology (F.implies model_expr expr)
      | None -> F.equivalent expr F.false_)

(* Fuzzing: Naive Representation vs BDD *)

type naive_atom =
  | NBool of bool Theo.Var.t
  | NStrEq of Eq.kind Theo.Var.t * string
  | NStrNe of Eq.kind Theo.Var.t * string
  | NVerLt of Leq.kind Theo.Var.t * Version.t
  | NVerLe of Leq.kind Theo.Var.t * Version.t
  | NVerGt of Leq.kind Theo.Var.t * Version.t
  | NVerGe of Leq.kind Theo.Var.t * Version.t

type naive_expr =
  | NAtom of naive_atom
  | NNot of naive_expr
  | NAnd of naive_expr * naive_expr
  | NOr of naive_expr * naive_expr
  | NImplies of naive_expr * naive_expr
  | NIff of naive_expr * naive_expr
  | NXor of naive_expr * naive_expr
  | NTrue
  | NFalse

let rec naive_to_bdd = function
  | NAtom (NBool v) -> Syn.bool v
  | NAtom (NStrEq (v, s)) -> StrSyn.(v = s)
  | NAtom (NStrNe (v, s)) -> StrSyn.(v <> s)
  | NAtom (NVerLt (v, ver)) -> VerSyn.(v < ver)
  | NAtom (NVerLe (v, ver)) -> VerSyn.(v <= ver)
  | NAtom (NVerGt (v, ver)) -> VerSyn.(v > ver)
  | NAtom (NVerGe (v, ver)) -> VerSyn.(v >= ver)
  | NNot e -> F.not (naive_to_bdd e)
  | NAnd (e1, e2) -> F.and_ (naive_to_bdd e1) (naive_to_bdd e2)
  | NOr (e1, e2) -> F.or_ (naive_to_bdd e1) (naive_to_bdd e2)
  | NImplies (e1, e2) -> F.implies (naive_to_bdd e1) (naive_to_bdd e2)
  | NIff (e1, e2) -> F.iff (naive_to_bdd e1) (naive_to_bdd e2)
  | NXor (e1, e2) -> F.xor (naive_to_bdd e1) (naive_to_bdd e2)
  | NTrue -> F.true_
  | NFalse -> F.false_

(* World Generation *)
type world = {
  bools : (bool Theo.Var.t, bool) Hashtbl.t;
  strs : (Eq.kind Theo.Var.t, string) Hashtbl.t;
  vers : (Leq.kind Theo.Var.t, Version.t) Hashtbl.t;
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

let compare_raw_version ({ Version.major; minor; patch } : Version.t)
    ({ Version.major = major'; minor = minor'; patch = patch' } : Version.t) =
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
      ~default:{ Version.major = 0; minor = 0; patch = 0 }
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
  | NImplies (e1, e2) -> Stdlib.not (eval_naive e1 w) || eval_naive e2 w
  | NIff (e1, e2) -> eval_naive e1 w = eval_naive e2 w
  | NXor (e1, e2) -> eval_naive e1 w <> eval_naive e2 w
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
        | Some b -> constraints := c_bool v b @ !constraints
        | None -> ())
      bool_var_pool
  in
  let add_str_constraints () =
    Array.iter
      (fun v ->
        match Hashtbl.find_opt w.strs v with
        | Some s -> constraints := c_str_eq v s @ !constraints
        | None -> ())
      str_var_pool
  in
  let add_ver_constraints () =
    Array.iter
      (fun v ->
        match Hashtbl.find_opt w.vers v with
        | Some ver ->
            (* For version, in a world, a var has a specific version value.
               But constructing a "Version=v" constraint is not directly supported by Leq theory atoms
               (which are <= or <).
               However, v=ver is equivalent to v<=ver && v>=ver.
               So we add both. *)
            constraints := c_ver_ge v ver @ c_ver_le v ver @ !constraints
        | None -> ())
      ver_var_pool
  in
  add_bool_constraints ();
  add_str_constraints ();
  add_ver_constraints ();
  !constraints

let gen_bool_var =
  Gen.map
    (fun i -> bool_var_pool.(i))
    (Gen.int_bound (Array.length bool_var_pool - 1))

let gen_str_var =
  Gen.map
    (fun i -> str_var_pool.(i))
    (Gen.int_bound (Array.length str_var_pool - 1))

let gen_ver_var =
  Gen.map
    (fun i -> ver_var_pool.(i))
    (Gen.int_bound (Array.length ver_var_pool - 1))

let gen_naive_atom =
  Gen.oneof
    [
      Gen.map (fun v -> NBool v) gen_bool_var;
      Gen.map2 (fun v s -> NStrEq (v, s)) gen_str_var gen_str_val;
      Gen.map2 (fun v s -> NStrNe (v, s)) gen_str_var gen_str_val;
      Gen.map2 (fun v ver -> NVerLt (v, ver)) gen_ver_var gen_ver_val;
      Gen.map2 (fun v ver -> NVerLe (v, ver)) gen_ver_var gen_ver_val;
      Gen.map2 (fun v ver -> NVerGt (v, ver)) gen_ver_var gen_ver_val;
      Gen.map2 (fun v ver -> NVerGe (v, ver)) gen_ver_var gen_ver_val;
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
        Gen.map2
          (fun e1 e2 -> NImplies (e1, e2))
          (gen_naive_expr (depth / 2))
          (gen_naive_expr (depth / 2));
        Gen.map2
          (fun e1 e2 -> NIff (e1, e2))
          (gen_naive_expr (depth / 2))
          (gen_naive_expr (depth / 2));
        Gen.map2
          (fun e1 e2 -> NXor (e1, e2))
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
      let restricted_bdd = F.restrict bdd constraints in
      if expected_bool then F.equivalent restricted_bdd F.true_
      else F.equivalent restricted_bdd F.false_)

let shuffle_list l state =
  let a = Array.of_list l in
  let len = Array.length a in
  for i = len - 1 downto 1 do
    let j = Random.State.int state (i + 1) in
    let t = a.(i) in
    a.(i) <- a.(j);
    a.(j) <- t
  done;
  Array.to_list a

let prop_restrict_consistent =
  Test.make ~name:"Restrict Partial: eval (restrict f C) w = eval f w"
    ~count:2000
    (triple (make (gen_naive_expr 4)) (make gen_world) small_nat)
    (fun (naive, world, seed_int) ->
      let bdd = naive_to_bdd naive in
      let expected_bool = eval_naive naive world in
      let constraints = world_to_constraints world in
      let state = Random.State.make [| seed_int |] in
      let shuffled = shuffle_list constraints state in
      let subset =
        if List.length shuffled = 0 then []
        else if seed_int mod 2 = 0 then
          (* Biased towards small lists *)
          let k = min (List.length shuffled) (Random.State.int state 6) in
          List.init k (fun i -> List.nth shuffled i)
        else
          (* Random subset *)
          let subset_size = Random.State.int state (List.length shuffled + 1) in
          List.init subset_size (fun i -> List.nth shuffled i)
      in

      let restricted_bdd = F.restrict bdd subset in
      (* Evaluate restricted BDD in the full world *)
      let fully_evaluated = F.restrict restricted_bdd constraints in
      if expected_bool then F.equivalent fully_evaluated F.true_
      else F.equivalent fully_evaluated F.false_)

let bdd_arbitrary = make (Gen.map naive_to_bdd (gen_naive_expr 4))

let prop_ite_constant_consistent =
  Test.make ~name:"ite_constant consistent with ite" ~count:2000
    (triple bdd_arbitrary bdd_arbitrary bdd_arbitrary) (fun (f, g, h) ->
      let res_ite = F.ite f g h in
      let res_const = F.ite_constant f g h in
      let ite_is_true = F.equivalent res_ite F.true_ in
      let ite_is_false = F.equivalent res_ite F.false_ in
      match res_const with
      | F.Constant true -> ite_is_true
      | F.Constant false -> ite_is_false
      | F.NonConstant -> Stdlib.not ite_is_true && Stdlib.not ite_is_false)

let prop_quantifier_duality =
  Test.make ~name:"Quantifier Duality: exists x. f <=> not (forall x. not f)"
    ~count:2000 (pair idx_arb bdd_arbitrary) (fun (idx, f) ->
      let v = bool_var_pool.(idx) in
      let lhs = F.exists v f in
      let rhs = F.not (F.forall v (F.not f)) in
      F.equivalent lhs rhs)

let prop_quantifier_distributivity_exists_or =
  Test.make
    ~name:
      "Quantifier Distributivity: exists x. (f || g) <=> (exists x. f) || \
       (exists x. g)" ~count:2000 (triple idx_arb bdd_arbitrary bdd_arbitrary)
    (fun (idx, f, g) ->
      let v = bool_var_pool.(idx) in
      let lhs = F.exists v (F.or_ f g) in
      let rhs = F.or_ (F.exists v f) (F.exists v g) in
      F.equivalent lhs rhs)

let prop_quantifier_distributivity_forall_and =
  Test.make
    ~name:
      "Quantifier Distributivity: forall x. (f && g) <=> (forall x. f) && \
       (forall x. g)" ~count:2000 (triple idx_arb bdd_arbitrary bdd_arbitrary)
    (fun (idx, f, g) ->
      let v = bool_var_pool.(idx) in
      let lhs = F.forall v (F.and_ f g) in
      let rhs = F.and_ (F.forall v f) (F.forall v g) in
      F.equivalent lhs rhs)

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
      prop_restrict_consistent;
    ]
