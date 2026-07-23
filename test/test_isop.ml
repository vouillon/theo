open Theories
module F = Formula
open QCheck
open Formula.Syntax

let assert_bool b msg = if Stdlib.not b then failwith ("FAIL: " ^ msg)

(* --- Structural checks on a cover --- *)

(* A cube is redundant if it can be dropped while staying equivalent to the
   original expression. *)
let cube_is_redundant expr cubes cube =
  let others = List.filter (fun c -> c != cube) cubes in
  F.equivalent (F.sop_to_bdd others) expr

(* A literal in a cube is redundant if removing it keeps the (now larger) cube
   still implying [expr] -- i.e. the literal was not needed to stay inside the
   on-set. *)
let literal_is_redundant expr cube lit =
  let shrunk = List.filter (fun l -> l != lit) cube in
  F.logical_implies (F.of_cube shrunk) expr

(* Guarantees that hold for ANY expression (Boolean or theory): the cover
   reproduces the function, and every cube implies it. *)
let check_cover name expr =
  let cubes = F.irredundant_sop expr in
  assert_bool
    (F.equivalent (F.sop_to_bdd cubes) expr)
    (Printf.sprintf "%s: cover equivalent to expr" name);
  List.iter
    (fun cube ->
      assert_bool
        (F.logical_implies (F.of_cube cube) expr)
        (Printf.sprintf "%s: cube implies expr" name))
    cubes

(* Stronger guarantee that holds when atoms are independent (i.e. pure Boolean
   expressions): the cover is irredundant and its cubes are prime. *)
let check_irredundant name expr =
  check_cover name expr;
  let cubes = F.irredundant_sop expr in
  List.iter
    (fun cube ->
      assert_bool
        (Stdlib.not (cube_is_redundant expr cubes cube))
        (Printf.sprintf "%s: no redundant cube" name))
    cubes;
  List.iter
    (fun cube ->
      List.iter
        (fun lit ->
          assert_bool
            (Stdlib.not (literal_is_redundant expr cube lit))
            (Printf.sprintf "%s: no redundant literal (prime cube)" name))
        cube)
    cubes

let total_literals cubes =
  List.fold_left (fun acc cube -> acc + List.length cube) 0 cubes

(* --- Hand-written Boolean cases --- *)

let test_basic () =
  Printf.printf "Test ISOP basic cases...\n";
  let a = bool (Theo.Var.fresh ()) in
  let b = bool (Theo.Var.fresh ()) in
  let c = bool (Theo.Var.fresh ()) in

  assert_bool (F.irredundant_sop F.false_ = []) "false -> empty cover";
  assert_bool (F.irredundant_sop F.true_ = [ [] ]) "true -> one empty cube";

  check_irredundant "a" a;
  check_irredundant "!a" (not a);
  check_irredundant "a&b" (a && b);
  check_irredundant "a|b" (a || b);
  check_irredundant "a^b" (a <+> b);

  (* a&b | !a&c : the consensus term b&c is redundant and must be absent. *)
  check_irredundant "ab|!ac" ((a && b) || ((not a) && c));

  (* Majority: all three cubes are prime and required (3-cube irredundant). *)
  let maj = (a && b) || (b && c) || (a && c) in
  check_irredundant "ab|bc|ac" maj;
  assert_bool (List.length (F.irredundant_sop maj) = 3) "majority has 3 cubes";

  Printf.printf "OK\n"

(* --- Hand-written theory cases ---

   [irredundant_sop] is irredundant modulo theory, so the full [check_irredundant]
   holds even for theory expressions. *)

let test_theory () =
  Printf.printf "Test ISOP theory cases...\n";
  let open VersionSyntax in
  let v = Theo.Var.fresh () in
  let s = Theo.Var.fresh () in
  let v1 = { Version.major = 1; minor = 0; patch = 0 } in
  let v2 = { Version.major = 2; minor = 0; patch = 0 } in

  check_irredundant "v<1.0.0" (v < v1);
  check_irredundant "v>=1 & v<2" (v >= v1 && v < v2);
  check_irredundant "s=a | s=b"
    (StringSyntax.(s = "a") || StringSyntax.(s = "b"));
  check_irredundant "v<1 | s=prod" (v < v1 || StringSyntax.(s = "prod"));
  Printf.printf "OK\n"

(* --- Exploiting impossible theory combinations --- *)

let test_theory_dont_care () =
  Printf.printf "Test ISOP theory don't-cares...\n";
  let open VersionSyntax in
  let v = Theo.Var.fresh () in
  let b1 = { Version.major = 1; minor = 0; patch = 0 } in
  let b2 = { Version.major = 2; minor = 0; patch = 0 } in
  let b3 = { Version.major = 3; minor = 0; patch = 0 } in

  (* The minimal example from the caveat:
       expr = ¬(v<1) ∧ ((v<2) ∨ ¬(v<3))
     The raw Minato-Morreale cover would emit the cube  ¬(v<1) ∧ ¬(v<3),  whose
     ¬(v<1) is redundant modulo theory ([¬(v<3)] entails it). [irredundant_sop]
     exploits that impossible combination and drops it, giving the single-literal
     cube [¬(v<3)]. *)
  let expr = F.and_ (F.not (v < b1)) (F.or_ (v < b2) (F.not (v < b3))) in
  let cubes = F.irredundant_sop expr in
  check_irredundant "example" expr;
  (* Two cubes, three literals total: [¬(v<1) ∧ (v<2)] and [¬(v<3)]. *)
  assert_bool (Int.equal (List.length cubes) 2) "example has 2 cubes";
  assert_bool
    (Int.equal (total_literals cubes) 3)
    "example has 3 literals total";
  assert_bool
    (List.exists
       (fun cube ->
         Stdlib.( && )
           (Int.equal (List.length cube) 1)
           (F.equivalent (F.of_cube cube) (F.not (v < b3))))
       cubes)
    "example contains the single-literal cube ¬(v<3)";

  check_irredundant "v<1 | v>=2 & v<3" (v < b1 || (v >= b2 && v < b3));

  (* Independent single theory atoms (different variables): no variable carries
     two related atoms, so the post-processing is skipped -- the result must
     still be a valid irredundant cover. *)
  let s = Theo.Var.fresh () in
  check_irredundant "v<1 | s=x (skip path)" (v < b1 || StringSyntax.(s = "x"));
  Printf.printf "OK\n"

let () =
  test_basic ();
  test_theory ();
  test_theory_dont_care ()

(* --- Property-based tests --- *)

let bool_var_pool = Array.init 6 (fun _ -> Theo.Var.fresh ())
let str_var_pool = Array.init 3 (fun _ -> Theo.Var.fresh ())
let ver_var_pool = Array.init 3 (fun _ -> Theo.Var.fresh ())
let gen_str_val = Gen.oneof_list [ "a"; "b"; "c" ]

let gen_ver_val =
  Gen.(
    map
      (fun (major, minor, patch) -> { Version.major; minor; patch })
      (triple (int_bound 3) (int_bound 3) (int_bound 3)))

module Syn = Formula.Syntax

let gen_bool_atom =
  Gen.map (fun i -> Syn.bool bool_var_pool.(i)) (Gen.int_bound 5)

let gen_theory_atom =
  Gen.oneof
    [
      gen_bool_atom;
      Gen.map2
        (fun i s -> StringSyntax.(str_var_pool.(i) = s))
        (Gen.int_bound 2) gen_str_val;
      Gen.map2
        (fun i v -> VersionSyntax.(ver_var_pool.(i) < v))
        (Gen.int_bound 2) gen_ver_val;
      Gen.map2
        (fun i v -> VersionSyntax.(ver_var_pool.(i) <= v))
        (Gen.int_bound 2) gen_ver_val;
    ]

let gen_expr atom =
  let rec go depth =
    if depth = 0 then atom
    else
      Gen.oneof
        [
          atom;
          Gen.map (fun e -> Syn.not e) (go (depth - 1));
          Gen.map2 (fun a b -> Syn.( && ) a b) (go (depth / 2)) (go (depth / 2));
          Gen.map2 (fun a b -> Syn.( || ) a b) (go (depth / 2)) (go (depth / 2));
        ]
  in
  go 4

let theory_arbitrary = make (gen_expr gen_theory_atom) ~print:F.to_string

(* All properties hold over arbitrary theory expressions: the cover is
   equivalent, every cube implies the input, and -- because the redundancy
   checks are theory-aware -- the cover is irredundant and its cubes prime
   modulo theory. *)
let prop_equivalent =
  Test.make ~name:"ISOP cover is equivalent to the input" ~count:5000
    theory_arbitrary (fun e ->
      F.equivalent (F.sop_to_bdd (F.irredundant_sop e)) e)

let prop_cubes_imply =
  Test.make ~name:"every ISOP cube implies the input" ~count:5000
    theory_arbitrary (fun e ->
      List.for_all
        (fun cube -> F.logical_implies (F.of_cube cube) e)
        (F.irredundant_sop e))

let prop_no_redundant_cube =
  Test.make ~name:"no ISOP cube is redundant (modulo theory)" ~count:3000
    theory_arbitrary (fun e ->
      let cubes = F.irredundant_sop e in
      List.for_all
        (fun cube -> Stdlib.not (cube_is_redundant e cubes cube))
        cubes)

let prop_prime_cubes =
  Test.make ~name:"no ISOP literal is redundant / prime cubes (modulo theory)"
    ~count:3000 theory_arbitrary (fun e ->
      List.for_all
        (fun cube ->
          List.for_all
            (fun lit -> Stdlib.not (literal_is_redundant e cube lit))
            cube)
        (F.irredundant_sop e))

let () =
  QCheck_runner.run_tests_main
    [
      prop_equivalent;
      prop_cubes_imply;
      prop_no_redundant_cube;
      prop_prime_cubes;
    ]
