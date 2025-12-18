open Theories

(* Formula is the BDD module from Theories *)
module F = Formula

(* Helper for printing/debugging *)
(* let print_bdd = F.print_dot stdout *)

(* Constraint construction helpers *)
let c_bool v b = F.Constraint.bool v b

(* String constraints *)
(* String theory is the Right component of the combined theory *)
(* Eq theory uses 'Eq category *)
let c_str_eq v s = F.Constraint.atom v Eq.category (Right (Eq.Const s))
let c_str_ne v s = F.Constraint.not (c_str_eq v s)

(* Version constraints *)
(* Version theory is the Left component *)
(* Leq theory uses 'Leq category and Bound descriptor *)
let c_ver_lt v ver =
  F.Constraint.atom v Leq.category
    (Left (Leq.Bound { limit = ver; inclusive = false }))

let c_ver_le v ver =
  F.Constraint.atom v Leq.category
    (Left (Leq.Bound { limit = ver; inclusive = true }))

let c_ver_ge v ver = F.Constraint.not (c_ver_lt v ver)
let c_ver_gt v ver = F.Constraint.not (c_ver_le v ver)

(* Test utility operations *)
let test_utility () =
  Printf.printf "Testing utility operations...\n";
  let open Formula.Syntax in
  (* Create some variables *)
  let b1 = Theo.Var.fresh () in
  let b2 = Theo.Var.fresh () in

  (* Create some expressions *)
  let e1 = bool b1 in
  let e2 = bool b2 in

  let and_expr = e1 && e2 in

  (* Test implies *)
  assert (F.is_tautology (F.true_ ==> F.true_));
  assert (F.is_tautology (F.false_ ==> F.true_));
  assert (F.is_tautology (F.true_ ==> F.false_) = false);
  assert (F.is_tautology (F.false_ ==> F.false_));
  assert (F.is_tautology (e1 ==> (e1 || e2)));

  (* Test implies - only works for expressions that reduce to constants *)
  (* implies checks if (not a || b) is literally true_, not a tautology *)
  Printf.printf "  implies: OK\n";

  (* Test equivalent *)
  assert (F.equivalent e1 e1 = true);
  assert (F.equivalent F.true_ F.true_ = true);
  assert (F.equivalent F.false_ F.false_ = true);

  (* Test equivalent with complex expressions *)
  let e3 = e1 && e2 in
  let e4 = e1 && e2 in
  assert (F.equivalent e3 e4 = true);
  Printf.printf "  equivalent: OK\n";

  (* Test size *)
  assert (F.size F.true_ = 1);
  assert (F.size F.false_ = 1);
  assert (F.size e1 > 0);
  (* Size comparisons depend on internal BDD optimizations *)
  Printf.printf "  size: OK (true=%d, false=%d, e1=%d, and=%d)\n"
    (F.size F.true_) (F.size F.false_) (F.size e1) (F.size and_expr);

  ()

(* Test batch operations *)
let test_batch () =
  Printf.printf "Testing batch operations...\n";
  let open Formula.Syntax in
  let b1 = Theo.Var.fresh () in
  let b2 = Theo.Var.fresh () in
  let b3 = Theo.Var.fresh () in

  let e1 = bool b1 in
  let e2 = bool b2 in
  let e3 = bool b3 in

  (* Test and_list *)
  assert (F.is_tautology (F.and_list []) = true);
  assert (F.equivalent (F.and_list [ e1; e2; e3 ]) ((e1 && e2) && e3));
  assert (F.is_tautology (F.and_list [ F.true_; F.true_ ]) = true);
  assert (F.is_tautology (F.and_list [ F.true_; F.false_ ]) = false);
  assert (F.is_tautology (F.and_list [ F.true_; F.true_; F.true_ ]) = true);
  Printf.printf "  and_list: OK\n";

  (* Test or_list *)
  assert (F.is_tautology (F.or_list []) = false);
  assert (F.equivalent (F.or_list [ e1; e2; e3 ]) ((e1 || e2) || e3));
  assert (F.is_tautology (F.or_list [ F.false_; F.false_ ]) = false);
  assert (F.is_tautology (F.or_list [ F.false_; F.true_ ]) = true);
  assert (F.is_tautology (F.or_list [ F.false_; F.false_; F.false_ ]) = false);
  Printf.printf "  or_list: OK\n";

  ()

(* Test debugging operations *)
let test_debug () =
  Printf.printf "Testing debugging operations...\n";
  let open Formula.Syntax in
  let b1 = Theo.Var.fresh () in
  let s1 = Theo.Var.fresh () in

  let e1 = bool b1 in
  let e2 = StringSyntax.(s1 = "hello") in

  (* Test to_string *)
  let str1 = F.to_string F.true_ in
  assert (String.length str1 > 0);
  Printf.printf "  to_string(true_) = %s\n" str1;

  let str2 = F.to_string e1 in
  assert (String.length str2 > 0);
  Printf.printf "  to_string(atom) = \n%s\n" str2;

  let str3 = F.to_string (e1 && e2) in
  assert (String.length str3 > 0);
  Printf.printf "  to_string(and) = \n%s\n" str3;

  ()

(* Test logical operations edge cases *)
let test_logical_operations () =
  Printf.printf "Testing logical operations...\n";
  let open Formula.Syntax in
  let b1 = Theo.Var.fresh () in
  let b2 = Theo.Var.fresh () in
  let b3 = Theo.Var.fresh () in
  let e1 = bool b1 in
  let e2 = bool b2 in
  let e3 = bool b3 in

  (* Test AND with constants *)
  assert (F.is_tautology (F.true_ && F.true_) = true);
  assert (F.is_tautology (F.true_ && F.false_) = false);
  assert (F.is_tautology (F.false_ && F.true_) = false);
  assert (F.is_tautology (F.false_ && F.false_) = false);
  Printf.printf "  AND with constants: OK\n";

  (* Test OR with constants *)
  assert (F.is_tautology (F.true_ || F.true_) = true);
  assert (F.is_tautology (F.true_ || F.false_) = true);
  assert (F.is_tautology (F.false_ || F.true_) = true);
  assert (F.is_tautology (F.false_ || F.false_) = false);
  Printf.printf "  OR with constants: OK\n";

  (* Test NOT *)
  assert (F.equivalent (not F.true_) F.false_);
  assert (F.equivalent (not F.false_) F.true_);
  assert (F.equivalent (not (not e1)) e1);
  Printf.printf "  NOT: OK\n";

  (* Test De Morgan's laws *)
  let not_and = not (e1 && e2) in
  let or_not = (not e1) || not e2 in
  assert (F.equivalent not_and or_not);

  let not_or = not (e1 || e2) in
  let and_not = (not e1) && not e2 in
  assert (F.equivalent not_or and_not);
  Printf.printf "  De Morgan's laws: OK\n";

  (* Test associativity *)
  let assoc1 = (e1 && e2) && e3 in
  let assoc2 = e1 && e2 && e3 in
  assert (F.equivalent assoc1 assoc2);
  Printf.printf "  Associativity: OK\n";

  ()

(* Test theory reasoning *)
let test_theory_reasoning () =
  Printf.printf "Testing theory reasoning...\n";
  let open Formula.Syntax in
  (* Test string equality *)
  let s1 = Theo.Var.fresh () in
  let s2 = Theo.Var.fresh () in

  let eq1 = StringSyntax.(s1 = "foo") in
  let eq2 = StringSyntax.(s1 = "bar") in
  let eq3 = StringSyntax.(s2 = "foo") in

  (* Same variable, different values - should be mutually exclusive *)
  let conflict = eq1 && eq2 in
  assert (F.is_tautology conflict = false);
  assert (F.equivalent conflict F.false_);
  Printf.printf "  String conflict detection: OK\n";

  (* Different variables can have same value *)
  let both = eq1 && eq3 in
  assert (F.is_tautology both = false);
  assert (F.is_satisfiable both = true);
  Printf.printf "  String independence: OK\n";

  (* Test version comparisons *)
  let v1 = Theo.Var.fresh () in
  let lt_2 = VersionSyntax.(v1 < { major = 2; minor = 0; patch = 0 }) in
  let lt_3 = VersionSyntax.(v1 < { major = 3; minor = 0; patch = 0 }) in

  (* If v < 2, can v < 3? Yes. *)
  let both_lt = lt_2 && lt_3 in
  assert (F.is_tautology both_lt = false);
  assert (F.is_satisfiable both_lt = true);
  Printf.printf "  Version reasoning: OK\n";

  ()

(* Test mixed theory atoms *)
let test_mixed_theory () =
  Printf.printf "Testing mixed theory atoms...\n";
  let open Formula.Syntax in
  let b = Theo.Var.fresh () in
  let s = Theo.Var.fresh () in
  let v = Theo.Var.fresh () in

  let bool_expr = bool b in
  let str_expr = StringSyntax.(s = "test") in
  let ver_expr = VersionSyntax.(v < { major = 1; minor = 0; patch = 0 }) in

  (* Combine all three types *)
  let combined = F.and_list [ bool_expr; str_expr; ver_expr ] in
  assert (F.is_tautology combined = false);
  assert (F.is_satisfiable combined);
  Printf.printf "  Mixed theory: OK\n";

  (* Test size with mixed atoms *)
  let s1 = F.size combined in
  assert (s1 > 0);
  Printf.printf "  Mixed theory size: %d\n" s1;

  ()

(* Test edge cases *)
let test_edge_cases () =
  Printf.printf "Testing edge cases...\n";
  let open Formula.Syntax in
  (* Empty and_list should be true *)
  assert (F.is_tautology (F.and_list []) = true);

  (* Empty or_list should be false *)
  assert (F.is_tautology (F.or_list []) = false);

  (* Single element lists *)
  let b = Theo.Var.fresh () in
  let e = bool b in
  assert (F.equivalent (F.and_list [ e ]) e);
  assert (F.equivalent (F.or_list [ e ]) e);
  Printf.printf "  Empty/single lists: OK\n";

  (* Implies reflexivity *)
  assert (F.is_tautology (F.implies e e));
  assert (F.is_tautology (F.implies F.true_ F.true_));
  assert (F.is_tautology (F.implies F.false_ F.false_));
  Printf.printf "  Implies reflexivity: OK\n";

  (* Size of constants *)
  assert (F.size F.true_ >= 1);
  assert (F.size F.false_ >= 1);
  Printf.printf "  Constant sizes: OK\n";

  ()

(* Test theory simplification (regression test for implication logic) *)
let test_theory_simplification () =
  let open Formula.Syntax in
  Printf.printf "Testing theory simplification...\n";

  let v = Theo.Var.fresh () in

  (* Case: x > 1 && x > 2 should be just x > 2 *)
  (* x > 1 is not (x <= 1) *)
  (* x > 2 is not (x <= 2) *)
  let leq1 = VersionSyntax.(v <= { major = 1; minor = 0; patch = 0 }) in
  let leq2 = VersionSyntax.(v <= { major = 2; minor = 0; patch = 0 }) in

  let gt1 = not leq1 in
  let gt2 = not leq2 in

  let conj_gt = gt1 && gt2 in

  assert (F.equivalent conj_gt gt2);
  Printf.printf "  (x > 1) && (x > 2) -> (x > 2): OK\n";

  ()

let test_more_theory_simplification () =
  Printf.printf "Testing more theory simplification...\n";
  let open Formula.Syntax in
  let a = Theo.Var.fresh () in
  let b = Theo.Var.fresh () in
  let c = Theo.Var.fresh () in

  (* IsTrue simplification *)
  let atom_c = bool c in
  (* atom_c || true is just true, but let's test that atom_c structure is simple *)
  let sc = F.size atom_c in
  Printf.printf "  IsTrue size: %d\n" sc;
  assert (sc > 0);
  Printf.printf "  IsTrue size: OK\n";

  (* String contradictions *)
  (* x="A" && x="B" -> False *)
  let is_a = StringSyntax.(b = "A") in
  let is_b = StringSyntax.(b = "B") in
  let both = is_a && is_b in
  assert (F.equivalent both F.false_);
  Printf.printf "  String contradiction (x='A' && x='B' -> False): OK\n";

  (* String implication *)
  (* x="A" -> x!="B" *)
  (* is_a && not is_b should be equal to is_a *)
  let not_b = not is_b in
  assert (F.equivalent (is_a && not_b) is_a);
  Printf.printf "  String implication (x='A' -> x!='B'): OK\n";

  (* Version transitivity *)
  (* x < 1 && x < 2 -> x < 1 *)
  let lt1 = VersionSyntax.(a < { major = 1; minor = 0; patch = 0 }) in
  let lt2 = VersionSyntax.(a < { major = 2; minor = 0; patch = 0 }) in
  assert (F.equivalent (lt1 && lt2) lt1);
  Printf.printf "  Version transitivity (x < 1 && x < 2 -> x < 1): OK\n";

  (* Strictness mixing *)
  (* x < 1 implies x <= 1 *)
  let leq1 = VersionSyntax.(a <= { major = 1; minor = 0; patch = 0 }) in
  assert (F.equivalent (lt1 && leq1) lt1);
  Printf.printf "  Strictness (x < 1 && x <= 1 -> x < 1): OK\n";

  (* Contradiction *)
  (* x < 1 && x > 2 -> False *)
  let gt2 = not VersionSyntax.(a <= { major = 2; minor = 0; patch = 0 }) in
  assert (F.equivalent (lt1 && gt2) F.false_);
  Printf.printf "  Contradiction (x < 1 && x > 2 -> False): OK\n";

  (* Valid Range *)
  (* x > 1 && x < 2 -> preserved *)
  let gt1 = not leq1 in
  (* x > 1 implies nothing about x < 2, and x < 2 implies nothing about x > 1 *)
  (* So this should not simplify to just gt1 or lt2 *)
  assert (F.equivalent (gt1 && lt2) gt1 = false);
  assert (F.equivalent (gt1 && lt2) lt2 = false);
  Printf.printf "  Valid Range (x > 1 && x < 2 -> preserved): OK\n";

  ()

let test_hash_consing () =
  Printf.printf "Testing hash-consing...\n";
  let open Formula.Syntax in
  let b = Theo.Var.fresh () in
  let e1 = bool b in
  let e2 = bool b in
  assert (e1 == e2);
  let c1 = e1 && e2 in
  let c2 = e1 && e2 in
  assert (c1 == c2);
  Printf.printf "  Physical equality: OK\n";
  ()

let test_variable_ordering () =
  Printf.printf "Testing variable ordering impact...\n";
  let open Formula.Syntax in
  (* Case 1: Interleaved *)
  let a1 = Theo.Var.fresh () in
  let b1 = Theo.Var.fresh () in
  let a2 = Theo.Var.fresh () in
  let b2 = Theo.Var.fresh () in
  let expr1 = (bool a1 && bool b1) || (bool a2 && bool b2) in

  (* Case 2: Grouped (simulated by just checking size, 
    but for true variable ordering tests we'd need to control IDs.
    Here we just check that size is consistent for now, or 
    demonstrate that different constructions might yield different sizes 
    if we could change ordering. Since we can't change ordering of existing vars,
    we just verify size consistency.) *)
  assert (F.size expr1 > 0);
  Printf.printf "  Variable ordering check: OK (Expr size: %d)\n" (F.size expr1);
  ()

let test_dot_output () =
  Printf.printf "Testing DOT output...\n";
  let b = Theo.Var.fresh () in
  let e = F.Syntax.bool b in
  (* Just ensure it doesn't crash *)
  F.print_dot stdout e;
  F.print_dot stdout F.false_;
  F.print_dot stdout F.true_;
  Printf.printf "  DOT output: OK\n";
  ()

let test_sat () =
  Printf.printf "Testing SAT...\n";
  let open F.Syntax in
  (* Case 1: Tautology *)
  assert (F.sat F.true_ = Some []);

  (* Case 2: Contradiction *)
  assert (F.sat F.false_ = None);

  (* Case 3: Simple boolean *)
  let b = Theo.Var.fresh () in
  let e = bool b in
  (match F.sat e with
  | Some [ c ] -> (
      match F.view_constraint c with
      | Constraint { var; payload = Bool; value = true } -> assert (var = b)
      | _ -> assert false)
  | _ -> assert false);

  (* Case 4: Unsatisfiable combination *)
  let s = Theo.Var.fresh () in
  let e_s = StringSyntax.(s = "a" && s = "b") in
  assert (F.sat e_s = None);

  (* Case 5: Satisfiable combination *)
  let b2 = Theo.Var.fresh () in
  let e_mix = bool b || bool b2 in
  (match F.sat e_mix with
  | Some (_ :: _) -> Printf.printf "  SAT found solution for OR\n"
  | _ -> assert false);

  Printf.printf "  SAT: OK\n";
  ()

(* Test convenience functions *)
let test_convenience () =
  Printf.printf "Testing convenience functions...\n";
  let open Formula.Syntax in
  (* is_satisfiable *)
  assert (F.is_satisfiable F.true_ = true);
  assert (F.is_satisfiable F.false_ = false);
  let b = Theo.Var.fresh () in
  assert (F.is_satisfiable (bool b) = true);
  Printf.printf "  is_satisfiable: OK\n";

  (* is_not_equal for strings *)
  let s = Theo.Var.fresh () in
  let eq_a = StringSyntax.(s = "a") in
  let ne_a = StringSyntax.(s <> "a") in
  assert (F.equivalent ne_a (not eq_a));
  Printf.printf "  is_not_equal: OK\n";

  (* Version comparisons: is_eq, is_gt, is_ge *)
  let v = Theo.Var.fresh () in
  let lt = VersionSyntax.(v < { major = 2; minor = 0; patch = 0 }) in
  let le = VersionSyntax.(v <= { major = 2; minor = 0; patch = 0 }) in
  let gt = VersionSyntax.(v > { major = 2; minor = 0; patch = 0 }) in
  let ge = VersionSyntax.(v >= { major = 2; minor = 0; patch = 0 }) in
  let eq = VersionSyntax.(v = { major = 2; minor = 0; patch = 0 }) in

  (* gt = not le *)
  assert (F.equivalent gt (not le));
  (* ge = not lt *)
  assert (F.equivalent ge (not lt));
  (* eq = le && ge *)
  assert (F.equivalent eq (le && ge));
  (* lt || eq || gt should be a tautology *)
  assert (F.is_tautology (F.or_list [ lt; eq; gt ]));
  Printf.printf "  is_eq, is_gt, is_ge: OK\n";

  (* xor truth table *)
  assert (F.is_tautology (F.true_ <+> F.false_) = true);
  assert (F.is_tautology (F.false_ <+> F.true_) = true);
  assert (F.is_tautology (F.true_ <+> F.true_) = false);
  assert (F.is_tautology (F.false_ <+> F.false_) = false);
  (* xor is satisfiable (not a tautology, not a contradiction) *)
  let b1 = Theo.Var.fresh () in
  let b2 = Theo.Var.fresh () in
  let e1 = bool b1 in
  let e2 = bool b2 in
  let xor_expr = e1 <+> e2 in
  assert (F.is_satisfiable xor_expr);
  assert (Stdlib.not (F.is_tautology xor_expr));
  let manual_xor = (e1 && not e2) || ((not e1) && e2) in
  assert (xor_expr == manual_xor);
  Printf.printf "  xor: OK\n";

  (* iff truth table *)
  assert (F.is_tautology (F.true_ <=> F.true_) = true);
  assert (F.is_tautology (F.false_ <=> F.false_) = true);
  assert (F.is_tautology (F.true_ <=> F.false_) = false);
  assert (F.is_tautology (F.false_ <=> F.true_) = false);
  (* iff(a, a) should be tautology *)
  Printf.printf "  iff: OK\n";

  (* Syntax operators *)
  let open F.Syntax in
  assert (F.is_tautology (F.true_ ==> F.true_));
  assert (F.is_tautology (F.false_ ==> F.true_));
  assert (Stdlib.not (F.is_tautology (F.true_ ==> F.false_)));

  assert (F.is_tautology (e1 <=> e1));
  assert (F.is_tautology (e1 <+> e2 <=> F.xor e1 e2));
  assert (F.is_tautology (e1 ==> e2 <=> F.implies e1 e2));

  (* Syntax.{String, Version} operators *)
  let open StringSyntax in
  let s_expr = s = "a" || s <> "b" in
  assert (F.is_satisfiable s_expr);

  let open VersionSyntax in
  let v_expr =
    v >= { major = 1; minor = 0; patch = 0 }
    && v < { major = 2; minor = 0; patch = 0 }
  in
  assert (F.is_satisfiable v_expr);
  (* Check simple implication: v < (1,0,0) => v <= (1,0,0) *)
  Printf.printf "  Syntax operators: OK\n";

  Printf.printf "  Convenience functions: OK\n";
  ()

let test_restrict_ite () =
  Printf.printf "Testing restrict and ite...\n";
  let open Formula.Syntax in
  let b1 = Theo.Var.fresh () in
  let b2 = Theo.Var.fresh () in
  let b3 = Theo.Var.fresh () in
  let e1 = bool b1 in
  let e2 = bool b2 in
  let e3 = bool b3 in

  (* Test ite *)
  let ite_expr = F.ite e1 e2 e3 in
  (* if b1 then b2 else b3 *)
  (* Equivalent to (b1 && b2) || (not b1 && b3) *)
  let manual_ite = (e1 && e2) || ((not e1) && e3) in
  assert (F.equivalent ite_expr manual_ite);
  Printf.printf "  ite: OK\n";

  (* Test restrict *)
  let expr = manual_ite in

  (* Restrict b1=true -> should be b2 *)
  let r1 = F.restrict expr (c_bool b1 true) in
  assert (F.equivalent r1 e2);

  (* Restrict b1=false -> should be b3 *)
  let r2 = F.restrict expr (c_bool b1 false) in
  assert (F.equivalent r2 e3);

  (* Restrict b2=true -> should be (b1 || (not b1 && b3)) -> b1 || b3 *)
  let r3 = F.restrict expr (c_bool b2 true) in
  assert (F.equivalent r3 (e1 || e3));

  (* Restrict multiple *)
  let r4 = F.restrict expr (c_bool b1 true @ c_bool b2 false) in
  assert (F.is_tautology (r4 <=> F.false_));

  (* Restrict contradiction *)
  let r_contra =
    F.restrict expr (F.Constraint.and_ (c_bool b1 true) (c_bool b1 false))
  in
  assert (F.equivalent r_contra F.false_);
  Printf.printf "  restrict contradiction: OK\n";

  (* Test String restrictions *)
  let open StringSyntax in
  let s1 = Theo.Var.fresh () in
  let e_s = s1 = "a" in

  (* Restrict s1="a" -> True *)
  let r_s1 = F.restrict e_s (c_str_eq s1 "a") in
  assert (F.equivalent r_s1 F.true_);

  (* Restrict s1="b" -> False *)
  let r_s2 = F.restrict e_s (c_str_eq s1 "b") in
  assert (F.equivalent r_s2 F.false_);

  (* Restrict s1!="a" -> False *)
  let r_s3 = F.restrict e_s (c_str_ne s1 "a") in
  assert (F.equivalent r_s3 F.false_);
  Printf.printf "  restrict String: OK\n";

  (* Test Version restrictions *)
  let v = Theo.Var.fresh () in
  (* e_v: v < 2.0.0 *)
  let e_v = VersionSyntax.(v < { major = 2; minor = 0; patch = 0 }) in

  (* Restrict v < 1.0.0 -> implies v < 2.0.0 is true *)
  let r_v1 = F.restrict e_v (c_ver_lt v { major = 1; minor = 0; patch = 0 }) in
  assert (F.equivalent r_v1 F.true_);

  (* Restrict v > 3.0.0 -> implies v < 2.0.0 is false *)
  let r_v2 = F.restrict e_v (c_ver_gt v { major = 3; minor = 0; patch = 0 }) in
  assert (F.equivalent r_v2 F.false_);

  (* Restrict v > 2.0.0 -> implies v < 2.0.0 is false *)
  let r_v3 = F.restrict e_v (c_ver_gt v { major = 2; minor = 0; patch = 0 }) in
  assert (F.equivalent r_v3 F.false_);

  Printf.printf "  restrict Version: OK\n";

  (* Test Version Strictness Edge Cases *)
  (* Case 1: Strict lower bound implies Inclusive lower bound *)
  (* Restrict (v >= 1.0.0) given (v > 1.0.0) -> True *)
  let v_ge_1 = VersionSyntax.(v >= { major = 1; minor = 0; patch = 0 }) in
  let r_strict_impl_inc =
    F.restrict v_ge_1 (c_ver_gt v { major = 1; minor = 0; patch = 0 })
  in
  assert (F.equivalent r_strict_impl_inc F.true_);

  (* Case 2: Inclusive lower bound does NOT imply Strict lower bound *)
  (* Restrict (v > 1.0.0) given (v >= 1.0.0) -> NonConstant (v could be 1.0.0) *)
  (* Wait, restrict simplifies based on partial assignment. *)
  (* If constraints don't fully determine value, it returns simplified BDD. *)
  (* v >= 1.0.0 doesn't determine v > 1.0.0. *)
  (* But v > 1.0.0 AND v >= 1.0.0 is just v > 1.0.0. *)
  (* restrict f C computes f | C. *)
  (* If C is v >= 1.0.0, then is_gt v 1.0.0 remains is_gt v 1.0.0. *)
  let v_gt_1 = VersionSyntax.(v > { major = 1; minor = 0; patch = 0 }) in
  let r_inc_not_impl_strict =
    F.restrict v_gt_1 (c_ver_ge v { major = 1; minor = 0; patch = 0 })
  in
  (* Result should be exactly v_gt_1 because constraint didn't resolve it *)
  assert (F.equivalent r_inc_not_impl_strict v_gt_1);

  (* Case 3: Contradiction Strict/Inclusive *)
  (* Restrict (v < 1.0.0) given (v >= 1.0.0) -> False *)
  let v_lt_1 = VersionSyntax.(v < { major = 1; minor = 0; patch = 0 }) in
  let r_contra_1 =
    F.restrict v_lt_1 (c_ver_ge v { major = 1; minor = 0; patch = 0 })
  in
  assert (F.equivalent r_contra_1 F.false_);

  (* Case 4: Contradiction Strict/Strict *)
  (* Restrict (v < 1.0.0) given (v > 1.0.0) -> False *)
  let r_contra_2 =
    F.restrict v_lt_1 (c_ver_gt v { major = 1; minor = 0; patch = 0 })
  in
  assert (F.equivalent r_contra_2 F.false_);

  (* Case 5: Tighter bound selection *)
  (* Given (v > 5) AND (v >= 5), store should keep v > 5. *)
  (* If we restrict (v > 5) we expect True. *)
  let v_gt_5 = VersionSyntax.(v > { major = 5; minor = 0; patch = 0 }) in
  let r_tighter =
    F.restrict v_gt_5
      (c_ver_ge v { major = 5; minor = 0; patch = 0 }
      @ c_ver_gt v { major = 5; minor = 0; patch = 0 })
  in
  assert (F.equivalent r_tighter F.true_);

  Printf.printf "  restrict Version Edge Cases: OK\n";

  Printf.printf "  restrict: OK\n";
  ()

let test_restrict_validation () =
  Printf.printf "Running restrict validation tests...\n";
  (* Setup variables *)
  let s = Theo.Var.fresh () in
  let v = Theo.Var.fresh () in
  let expr = F.true_ in

  (* 1. Boolean Contradiction (already covered but good to be explicit) *)
  let b = Theo.Var.fresh () in
  let r_bool = F.restrict expr (c_bool b true @ c_bool b false) in
  assert (F.equivalent r_bool F.false_);

  (* 2. String Contradiction: Eq vs Eq *)
  (* s="a" AND s="b" -> False *)
  let r_s_eq_eq = F.restrict expr (c_str_eq s "a" @ c_str_eq s "b") in
  assert (F.equivalent r_s_eq_eq F.false_);

  (* 3. String Contradiction: Eq vs Ne *)
  (* s="a" AND s!="a" -> False *)
  let r_s_eq_ne = F.restrict expr (c_str_eq s "a" @ c_str_ne s "a") in
  assert (F.equivalent r_s_eq_ne F.false_);

  (* 4. String Consistency: Eq vs Ne (Valid) *)
  (* s="a" AND s!="b" -> True (consistent assignment to "a") *)
  let r_s_valid = F.restrict expr (c_str_eq s "a" @ c_str_ne s "b") in
  assert (F.equivalent r_s_valid F.true_);

  (* 5. Version Contradiction: Disjoint Ranges *)
  (* v > 2.0 AND v < 1.0 -> False *)
  let ver1 = { Version.major = 1; minor = 0; patch = 0 } in
  let ver2 = { Version.major = 2; minor = 0; patch = 0 } in
  let r_v_disjoint = F.restrict expr (c_ver_gt v ver2 @ c_ver_lt v ver1) in
  assert (F.equivalent r_v_disjoint F.false_);

  (* 6. Version Contradiction: Empty Range (Exclusive) *)
  (* v > 1.0 AND v < 1.0 -> False *)
  let r_v_empty = F.restrict expr (c_ver_gt v ver1 @ c_ver_lt v ver1) in
  assert (F.equivalent r_v_empty F.false_);

  (* 7. Version Contradiction: Contradictory Bounds *)
  (* v >= 2.0 AND v <= 1.0 -> False *)
  let r_v_contra = F.restrict expr (c_ver_ge v ver2 @ c_ver_le v ver1) in
  assert (F.equivalent r_v_contra F.false_);

  (* 8. Version Consistency: Overlapping Range *)
  (* v > 1.0 AND v < 3.0 -> True (Range (1.0, 3.0)) *)
  let ver3 = { Version.major = 3; minor = 0; patch = 0 } in
  let r_v_valid = F.restrict expr (c_ver_gt v ver1 @ c_ver_lt v ver3) in
  assert (F.equivalent r_v_valid F.true_);

  Printf.printf "  restrict validation: OK\n"

(* Test restrict with negative low branch case *)
let test_restrict_negative_low () =
  Printf.printf "Testing restrict negative low branch...\n";
  let open F.Syntax in
  let x = Theo.Var.fresh () in
  let y = Theo.Var.fresh () in
  let z = Theo.Var.fresh () in
  (* if x then y else z *)
  let f = F.ite (bool x) (bool y) (bool z) in

  (* Restrict z -> true *)
  (* Result should be if x then y else true *)
  (* make_node_simple x y true *)
  (* low=true (Not False) is Negative. *)
  let constraints = c_bool z true in
  let res = F.restrict f constraints in

  (* Expected: if x then y else true *)
  let expected = F.ite (bool x) (bool y) F.true_ in
  assert (F.equivalent res expected);
  Printf.printf "  Restrict negative low: OK\n";
  ()

(* Test quantifier operations *)
let test_quantifiers () =
  Printf.printf "Testing quantifier operations...\n";
  let open F.Syntax in
  let b1 = Theo.Var.fresh () in
  let b2 = Theo.Var.fresh () in
  let b3 = Theo.Var.fresh () in

  let e1 = bool b1 in
  let e2 = bool b2 in
  let _e3 = bool b3 in

  (* exists b. b = true (b can be true) *)
  assert (F.is_tautology (F.exists b1 e1));
  Printf.printf "  exists b. b = true: OK\n";

  (* forall b. b = false (not all values of b make b true) *)
  assert (F.equivalent (F.forall b1 e1) F.false_);
  Printf.printf "  forall b. b = false: OK\n";

  (* exists b. not b = true *)
  assert (F.is_tautology (F.exists b1 (not e1)));
  Printf.printf "  exists b. not b = true: OK\n";

  (* forall b. not b = false *)
  assert (F.equivalent (F.forall b1 (not e1)) F.false_);
  Printf.printf "  forall b. not b = false: OK\n";

  (* exists b. (b && c) = c (if c is true, b can be true) *)
  let and_bc = e1 && e2 in
  let exists_and = F.exists b1 and_bc in
  assert (F.equivalent exists_and e2);
  Printf.printf "  exists b. (b && c) = c: OK\n";

  (* forall b. (b || c) = c *)
  let or_bc = e1 || e2 in
  let forall_or = F.forall b1 or_bc in
  assert (F.equivalent forall_or e2);
  Printf.printf "  forall b. (b || c) = c: OK\n";
  (* exists b. true = true *)
  assert (F.is_tautology (F.exists b1 F.true_));
  Printf.printf "  exists b. true = true: OK\n";

  (* forall b. true = true *)
  assert (F.is_tautology (F.forall b1 F.true_));
  Printf.printf "  forall b. true = true: OK\n";

  (* exists b. false = false *)
  assert (F.equivalent (F.exists b1 F.false_) F.false_);
  Printf.printf "  exists b. false = false: OK\n";

  (* forall b. false = false *)
  assert (F.equivalent (F.forall b1 F.false_) F.false_);
  Printf.printf "  forall b. false = false: OK\n";

  (* Quantifier doesn't affect unrelated variables *)
  let exists_unrelated = F.exists b3 (e1 && e2) in
  assert (F.equivalent exists_unrelated (e1 && e2));
  Printf.printf "  exists on unrelated var: OK\n";

  (* Nested quantifiers: exists b. exists c. (b && c) = true *)
  let nested = F.exists b1 (F.exists b2 (e1 && e2)) in
  assert (F.is_tautology nested);
  Printf.printf "  exists b. exists c. (b && c) = true: OK\n";

  (* forall b. forall c. (b || c) = false *)
  let nested_forall = F.forall b1 (F.forall b2 (e1 || e2)) in
  assert (F.equivalent nested_forall F.false_);
  Printf.printf "  forall b. forall c. (b || c) = false: OK\n";

  (* Test with string variables *)
  let s = Theo.Var.fresh () in
  let eq_foo = StringSyntax.(s = "foo") in
  let eq_bar = StringSyntax.(s = "bar") in

  (* exists s. (s = "foo") combines all string atoms for s *)
  let exists_str = F.exists s eq_foo in
  assert (F.is_tautology exists_str);
  Printf.printf "  exists s. (s = \"foo\") = true: OK\n";

  (* exists s. (s = "foo" && s = "bar") - conflicting, but exists should still work *)
  let conflict = eq_foo && eq_bar in
  let exists_conflict = F.exists s conflict in
  (* The conflict is unsatisfiable, exists eliminates s but result is still false *)
  assert (F.equivalent exists_conflict F.false_);
  Printf.printf "  exists s. (s = \"foo\" && s = \"bar\") = false: OK\n";

  ()

let () =
  Printf.printf "\n=== Comprehensive BDD Testing ===\n\n";
  test_utility ();
  test_batch ();
  test_debug ();
  test_logical_operations ();
  test_theory_reasoning ();
  test_mixed_theory ();
  test_theory_simplification ();
  test_more_theory_simplification ();
  test_edge_cases ();
  test_hash_consing ();
  test_variable_ordering ();
  test_dot_output ();
  test_sat ();
  test_convenience ();
  test_restrict_ite ();
  test_restrict_negative_low ();
  test_quantifiers ();
  test_restrict_validation ();
  Printf.printf "\n=== All %d test suites passed! ===\n" 18
