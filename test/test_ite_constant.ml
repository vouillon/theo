open Theories
module F = Formula

let assert_equal_bool b1 b2 =
  if b1 <> b2 then failwith "assert_equal_bool failed"

let test_ite_constant_check () =
  let open Formula.Syntax in
  let v1 = bool (Theo.Var.fresh ()) in
  let v2 = bool (Theo.Var.fresh ()) in
  (* Tautology: v1 || not v1 -> True *)
  Printf.printf "Checking tautology...\n";
  let res = F.ite_constant v1 F.true_ (not v1) in
  assert_equal_bool (res = Constant true) true;

  (* Contradiction: v1 && not v1 -> False *)
  Printf.printf "Checking contradiction...\n";
  let res = F.ite_constant v1 (not v1) F.false_ in
  assert_equal_bool (res = Constant false) true;

  (* Identity: if v1 then v1 else v1 -> v1 (NonConstant) *)
  Printf.printf "Checking identity...\n";
  let res = F.ite_constant v1 v1 v1 in
  (* Wait, if f then f else f is f. If f is non-constant, result is NonConstant. *)
  assert_equal_bool (res = NonConstant) true;

  (* Non-constant: v1 || v2 *)
  Printf.printf "Checking v1 || v2...\n";
  let res = F.ite_constant v1 F.true_ v2 in
  assert_equal_bool (res = NonConstant) true;

  (* Non-constant: v1 && v2 *)
  Printf.printf "Checking v1 && v2...\n";
  let res = F.ite_constant v1 v2 F.false_ in
  assert_equal_bool (res = NonConstant) true;

  (* Check short-circuiting capability *)
  (* Construct a BDD that is constant true but large *)
  ()

(* Regression test for the polarity-collision bug in ITE_constant_cache: it
   used to key only on |g|, so ite_constant(f, g, h) and ite_constant(f, !g, h)
   shared a cache slot and returned each other's (generally different) result.

   This is only exercised when ITE_cache misses, so we (1) build the pool from
   FRESH variables and (2) compute ALL ite_constant results BEFORE any ite call
   populates ITE_cache. *)
let test_ite_constant_consistent () =
  let v = Theo.Var.fresh () in
  let s = Theo.Var.fresh () in
  let mk major = { Version.major; minor = 0; patch = 0 } in
  let base =
    [|
      VersionSyntax.(v <= mk 0);
      VersionSyntax.(v <= mk 1);
      VersionSyntax.(v < mk 2);
      StringSyntax.(s = "A");
      StringSyntax.(s = "B");
      StringSyntax.(s = "C");
    |]
  in
  let pool =
    let open Formula.Syntax in
    let l = ref [ F.true_; F.false_ ] in
    Array.iter (fun a -> l := a :: not a :: !l) base;
    for i = 0 to Array.length base - 1 do
      for j = i + 1 to Array.length base - 1 do
        l := (base.(i) && base.(j)) :: (base.(i) || base.(j)) :: !l
      done
    done;
    Array.of_list !l
  in
  let n = Array.length pool in
  (* Phase 1: ite_constant first, before ITE_cache is primed. *)
  let codes = Array.make (n * n * n) 0 in
  for fi = 0 to n - 1 do
    for gi = 0 to n - 1 do
      for hi = 0 to n - 1 do
        let c =
          match F.ite_constant pool.(fi) pool.(gi) pool.(hi) with
          | F.Constant false -> 0
          | F.Constant true -> 1
          | F.NonConstant -> 2
        in
        codes.(((fi * n) + gi) * n + hi) <- c
      done
    done
  done;
  (* Phase 2: compare against ite. *)
  let mismatches = ref 0 in
  for fi = 0 to n - 1 do
    for gi = 0 to n - 1 do
      for hi = 0 to n - 1 do
        let res_ite = F.ite pool.(fi) pool.(gi) pool.(hi) in
        let ite_true = F.equivalent res_ite F.true_ in
        let ite_false = F.equivalent res_ite F.false_ in
        let ok =
          match codes.(((fi * n) + gi) * n + hi) with
          | 1 -> ite_true
          | 0 -> ite_false
          | _ -> Stdlib.not ite_true && Stdlib.not ite_false
        in
        if not ok then incr mismatches
      done
    done
  done;
  if !mismatches > 0 then
    failwith (Printf.sprintf "ite_constant inconsistent with ite in %d cases" !mismatches)

let () =
  Printf.printf "Test ite_constant... ";
  test_ite_constant_check ();
  Printf.printf "OK\n";
  Printf.printf "Test ite_constant consistency... ";
  test_ite_constant_consistent ();
  Printf.printf "OK\n"
