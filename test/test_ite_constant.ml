open Theo
open Theo.Syntax

let assert_equal_bool b1 b2 =
  if b1 <> b2 then failwith "assert_equal_bool failed"

let test_ite_constant_check () =
  let v1 = atom (var ()) in
  let v2 = atom (var ()) in
  (* Tautology: v1 || not v1 -> True *)
  Printf.printf "Checking tautology...\n";
  let res = ite_constant v1 true_ (not v1) in
  assert_equal_bool (res = Constant true) true;

  (* Contradiction: v1 && not v1 -> False *)
  Printf.printf "Checking contradiction...\n";
  let res = ite_constant v1 (not v1) false_ in
  assert_equal_bool (res = Constant false) true;

  (* Identity: if v1 then v1 else v1 -> v1 (NonConstant) *)
  Printf.printf "Checking identity...\n";
  let res = ite_constant v1 v1 v1 in
  (* Wait, if f then f else f is f. If f is non-constant, result is NonConstant. *)
  assert_equal_bool (res = NonConstant) true;

  (* Non-constant: v1 || v2 *)
  Printf.printf "Checking v1 || v2...\n";
  let res = ite_constant v1 true_ v2 in
  assert_equal_bool (res = NonConstant) true;

  (* Non-constant: v1 && v2 *)
  Printf.printf "Checking v1 && v2...\n";
  let res = ite_constant v1 v2 false_ in
  assert_equal_bool (res = NonConstant) true;

  (* Check short-circuiting capability *)
  (* Construct a BDD that is constant true but large *)
  ()

let () =
  Printf.printf "Test ite_constant... ";
  test_ite_constant_check ();
  Printf.printf "OK\n"
