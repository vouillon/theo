open Theo
open Theo.Syntax

let assert_bool b msg = if Stdlib.not b then failwith ("FAIL: " ^ msg)

let test_logical_checks () =
  Printf.printf "Test logical checks...\n";
  let a = atom (var ()) in
  let b = atom (var ()) in

  (* logical_implies *)
  assert_bool (logical_implies (a && b) a) "a&b => a";
  assert_bool (logical_implies a (a || b)) "a => a|b";
  assert_bool (Stdlib.not (logical_implies a b)) "not (a => b)";
  assert_bool (logical_implies false_ a) "false => a";
  assert_bool (logical_implies a true_) "a => true";

  (* is_disjoint *)
  assert_bool (is_disjoint a (not a)) "a and not a disjoint";
  assert_bool (is_disjoint (a && b) (a && not b)) "a&b and a&!b disjoint";
  assert_bool (Stdlib.not (is_disjoint a b)) "a and b (overlap)";
  assert_bool (is_disjoint false_ a) "false and a disjoint";

  (* is_exhaustive *)
  assert_bool (is_exhaustive a (not a)) "a or not a exhaustive";
  assert_bool (Stdlib.not (is_exhaustive a b)) "a or b (not exhaustive)";
  assert_bool (is_exhaustive (a || b) (not a)) "a|b or !a exhaustive";
  assert_bool (is_exhaustive true_ a) "true or a exhaustive";

  Printf.printf "OK\n"

let () = test_logical_checks ()
