open Theo
open Theo.Syntax

let () =
  Printf.printf "Running Recursion Necessity Test...\\n";
  let v = var String in

  let is_a = is_equal v "A" in
  let is_b = is_equal v "B" in
  let is_c = is_equal v "C" in

  (* Cases:
     1. x="A" \/ (x!="B" && x!="C")
     Since x="A" implies x!="B" and x!="C", this should reduce to (x!="B" && x!="C").
  *)
  let not_b_and_not_c = (not is_b) && not is_c in
  let expr = is_a || not_b_and_not_c in

  Printf.printf "Expr: (x='A') \\/ (x != 'B' && x != 'C')\n";
  Printf.printf "Expected Size: %d (size of x!='B' && x!='C')\n"
    (size not_b_and_not_c);
  Printf.printf "Actual Size: %d\n" (size expr);

  if equivalent expr not_b_and_not_c then Printf.printf "SUCCESS: Equivalent\n"
  else (
    Printf.printf "FAILURE: Not equivalent\n";
    Printf.printf "Expr BDD: %s\n" (to_string expr);
    exit 1)
