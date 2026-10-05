(* Regression test: [Combine] of a theory with itself.

   [Leq (C)] and [Eq (C)] are applicative functors, so their [kind] type is
   shared by every [Combine] side that uses the same instance, and one
   variable can carry atoms of both sides. Theo cannot relate the two sides,
   so it must treat them as independent values. It used to apply the
   single-theory simplifications across sides instead, deciding for instance
   that [Left (v < 5)] entails [Right (v < 3)]. *)

module Int = struct
  type t = int

  let equal = Int.equal
  let compare = Int.compare
  let hash = Hashtbl.hash
  let to_string = string_of_int
end

module Str = struct
  include String

  let hash = Hashtbl.hash
  let to_string s = s
end

let check b msg = if Stdlib.not b then failwith ("FAIL: " ^ msg)

let test_leq () =
  let module L = Theo.Leq (Int) in
  let module T = Theo.Combine (L) (L) in
  let module B = Theo.Make (T) in
  let module SL = L.Syntax (T.Left (B)) in
  let module SR = L.Syntax (T.Right (B)) in
  let module CL = L.Syntax (T.Left (B.Constraint)) in
  let module CR = L.Syntax (T.Right (B.Constraint)) in
  let v = Theo.Var.fresh () in
  let a = SL.(v < 5) and b = SR.(v < 3) in
  check (Stdlib.not (B.is_tautology (B.implies a b))) "Left(v<5) => Right(v<3)";
  check (Stdlib.not (B.logical_implies a b)) "logical_implies across sides";
  check (B.is_satisfiable (B.and_ a (B.not b))) "Left(v<5) /\\ ~Right(v<3)";
  check (B.is_satisfiable (B.and_ b (B.not a))) "Right(v<3) /\\ ~Left(v<5)";
  (* Same-side reasoning is unaffected. *)
  check (B.logical_implies SL.(v < 3) a) "Left(v<3) => Left(v<5)";
  check (B.logical_implies b SR.(v < 5)) "Right(v<3) => Right(v<5)";
  check
    (Stdlib.not (B.is_satisfiable (B.and_ SR.(v < 3) SR.(v >= 5))))
    "Right(v<3) /\\ Right(v>=5)";
  (* [restrict], through each of its three code paths: a single constraint,
     a short list, and a long list (which uses the constraint store). *)
  let f = B.and_ a b in
  check (B.equal (B.restrict f CL.(v < 5)) b) "restrict single, Left";
  check (B.equal (B.restrict f CR.(v >= 3)) B.false_) "restrict single, Right";
  check (B.equal (B.restrict b CL.(v < 5)) b) "restrict b by Left";
  check (B.equal (B.restrict b CL.(v >= 7)) b) "restrict b by ~Left";
  let short = B.Constraint.and_ CL.(v < 5) CL.(v < 9) in
  check (B.equal (B.restrict f short) b) "restrict short list";
  let long =
    List.fold_left B.Constraint.and_ []
      [
        CL.(v < 5); CL.(v < 6); CL.(v < 7); CL.(v < 8); CL.(v < 9); CL.(v < 10);
      ]
  in
  check (B.equal (B.restrict f long) b) "restrict long list";
  let long_right =
    List.fold_left B.Constraint.and_ []
      [ CR.(v < 2); CR.(v < 3); CR.(v < 4); CR.(v < 5); CR.(v < 6); CR.(v < 7) ]
  in
  check (B.equal (B.restrict f long_right) a) "restrict long list, Right";
  check
    (B.equal (B.sop_to_bdd (B.irredundant_sop (B.or_ a b))) (B.or_ a b))
    "irredundant_sop round trip"

let test_eq () =
  let module E = Theo.Eq (Str) in
  let module T = Theo.Combine (E) (E) in
  let module B = Theo.Make (T) in
  let module SL = E.Syntax (T.Left (B)) in
  let module SR = E.Syntax (T.Right (B)) in
  let module CL = E.Syntax (T.Left (B.Constraint)) in
  let v = Theo.Var.fresh () in
  let a = SL.(v = "A") and b = SR.(v = "B") in
  check (B.is_satisfiable (B.and_ a b)) "Left(v=A) /\\ Right(v=B)";
  check (Stdlib.not (B.logical_implies a (B.not b))) "Left(v=A) => ~Right(v=B)";
  check
    (Stdlib.not (B.is_satisfiable (B.and_ a SL.(v = "B"))))
    "Left(v=A) /\\ Left(v=B)";
  (* A low chain mixing both sides: the Eq simplification must stop at the
     first atom of the other side. *)
  let f = B.or_ (B.and_ a b) (B.and_ SL.(v <> "C") SR.(v = "C")) in
  check
    (B.equal (B.restrict f CL.(v = "A")) (B.or_ b SR.(v = "C")))
    "restrict mixed chain";
  check (B.equal (B.restrict f CL.(v = "C")) B.false_) "restrict mixed chain 2"

let test_nested () =
  let module L = Theo.Leq (Int) in
  let module T = Theo.Combine (Theo.Combine (L) (L)) (L) in
  let module B = Theo.Make (T) in
  let module Inner = Theo.Combine (L) (L) in
  let module S1 = L.Syntax (Inner.Left (T.Left (B))) in
  let module S2 = L.Syntax (Inner.Right (T.Left (B))) in
  let module S3 = L.Syntax (T.Right (B)) in
  let v = Theo.Var.fresh () in
  let sides = [ S1.(v < 5); S2.(v < 3); S3.(v < 1) ] in
  List.iteri
    (fun i x ->
      List.iteri
        (fun j y ->
          if i <> j then
            check
              (B.is_satisfiable (B.and_ x (B.not y)))
              (Printf.sprintf "nested sides %d and %d independent" i j))
        sides)
    sides

let () =
  test_leq ();
  test_eq ();
  test_nested ();
  print_endline "OK"
