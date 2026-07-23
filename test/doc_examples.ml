(* Compiled versions of the usage examples in README.md (and the theo.mli
   header). They exist to ensure the documented code keeps compiling and
   behaving as described: keep them in sync with the documentation. *)

(* Example 1: Simple Boolean Logic *)

module BDD = Theo.Make (Theo.Void)

let () =
  let x = BDD.Var.fresh () in
  let y = BDD.Var.fresh () in

  (* Construct expressions *)
  let open BDD.Syntax in
  let expr = bool x && not (bool y) in

  (* Check tautology/satisfiability *)
  let is_sat = BDD.is_satisfiable expr in
  (* true *)
  let is_taut = BDD.is_tautology expr in
  (* false *)
  assert is_sat;
  assert (Stdlib.not is_taut)

(* Example 2: Combining Theories *)

(* 1. Define your atomic types *)
module StringAtom = struct
  include String

  let to_string s = s
  let hash = Hashtbl.hash
end

module VersionAtom = struct
  type t = { major : int; minor : int; patch : int }

  let compare = compare
  let equal = ( = )
  let hash = Hashtbl.hash
  let to_string v = Printf.sprintf "%d.%d.%d" v.major v.minor v.patch
end

(* 2. Instantiate primitive theories *)
module StringEq = Theo.Eq (StringAtom)
module VersionLeq = Theo.Leq (VersionAtom)

(* 3. Combine them into a single theory *)
module MyTheory = Theo.Combine (VersionLeq) (StringEq)

(* 4. Create the BDD module *)
module MyBDD = Theo.Make (MyTheory)

(* 5. Instantiate syntax helpers for convenient construction *)
module V = VersionLeq.Syntax (MyTheory.Left (MyBDD))
module S = StringEq.Syntax (MyTheory.Right (MyBDD))

(* 6. Now you can mix them! *)
let v_var = MyBDD.Var.fresh ()
let s_var = MyBDD.Var.fresh ()
let v = { VersionAtom.major = 1; minor = 0; patch = 0 }
let s = "production"

(* Use infix operators: V.(...) and S.(...) *)
let expr = MyBDD.and_ V.(v_var < v) S.(s_var = s)
(* "Version < 1.0.0 AND String = 'production'" *)

let () = assert (MyBDD.is_satisfiable expr)

(* Example 3: Working with Constraints *)

(* 1. Build constraint syntax helpers *)
(* Pass MyBDD.Constraint instead of MyBDD *)
module V_cstr = VersionLeq.Syntax (MyTheory.Left (MyBDD.Constraint))
module S_cstr = StringEq.Syntax (MyTheory.Right (MyBDD.Constraint))

let () =
  (* 2. Create constraints *)
  let c1 = V_cstr.(v_var < v) in
  let c2 = S_cstr.(s_var = s) in

  (* 3. Restrict a BDD *)
  (* assume that v_var < 1.0.0 *)
  let restricted_expr = MyBDD.restrict expr c1 in
  assert (MyBDD.equivalent restricted_expr S.(s_var = s));
  assert (MyBDD.is_tautology (MyBDD.restrict expr (MyBDD.Constraint.and_ c1 c2)));

  (* 4. Introspection *)
  let describe (c : MyBDD.atomic_constraint) =
    match MyBDD.view_constraint c with
    | MyBDD.Constraint { payload = Bool; value; _ } ->
        Printf.sprintf "boolean variable is %b" value
    | MyBDD.Constraint { payload = Theory desc; value; _ } -> (
        match desc with
        | MyTheory.Left (VersionLeq.Bound { limit; inclusive }) ->
            Printf.sprintf "version %s %s is %b"
              (if inclusive then "<=" else "<")
              (VersionAtom.to_string limit)
              value
        | MyTheory.Right (StringEq.Const s) ->
            Printf.sprintf "string = %s is %b" s value)
  in
  assert (List.map describe c1 = [ "version < 1.0.0 is true" ]);
  assert (List.map describe c2 = [ "string = production is true" ])
