(* [restrict] has three code paths, picked by the length of the constraint
   list: a single constraint, up to five (scanned directly, consistency
   checked pairwise), and longer lists (a constraint store). Check that the
   short-list path agrees with the store on random lists of 2 to 5
   constraints, contradictory ones included: duplicating every constraint
   does not change the meaning of a list but sends it to the store. *)

open Theories
module F = Formula

let bvars = Array.init 2 (fun _ -> Theo.Var.fresh ())
let vvars = Array.init 2 (fun _ -> Theo.Var.fresh ())
let svars = Array.init 2 (fun _ -> Theo.Var.fresh ())
let version i = { Version.major = i; minor = 0; patch = 0 }
let strings = [| "a"; "b"; "c" |]
let pick a = a.(Random.int (Array.length a))

(* A random atom, as a BDD and as a (positive) constraint. *)
let random_atom () =
  match Random.int 4 with
  | 0 ->
      let v = pick bvars in
      (F.bool v, F.Constraint.bool v true)
  | 1 ->
      let v = pick vvars and x = version (Random.int 4) in
      (VersionSyntax.(v < x), VersionCstr.(v < x))
  | 2 ->
      let v = pick vvars and x = version (Random.int 4) in
      (VersionSyntax.(v <= x), VersionCstr.(v <= x))
  | _ ->
      let v = pick svars and x = pick strings in
      (StringSyntax.(v = x), StringCstr.(v = x))

let random_constraint () =
  let _, c = random_atom () in
  if Random.bool () then c else F.Constraint.not c

let rec random_formula depth =
  if depth = 0 then fst (random_atom ())
  else
    match Random.int 3 with
    | 0 -> F.not (random_formula (depth - 1))
    | 1 -> F.and_ (random_formula (depth - 1)) (random_formula (depth - 1))
    | _ -> F.or_ (random_formula (depth - 1)) (random_formula (depth - 1))

let () =
  Random.init 2026;
  let contradictory = ref 0 in
  for i = 1 to 20_000 do
    let f = random_formula 4 in
    let cs =
      List.concat (List.init (2 + Random.int 4) (fun _ -> random_constraint ()))
    in
    let short = F.restrict f cs in
    let long = F.restrict f (cs @ cs) in
    if F.equal (F.restrict F.true_ cs) F.false_ then incr contradictory;
    if Stdlib.not (F.equal short long) then (
      Printf.printf
        "Mismatch at iteration %d\n  f = %s\n  short = %s\n  long = %s\n" i
        (F.to_string f) (F.to_string short) (F.to_string long);
      exit 1)
  done;
  (* Make sure the contradiction check was actually exercised. *)
  if !contradictory < 1000 then (
    Printf.printf "Only %d contradictory lists\n" !contradictory;
    exit 1);
  print_endline "OK"
