module Version = struct
  type t = { major : int; minor : int; patch : int }

  let compare { major; minor; patch }
      { major = major'; minor = minor'; patch = patch' } =
    let c = Int.compare major major' in
    if c <> 0 then c
    else
      let c = Int.compare minor minor' in
      if c <> 0 then c else Int.compare patch patch'

  let equal v v' = compare v v' = 0
  let hash = Hashtbl.hash

  let to_string { major; minor; patch } =
    Printf.sprintf "%d.%d.%d" major minor patch
end

module String = struct
  include String

  let to_string s = Printf.sprintf "%S" s
end

module Leq = Theo.Leq (Version)
module Eq = Theo.Eq (String)
module Theories = Theo.Combine (Leq) (Eq)
module Formula = Theo.Make (Theories)
module VersionSyntax = Leq.Syntax (Theories.Left (Formula))
module StringSyntax = Eq.Syntax (Theories.Right (Formula))
module VersionCstr = Leq.Syntax (Theories.Left (Formula.Constraint))
module StringCstr = Eq.Syntax (Theories.Right (Formula.Constraint))
