(*** Variables ***)

type version = { major : int; minor : int; patch : int }

(* version_bound pairs a version with a boolean indicating strictness:
   { version; inclusive=false } means "< ver", { version; inclusive=true } means "<= ver" *)
type version_bound = { version : version; inclusive : bool }

let compare_raw_version ({ major; minor; patch } : version)
    ({ major = major'; minor = minor'; patch = patch' } : version) =
  let c = Int.compare major major' in
  if c <> 0 then c
  else
    let c = Int.compare minor minor' in
    if c <> 0 then c else Int.compare patch patch'

let compare_version_bound ({ version; inclusive } : version_bound)
    ({ version = version'; inclusive = inclusive' } : version_bound) =
  let c = compare_raw_version version version' in
  if c <> 0 then c else Bool.compare inclusive inclusive'

type _ kind =
  | Boolean : bool kind
  | String : string kind
  | Version : version kind

type _ var = int

let var_counter = ref 0

let new_var (type a) (_ : a kind) : a var =
  incr var_counter;
  !var_counter

type atom_constraint =
  | Boolean of bool var * bool
  | String of string var * [ `Eq | `Ne ] * string
  | Version of version var * [ `Lt | `Le | `Ge | `Gt ] * version

(*** Atoms ***)

module Atom = struct
  type desc = IsTrue | IsEqual of string | IsLess of version_bound
  type t = { var : int; desc : desc; id : int }

  module WeakTbl = Weak.Make (struct
    type nonrec t = t

    let equal t t' =
      if t.var <> t'.var then false
      else
        (* Two atoms are equal iff they have the same variable and description. *)
        match (t.desc, t'.desc) with
        | IsTrue, IsTrue -> true
        | IsEqual s, IsEqual s' -> String.equal s s'
        | IsLess v, IsLess v' -> Int.equal (compare_version_bound v v') 0
        | _ -> false

    let hash (t : t) = Hashtbl.hash (t.var, t.desc)
  end)

  let equal a a' = a == a'

  let to_string { var; desc; _ } =
    match desc with
    | IsTrue -> Printf.sprintf "$%d" var
    | IsEqual s -> Printf.sprintf "$%d = %S" var s
    | IsLess { version = { major; minor; patch }; inclusive } ->
        Printf.sprintf "$%d %s %d.%d.%d" var
          (if inclusive then "<=" else "<")
          major minor patch

  let next_atom_id = ref 0
  let atom_tbl = WeakTbl.create 4096

  let make var desc =
    let id = !next_atom_id in
    let atom = { var; desc; id } in
    let atom' = WeakTbl.merge atom_tbl atom in
    if Int.equal atom'.id id then incr next_atom_id;
    atom'

  let sentinel = { var = max_int; desc = IsTrue; id = max_int }

  (* Atom ordering is crucial for correctness: theory simplification relies on
     atoms of the same variable being clustered, and version comparison further
     requires atoms to be ordered by their version bounds. *)
  let compare a a' =
    let c = Int.compare a.var a'.var in
    if c <> 0 then c
    else
      match (a.desc, a'.desc) with
      | IsTrue, IsTrue -> 0
      | IsTrue, _ -> -1
      | _, IsTrue -> 1
      | IsEqual v, IsEqual v' -> String.compare v v'
      | IsEqual _, _ -> -1
      | _, IsEqual _ -> 1
      | IsLess v, IsLess v' -> compare_version_bound v v'

  let min a a' =
    let c = compare a a' in
    if c < 0 then a else a'
end

type positive
type negative

(* BDD nodes are ordered by Atom.compare. *)

type _ u =
  (* False is our unique positive terminal node. *)
  | False : positive u
  (* If-then-else node. The low branch is always positive (no complemented
     edge), ensuring a canonical form where negations appear only on
     the high branch or at the root. *)
  | If : {
      atom : Atom.t;
      high : positive u;
      negate_high : bool;
      low : positive u;
      id : int;
    }
      -> positive u
  | Not : positive u -> negative u

type t = Bdd : _ u -> t [@@unboxed]

(* BDD operations. Hash-consing guarantees that structurally equal
   BDDs are physically equal, so equality is O(1). *)
module Bdd = struct
  let rec equal t t' =
    match (t, t') with
    | Bdd (Not t), Bdd (Not t') -> equal (Bdd t) (Bdd t')
    | Bdd (Not _), Bdd _ | Bdd _, Bdd (Not _) -> false
    | _ -> t == t'

  let are_complement (Bdd u) (Bdd v) =
    match (u, v) with
    | Not x, y -> equal (Bdd x) (Bdd y)
    | x, Not y -> equal (Bdd x) (Bdd y)
    | _ -> false

  let rec uid t =
    match t with
    | Bdd False -> 0
    | Bdd (If { id; _ }) -> id
    | Bdd (Not t) -> lnot (uid (Bdd t))

  let compare t t' = Int.compare (uid t) (uid t')
end

module UidTbl = Hashtbl.Make (struct
  type t = int

  let equal = Int.equal
  let hash x = x
end)

(*** Debugging ***)

let to_string (Bdd t) : string =
  let buf = Buffer.create 128 in
  let rec to_string_rec u =
    match u with
    | False -> Buffer.add_string buf "⊥"
    | If { atom; high = False; negate_high = true; low; _ } ->
        Buffer.add_string buf "If(";
        Buffer.add_string buf (Atom.to_string atom);
        Buffer.add_string buf ", ⊤, ";
        to_string_rec low;
        Buffer.add_char buf ')'
    | If { atom; high; negate_high; low; _ } ->
        Buffer.add_string buf "If(";
        Buffer.add_string buf (Atom.to_string atom);
        Buffer.add_string buf ", ";
        if negate_high then Buffer.add_string buf "¬";
        to_string_rec high;
        Buffer.add_string buf ", ";
        to_string_rec low;
        Buffer.add_char buf ')'
  in
  (match t with
  | Not False -> Buffer.add_string buf "⊤"
  | Not u ->
      Buffer.add_string buf "¬(";
      to_string_rec u;
      Buffer.add_char buf ')'
  | False as u -> to_string_rec u
  | If _ as u -> to_string_rec u);
  Buffer.contents buf

let print_dot (chan : out_channel) (t : t) : unit =
  let visited = UidTbl.create 16 in
  Printf.fprintf chan "digraph G {\n";
  let rec traverse : type a. a u -> unit =
   fun u ->
    let uid = Bdd.uid (Bdd u) in
    if Stdlib.not (UidTbl.mem visited uid) then (
      UidTbl.add visited uid ();
      match u with
      | False -> Printf.fprintf chan "  %d [label=\"⊥\", shape=box];\n" uid
      | Not False -> Printf.fprintf chan "  %d [label=\"⊤\", shape=box];\n" uid
      | Not u' ->
          Printf.fprintf chan "  %d [label=\"¬\", shape=circle];\n" uid;
          Printf.fprintf chan "  %d -> %d;\n" uid (Bdd.uid (Bdd u'));
          traverse u'
      | If { atom; high = False; negate_high = true; low; id } ->
          Printf.fprintf chan "  %d [label=\"%s\"];\n" id (Atom.to_string atom);
          let low_uid = Bdd.uid (Bdd low) in
          let true_ = Not False in
          Printf.fprintf chan "  %d -> %d [style=solid];\n" id
            (Bdd.uid (Bdd true_));
          traverse true_;
          Printf.fprintf chan "  %d -> %d [style=solid];\n" id low_uid;
          traverse low
      | If { atom; high; negate_high; low; id } ->
          Printf.fprintf chan "  %d [label=\"%s\"];\n" id (Atom.to_string atom);
          let high_uid = Bdd.uid (Bdd high) in
          let low_uid = Bdd.uid (Bdd low) in
          Printf.fprintf chan "  %d -> %d [style=%s];\n" id high_uid
            (if negate_high then "dashed" else "solid");
          Printf.fprintf chan "  %d -> %d [style=solid];\n" id low_uid;
          traverse high;
          traverse low)
  in
  match t with
  | Bdd u ->
      traverse u;
      Printf.fprintf chan "}\n"

(*** Core Logic ***)

let false_ = Bdd False
let true_ = Bdd (Not False)

let not u =
  match u with
  | Bdd (Not u) -> Bdd u
  | Bdd False -> true_
  | Bdd (If _ as f) -> Bdd (Not f)

let with_polarity negate t = if negate then Bdd (Not t) else Bdd t

(* split: Decomposes a BDD into (is_negated, positive_core).
   This allows treating Not as a flag rather than a node. *)
let split (Bdd u) =
  match u with
  | Not n -> (true, n)
  | If _ as n -> (false, n)
  | False as n -> (false, n)

module Positive = struct
  type t = positive u

  let uid (u : positive u) = match u with False -> 0 | If { id; _ } -> id

  module WeakTbl = Weak.Make (struct
    type t = positive u

    let equal (t : positive u) (t' : positive u) =
      match (t, t') with
      | ( If { atom; high; negate_high; low; _ },
          If
            {
              atom = atom';
              high = high';
              negate_high = negate_high';
              low = low';
              _;
            } ) ->
          Atom.equal atom atom' && high == high' && negate_high = negate_high'
          && low == low'
      | False, False -> true
      | If _, _ | _, If _ -> false

    let combine x y = (y * 1000003) + x

    let hash (t : positive u) =
      match t with
      | False -> 0
      | If { atom; high; negate_high; low; _ } ->
          let h =
            atom.id
            |> combine (uid high)
            |> combine (if negate_high then 1 else 0)
            |> combine (uid low)
          in
          h lxor (h lsr 17)
  end)

  let equal (t : positive u) (t' : positive u) = t == t'
  let hash = uid
  let weak_tbl = WeakTbl.create 4096
  let next_id = ref 1

  (* Hash-consing constructor: ensures each unique node has exactly one
     representation in memory. Returns existing node if found. *)
  let ite atom high negate_high low =
    let id = !next_id in
    let node =
      WeakTbl.merge weak_tbl (If { atom; high; negate_high; low; id })
    in
    match node with
    | If { id = id'; _ } when Int.equal id id' ->
        next_id := !next_id + 1;
        node
    | If _ | False -> node
end

(*** Theory Simplification ***)

module Simplify_cache = struct
  module Table = Ephemeron.K1.Make (Positive)

  let cache = Table.create 4096
  let find t = Table.find_opt cache t
  let add t res = Table.add cache t res
end

(* Theory simplification: when an atom like "v = A" is true, it implies
   "v != B" for any B != A. These functions propagate such implications
   through the BDD to simplify redundant nodes. *)
let rec simplify_node v (u : positive u) =
  match u with
  | If { atom; low; _ } when atom.var = v.Atom.var -> (
      match Simplify_cache.find u with
      | Some res -> res
      | None ->
          let res = simplify_node v low in
          Simplify_cache.add u res;
          res)
  | If _ | False -> u

(* simplify_assuming: Simplifies 'u' assuming atom 'v' is true. *)
let simplify_assuming v (u : positive u) (atom : Atom.t) (high : positive u)
    (negate_high : bool) (low : positive u) negate_result : t =
  if v.Atom.var <> atom.var then with_polarity negate_result u
  else
    match v.desc with
    | IsTrue -> with_polarity negate_result u
    | IsLess _ -> with_polarity (negate_result <> negate_high) high
    | IsEqual _ -> with_polarity negate_result (simplify_node v low)

let check_simplification v (atom : Atom.t) (high : positive u)
    (negate_high : bool) (low : positive u) (target : t) : bool =
  if v.Atom.var <> atom.var then false
  else
    match v.desc with
    | IsTrue -> false
    | IsLess _ -> Bdd.equal (with_polarity negate_high high) target
    | IsEqual _ -> Bdd.equal (Bdd (simplify_node v low)) target

(* make_node: Constructs a BDD node, applying simplifications. Given
   the normalizations perform by [ite], [low] is always positive. *)
let make_node atom (high : t) (low : t) : t =
  if Bdd.equal high low then high
  else
    match low with
    | Bdd
        (If
           { atom = l_atom; high = l_high; negate_high = l_neg; low = l_low; _ }
         as l_pos) ->
        if check_simplification atom l_atom l_high l_neg l_low high then low
        else
          let negate_high, h_node = split high in
          Bdd (Positive.ite atom h_node negate_high l_pos)
    | Bdd (False as l_pos) ->
        let negate_high, h_node = split high in
        Bdd (Positive.ite atom h_node negate_high l_pos)
    | Bdd (Not (False as l_inner)) ->
        let negate_high, h_node = split high in
        Bdd (Not (Positive.ite atom h_node (Stdlib.not negate_high) l_inner))
    | Bdd
        (Not
           (If
              {
                atom = l_atom;
                high = l_high;
                negate_high = l_neg;
                low = l_low;
                _;
              } as l_inner)) ->
        let (Bdd h_neg_inner) = not high in
        if check_simplification atom l_atom l_high l_neg l_low (Bdd h_neg_inner)
        then low
        else
          let negate_high, h_node = split high in
          Bdd (Not (Positive.ite atom h_node (Stdlib.not negate_high) l_inner))

(*** Core Computation ***)

let top_atom t =
  let _, u = split t in
  match u with If { atom; _ } -> atom | False -> Atom.sentinel

(* Theory-Aware Cofactors *)
let[@inline] cofactors v (t : t) =
  let negate_t, u = split t in
  match u with
  | If { atom; high; negate_high; low; _ } ->
      if atom == v then
        let eff_neg_high =
          if negate_t then Stdlib.not negate_high else negate_high
        in
        let h = with_polarity eff_neg_high high in
        let l = with_polarity negate_t low in
        (h, l)
      else
        let simplified =
          simplify_assuming v u atom high negate_high low negate_t
        in
        (simplified, t)
  | False -> (t, t)

(* ITE cache: memoizes ite(f, g, h) results. Since g can be positive or
   negated, we store both polarities in the same cell keyed by (f, |g|, h). *)
module ITE_cache = struct
  type 'a polarity_cell = { mutable pos : 'a option; mutable neg : 'a option }

  let empty_cell () = { pos = None; neg = None }

  module Store = Ephemeron.Kn.Make (Positive)

  let cache = Store.create 4096

  let find u g w =
    let is_neg, v = split g in
    let keys = [| u; v; w |] in
    match Store.find_opt cache keys with
    | None -> None
    | Some cell -> if is_neg then cell.neg else cell.pos

  let add u g w res =
    let is_neg, v = split g in
    let keys = [| u; v; w |] in
    let cell =
      match Store.find_opt cache keys with
      | Some c -> c
      | None ->
          let c = empty_cell () in
          Store.add cache keys c;
          c
    in
    if is_neg then cell.neg <- Some res else cell.pos <- Some res
end

(* ite f g h: computes "if f then g else h".

   Normalization rules for canonical form:
   - f is always positive (otherwise swap g and h)
   - h is always positive (otherwise negate the entire result)
   - Commutative cases use uid ordering to break symmetry *)
let rec ite f g h =
  let compute u g w =
    let f = Bdd u in
    let h = Bdd w in
    if Bdd.equal f g then ite f true_ h
    else if Bdd.are_complement f g then ite f false_ h
    else if Bdd.equal f h then ite f g false_
    else
      match ITE_cache.find u g w with
      | Some res -> res
      | None ->
          let v_f = top_atom f in
          let v_g = top_atom g in
          let v_h = top_atom h in
          let top = Atom.min v_f (Atom.min v_g v_h) in

          let f_high, f_low = cofactors top f in
          let g_high, g_low = cofactors top g in
          let h_high, h_low = cofactors top h in

          let r_high = ite f_high g_high h_high in
          let r_low = ite f_low g_low h_low in

          let res = make_node top r_high r_low in
          ITE_cache.add u g w res;
          res
  in
  match (f, g, h) with
  (* Terminal cases *)
  | _ when Bdd.equal g h -> g
  | Bdd (Not False), _, _ -> g
  | Bdd False, _, _ -> h
  | _, Bdd False, Bdd (Not False) -> not f
  | _, Bdd (Not False), Bdd False -> f
  (* Enforce f is positive *)
  | Bdd (Not f'), _, _ -> ite (Bdd f') h g
  (* Enforce h is positive *)
  | _, _, Bdd (Not h') -> not (ite f (not g) (Bdd h'))
  (* f \/ h *)
  | _, Bdd (Not False), _ when Bdd.compare f h > 0 -> ite h g f
  (* f /\ g *)
  | _, _, Bdd False when Bdd.compare f g > 0 -> ite g f h
  (* Recursion *)
  | Bdd (If _ as u), _, Bdd (False as w) -> compute u g w
  | Bdd (If _ as u), _, Bdd (If _ as w) -> compute u g w

type constant_result = Constant of bool | NonConstant

(* Constant_cache: Memoization for ite_constant checks.
   Keys are (f, g, h). Stores constant_result. *)
module Constant_cache = struct
  module Store = Ephemeron.Kn.Make (Positive)

  let cache = Store.create 4096

  let find u g w =
    let _, v = split g in
    let keys = [| u; v; w |] in
    Store.find_opt cache keys

  let add u g w res =
    let _, v = split g in
    let keys = [| u; v; w |] in
    Store.add cache keys res
end

let rec ite_constant f g h =
  let check u g w =
    (* Check if full result is already cached in ITE_cache *)
    match ITE_cache.find u g w with
    | Some res -> (
        match res with
        | Bdd False -> Constant false
        | Bdd (Not False) -> Constant true
        | Bdd _ -> NonConstant)
    | None -> (
        (* Check Constant_cache *)
        match Constant_cache.find u g w with
        | Some res -> res
        | None ->
            let v_f = top_atom f in
            let v_g = top_atom g in
            let v_h = top_atom h in
            let top = Atom.min v_f (Atom.min v_g v_h) in

            let f_high, f_low = cofactors top f in
            let g_high, g_low = cofactors top g in
            let h_high, h_low = cofactors top h in

            (* Short-circuiting recursion *)
            let res =
              match ite_constant f_high g_high h_high with
              | NonConstant -> NonConstant
              | Constant high_val -> (
                  match ite_constant f_low g_low h_low with
                  | NonConstant -> NonConstant
                  | Constant low_val ->
                      if high_val = low_val then Constant high_val
                      else NonConstant)
            in
            Constant_cache.add u g w res;
            res)
  in
  match (f, g, h) with
  (* Trivial identity cases *)
  | Bdd False, _, Bdd False
  | Bdd (Not False), Bdd False, _
  | _, Bdd False, Bdd False ->
      Constant false
  | Bdd False, _, Bdd (Not False)
  | Bdd (Not False), Bdd (Not False), _
  | _, Bdd (Not False), Bdd (Not False) ->
      Constant true
  | Bdd False, _, _ | Bdd (Not False), _, _ | _, Bdd (Not False), Bdd False ->
      NonConstant
  | _, g, h when Bdd.equal g h -> NonConstant
  (* Normalization to match ITE structure/invariants *)
  | Bdd (Not u), g, h -> ite_constant (Bdd u) h g
  | f, g, h when Bdd.equal f g ->
      ite_constant f true_ h (* If f then f else h -> if f then true else h *)
  | f, g, h when Bdd.are_complement f g -> ite_constant f false_ h
  | f, g, h when Bdd.equal f h -> ite_constant f g false_
  (* Canonical ordering for commutativity *)
  | f, Bdd (Not False), h when Bdd.compare f h > 0 ->
      ite_constant h true_ f (* f \/ h -> h \/ f *)
  | f, g, Bdd False when Bdd.compare f g > 0 ->
      ite_constant g f false_ (* f /\ g -> g /\ f *)
  (* Normalize h to be positive *)
  | f, g, Bdd (Not u) -> (
      match ite_constant f (not g) (Bdd u) with
      | Constant b -> Constant (Stdlib.not b)
      | NonConstant -> NonConstant)
  (* General decomposition *)
  | Bdd (If _ as u), _, Bdd (False as w) -> check u g w
  | Bdd (If _ as u), _, Bdd (If _ as w) -> check u g w

(*** Constructors ***)

let make_atom i = Bdd (Positive.ite i False true False)
let atom v = make_atom (Atom.make v IsTrue)
let is_equal v s = make_atom (Atom.make v (IsEqual s))
let is_not_equal v s = not (is_equal v s)

let is_lt v ver =
  make_atom (Atom.make v (IsLess { version = ver; inclusive = false }))

let is_le v ver =
  make_atom (Atom.make v (IsLess { version = ver; inclusive = true }))

let is_gt v ver = not (is_le v ver)
let is_ge v ver = not (is_lt v ver)

(*** High-Level Operations ***)

module Constraint_store = struct
  module StringSet = Set.Make (String)

  type t = {
    bools : (int, bool) Hashtbl.t;
    strs_eq : (int, string) Hashtbl.t;
    strs_ne : (int, StringSet.t) Hashtbl.t;
    vers_lower : (int, version_bound) Hashtbl.t; (* >= bound *)
    vers_upper : (int, version_bound) Hashtbl.t; (* < bound *)
    mutable max_var : int;
  }

  let create constraints =
    let store =
      {
        bools = Hashtbl.create 16;
        strs_eq = Hashtbl.create 16;
        strs_ne = Hashtbl.create 16;
        vers_lower = Hashtbl.create 16;
        vers_upper = Hashtbl.create 16;
        max_var = -1;
      }
    in
    let update_lower v new_bound =
      match Hashtbl.find_opt store.vers_lower v with
      | Some current ->
          if compare_version_bound new_bound current > 0 then
            Hashtbl.replace store.vers_lower v new_bound
      | None -> Hashtbl.replace store.vers_lower v new_bound
    in
    let update_upper v new_bound =
      match Hashtbl.find_opt store.vers_upper v with
      | Some current ->
          if compare_version_bound new_bound current < 0 then
            Hashtbl.replace store.vers_upper v new_bound
      | None -> Hashtbl.replace store.vers_upper v new_bound
    in
    try
      List.iter
        (fun c ->
          match c with
          | Boolean (v, b) -> (
              if v > store.max_var then store.max_var <- v;
              match Hashtbl.find_opt store.bools v with
              | Some b' when b <> b' -> raise Exit (* Contradiction *)
              | _ -> Hashtbl.replace store.bools v b)
          | String (v, op, s) -> (
              if v > store.max_var then store.max_var <- v;
              match op with
              | `Eq -> (
                  (* Check against existing NE constraints *)
                  (match Hashtbl.find_opt store.strs_ne v with
                  | Some set when StringSet.mem s set -> raise Exit
                  | _ -> ());
                  (* Check against existing EQ constraints *)
                  match Hashtbl.find_opt store.strs_eq v with
                  | Some s' when Stdlib.not (String.equal s s') -> raise Exit
                  | _ -> Hashtbl.replace store.strs_eq v s)
              | `Ne ->
                  (* Check against existing EQ constraint *)
                  (match Hashtbl.find_opt store.strs_eq v with
                  | Some s' when String.equal s s' -> raise Exit
                  | _ -> ());
                  let set =
                    match Hashtbl.find_opt store.strs_ne v with
                    | Some set -> set
                    | None -> StringSet.empty
                  in
                  Hashtbl.replace store.strs_ne v (StringSet.add s set))
          | Version (v, op, ver) -> (
              if v > store.max_var then store.max_var <- v;
              match op with
              | `Ge -> update_lower v { version = ver; inclusive = false }
              | `Gt -> update_lower v { version = ver; inclusive = true }
              | `Le -> update_upper v { version = ver; inclusive = true }
              | `Lt -> update_upper v { version = ver; inclusive = false }))
        constraints;
      (* Final consistency check for versions *)
      Hashtbl.iter
        (fun v lower ->
          match Hashtbl.find_opt store.vers_upper v with
          | Some upper ->
              if compare_version_bound lower upper >= 0 then raise Exit
          | None -> ())
        store.vers_lower;
      Some store
    with Exit -> None

  let find_bool t v = Hashtbl.find_opt t.bools v
  let find_string_eq t v = Hashtbl.find_opt t.strs_eq v

  let check_string_ne t v s =
    match Hashtbl.find_opt t.strs_ne v with
    | Some set -> StringSet.mem s set
    | None -> false

  let find_lower_bound t v = Hashtbl.find_opt t.vers_lower v
  let find_upper_bound t v = Hashtbl.find_opt t.vers_upper v
end

let restrict t constraints =
  match t with
  | Bdd False -> false_
  | _ -> (
      if constraints = [] then t
      else
        match Constraint_store.create constraints with
        | None ->
            false_ (* Contradiction in constraints -> empty set -> false *)
        | Some store -> (
            let eval_atom (atom : Atom.t) =
              match atom.desc with
              | IsTrue -> Constraint_store.find_bool store atom.var
              | IsEqual s -> (
                  match Constraint_store.find_string_eq store atom.var with
                  | Some s' -> Some (String.equal s s')
                  | None ->
                      if Constraint_store.check_string_ne store atom.var s then
                        Some false
                      else None)
              | IsLess atom_bound ->
                  (* Check implications from range *)
                  (* Atom is: var < v_atom (if !inc) or var <= v_atom (if inc) *)
                  let implies_true =
                    match Constraint_store.find_upper_bound store atom.var with
                    | Some u -> compare_version_bound u atom_bound <= 0
                    | None -> false
                  in
                  if implies_true then Some true
                  else
                    let implies_false =
                      match
                        Constraint_store.find_lower_bound store atom.var
                      with
                      | Some l -> compare_version_bound l atom_bound >= 0
                      | None -> false
                    in
                    if implies_false then Some false else None
            in
            let visited = UidTbl.create 1024 in
            let rec visit u =
              let uid = Positive.uid u in
              match UidTbl.find_opt visited uid with
              | Some res -> res
              | None ->
                  let res =
                    match u with
                    | False -> false_
                    | If { atom; high; negate_high; low; _ } -> (
                        if atom.var > store.max_var then Bdd u
                        else
                          match eval_atom atom with
                          | Some true ->
                              let h = visit high in
                              if negate_high then not h else h
                          | Some false -> visit low
                          | None ->
                              let h = visit high in
                              let l = visit low in
                              make_node atom
                                (if negate_high then not h else h)
                                l)
                  in
                  UidTbl.add visited uid res;
                  res
            in
            match t with
            | Bdd False -> false_
            | Bdd (Not u) -> not (visit u)
            | Bdd (If _ as u) -> visit u))

let and_ a b = ite a b false_
let or_ a b = ite a true_ b
let xor a b = ite a (not b) b
let iff a b = not (xor a b)
let implies a b = ite a b true_

let logical_implies a b =
  match ite_constant a b true_ with Constant true -> true | _ -> false

let is_disjoint a b =
  match ite_constant a b false_ with Constant false -> true | _ -> false

let is_exhaustive a b =
  match ite_constant a true_ b with Constant true -> true | _ -> false

(* Quantifier elimination: removes all atoms mentioning the given variable *)
let quantify combine_op (type a) (v : a var) (t : t) : t =
  let target_var = v in
  (* Cache: keyed by (uid, polarity) *)
  let visited = UidTbl.create 1024 in
  let rec visit negate u =
    let uid = Positive.uid u in
    let key = (uid lsl 1) lor if negate then 1 else 0 in
    match UidTbl.find_opt visited key with
    | Some res -> res
    | None ->
        let res =
          match u with
          | False -> if negate then true_ else false_
          | If { atom; high; negate_high; low; _ } -> (
              if atom.var > target_var then with_polarity negate u
              else
                (* Effective polarity for high branch *)
                let h_negate =
                  if negate_high then Stdlib.not negate else negate
                in
                let h = visit h_negate high in
                let l = visit negate low in
                if atom.var = target_var then
                  (* Quantify: combine high and low branches *)
                  combine_op h l
                else
                  (* Keep node, recurse on children *)
                  match l with
                  | Bdd (Not l_inner) ->
                      let res = make_node atom (not h) (Bdd l_inner) in
                      not res
                  | _ -> make_node atom h l)
        in
        UidTbl.add visited key res;
        res
  in
  let negate, u = split t in
  visit negate u

let exists (type a) (v : a var) (t : t) : t = quantify or_ v t
let forall (type a) (v : a var) (t : t) : t = quantify and_ v t
let is_eq v ver = and_ (is_le v ver) (is_ge v ver)

let balanced_reduce op base l =
  let cmp a b =
    let va = top_atom a in
    let vb = top_atom b in
    let c = Atom.compare vb va in
    if c <> 0 then c else Bdd.compare a b
  in
  let l = List.sort cmp l in
  let rec reduce op base l =
    match l with [] -> base | [ x ] -> x | _ -> aux op base [] l
  and aux op base acc l =
    match l with
    | [] -> reduce op base (List.rev acc)
    | [ x ] -> reduce op base (List.rev (x :: acc))
    | x :: y :: t -> aux op base (op x y :: acc) t
  in
  reduce op base l

let and_list exprs = balanced_reduce and_ true_ exprs
let or_list exprs = balanced_reduce or_ false_ exprs
let is_tautology t = Bdd.equal t true_
let is_satisfiable t = Stdlib.not (Bdd.equal t false_)
let equivalent a b = Bdd.equal a b

let size t =
  (* Use a hash table to track visited nodes and count unique ones *)
  let visited = UidTbl.create 16 in
  let rec count : type a. a u -> int =
   fun u ->
    let uid = Bdd.uid (Bdd u) in
    if UidTbl.mem visited uid then 0
    else (
      UidTbl.add visited uid ();
      match u with
      | False -> 1
      | Not u' -> count u'
      | If { high; low; _ } -> 1 + count high + count low)
  in
  match t with Bdd u -> count u

(*** Syntax ***)

module Syntax = struct
  let ( && ) = and_
  let ( || ) = or_
  let not = not
  let ( ==> ) = implies
  let ( <=> ) = iff
  let ( <+> ) = xor

  module String = struct
    let ( = ) = is_equal
    let ( <> ) = is_not_equal
  end

  module Version = struct
    let ( < ) = is_lt
    let ( <= ) = is_le
    let ( > ) = is_gt
    let ( >= ) = is_ge
    let ( = ) = is_eq
    let ( <> ) v ver = not (is_eq v ver)
  end
end

(*** Solvers ***)

let sat (t : t) : atom_constraint list option =
  let rec solve u target =
    match u with
    | False -> [] (* Only reached if valid, so return empty constraints *)
    | If { atom; high; negate_high; low; _ } ->
        (* Prefer high branch. Check if high is capable of satisfying
            eff_target. *)
        let eff_target = if negate_high then Stdlib.not target else target in
        let high_satisfiable =
          match (high, eff_target) with False, true -> false | _, _ -> true
        in
        if high_satisfiable then
          let constraints = solve high eff_target in
          let c =
            match atom.desc with
            | Atom.IsTrue -> Boolean (atom.var, true)
            | Atom.IsEqual s -> String (atom.var, `Eq, s)
            | Atom.IsLess { version; inclusive } ->
                Version (atom.var, (if inclusive then `Le else `Lt), version)
          in
          c :: constraints
        else
          let constraints = solve low target in
          let c =
            match atom.desc with
            | Atom.IsTrue -> Boolean (atom.var, false)
            | Atom.IsEqual s -> String (atom.var, `Ne, s)
            | Atom.IsLess { version; inclusive } ->
                Version (atom.var, (if inclusive then `Gt else `Ge), version)
          in
          c :: constraints
  in
  match t with
  | Bdd False -> None
  | Bdd (If _ as u) -> Some (solve u true)
  | Bdd (Not u) -> Some (solve u false)

let shortest_sat (t : t) : atom_constraint list option =
  let dist_cache = UidTbl.create 128 in
  let rec get_dist u target =
    let uid = Bdd.uid (Bdd u) in
    let key = (uid lsl 1) lor if target then 1 else 0 in
    match UidTbl.find_opt dist_cache key with
    | Some d -> d
    | None ->
        let d =
          match (u, target) with
          | False, true -> max_int (* Impossible *)
          | False, false -> 0 (* Reached! *)
          | If { high; negate_high; low; _ }, _ ->
              let eff_target_high =
                if negate_high then Stdlib.not target else target
              in
              let d_high = get_dist high eff_target_high in
              if d_high = 0 then 1
              else
                let d_low = get_dist low target in
                let min_d =
                  if d_high = max_int && d_low = max_int then max_int
                  else 1 + min d_high d_low
                in
                min_d
        in
        UidTbl.add dist_cache key d;
        d
  in
  (* Trace back *)
  let rec trace u target =
    match (u, target) with
    | False, false -> []
    | False, true -> assert false
    | If { atom; high; negate_high; low; _ }, _ ->
        let eff_target_high =
          if negate_high then Stdlib.not target else target
        in
        let d_high = get_dist high eff_target_high in
        if
          (* If d_high is 0, we know it's optimal (local cost 1). *)
          d_high = 0
          ||
          let d_low = get_dist low target in
          d_high <= d_low
        then
          let c =
            match atom.desc with
            | Atom.IsTrue -> Boolean (atom.var, true)
            | Atom.IsEqual s -> String (atom.var, `Eq, s)
            | Atom.IsLess { version; inclusive } ->
                Version (atom.var, (if inclusive then `Le else `Lt), version)
          in
          c :: trace high eff_target_high
        else
          let c =
            match atom.desc with
            | Atom.IsTrue -> Boolean (atom.var, false)
            | Atom.IsEqual s -> String (atom.var, `Ne, s)
            | Atom.IsLess { version; inclusive } ->
                Version (atom.var, (if inclusive then `Gt else `Ge), version)
          in
          c :: trace low target
  in
  match t with
  | Bdd False -> None
  | Bdd (Not u) -> Some (trace u false)
  | Bdd (If _ as u) -> Some (trace u true)
