(** Theory-Augmented Binary Decision Diagrams (BDDs)

    This module provides an efficient implementation of Binary Decision Diagrams
    with support for theory reasoning over booleans, strings, and semantic
    versions.

    BDDs are canonical representations of boolean functions that enable
    efficient logical operations and satisfiability checking through
    hash-consing and memoization.

    {b Features:}
    - Automatic node sharing via hash-consing
    - Memoized operations for performance
    - Theory atoms: boolean tests, string equality, version comparisons
    - Type-safe variable system using GADTs

    {b Example usage:}
    {[
      let open Theo.Syntax in
      let b1 = Theo.new_var Boolean in
      let b2 = Theo.new_var Boolean in
      let expr = Theo.atom b1 && not (Theo.atom b2) in
      if Theo.is_tautology expr then Printf.printf "Always true\n"
      else Printf.printf "Depends on variables\n"
    ]} *)

(** {1 Types} *)

type version = { major : int; minor : int; patch : int }
(** Semantic version as [{ major; minor; patch }] record. *)

type _ kind =
  | Boolean : bool kind
  | String : string kind
  | Version : version kind
      (** GADT representing the kind of a variable. Ensures type safety between
          variables and their values. *)

type _ var
(** Type-indexed variable. The type parameter indicates what kind of values the
    variable can hold (bool, string, or version). *)

type t
(** Abstract type representing a BDD expression. *)

type atom_constraint =
  | Boolean of bool var * bool
  | String of string var * [ `Eq | `Ne ] * string
  | Version of version var * [ `Lt | `Le | `Ge | `Gt ] * version
      (** Represents an atomic constraint on a variable that contributes to
          satisfying the formula. *)

(** {1 Variable Creation} *)

val new_var : 'kind kind -> 'kind var
(** [new_var kind] creates a fresh variable of the specified kind. Each call
    returns a unique variable.

    Example:
    {[
      let b = new_var Boolean in
      let s = new_var String in
      let v = new_var Version in
    ]} *)

(** {1 Atomic Formulas} *)

val atom : bool var -> t
(** [atom var] creates an expression that is true when [var] is true.

    Example: [let expr = atom b] *)

val is_equal : string var -> string -> t
(** [is_equal var str] creates an expression that is true when [var] equals
    [str].

    Example: [let expr = is_equal s "hello"] *)

val is_not_equal : string var -> string -> t
(** [is_not_equal var str] creates an expression that is true when [var] does
    not equal [str]. Equivalent to [not (is_equal var str)].

    Example: [let expr = is_not_equal s "hello"] *)

val is_lt : version var -> version -> t
(** [is_lt var ver] creates an expression that is true when [var] is strictly
    less than [ver] according to semantic versioning rules.

    Example: [let expr = is_lt v (1, 2, 3)] *)

val is_le : version var -> version -> t
(** [is_le var ver] creates an expression that is true when [var] is less than
    or equal to [ver] according to semantic versioning rules.

    Example: [let expr = is_le v (1, 2, 3)] *)

val is_gt : version var -> version -> t
(** [is_gt var ver] creates an expression that is true when [var] is strictly
    greater than [ver]. Equivalent to [not (is_le var ver)].

    Example: [let expr = is_gt v (1, 2, 3)] *)

val is_ge : version var -> version -> t
(** [is_ge var ver] creates an expression that is true when [var] is greater
    than or equal to [ver]. Equivalent to [not (is_lt var ver)].

    Example: [let expr = is_ge v (1, 2, 3)] *)

val is_eq : version var -> version -> t
(** [is_eq var ver] creates an expression that is true when [var] equals [ver].
    Equivalent to [and_ (is_le var ver) (not (is_lt var ver))].

    Example: [let expr = is_eq v (1, 2, 3)] *)

(** {1 Logical Constants} *)

val false_ : t
(** The constant false expression. *)

val true_ : t
(** The constant true expression. *)

(** {1 Logical Connectives} *)

val not : t -> t
(** [not expr] negates the expression.

    Complexity: O(1) *)

val and_ : t -> t -> t
(** [and_ a b] computes the conjunction (AND) of two expressions.

    Complexity: O(|a| × |b|) where |·| is the number of nodes *)

val or_ : t -> t -> t
(** [or_ a b] computes the disjunction (OR) of two expressions.

    Complexity: O(|a| × |b|) *)

val xor : t -> t -> t
(** [xor a b] computes the exclusive or of two expressions. True when exactly
    one of [a] or [b] is true.

    Complexity: O(|a| × |b|) *)

val iff : t -> t -> t
(** [iff a b] computes the biconditional (if and only if) of two expressions.
    True when [a] and [b] have the same truth value. Equivalent to
    [not (xor a b)].

    Complexity: O(|a| × |b|) *)

val implies : t -> t -> t
(** [implies a b] constructs the implication [a => b] (equivalent to
    [not a || b]). Returns a BDD representing the logical implication.

    To check if [a] logically implies [b] (i.e., is a tautology), use
    [is_tautology (implies a b)].

    Complexity: O(|a| × |b|) *)

val ite : t -> t -> t -> t
(** [ite cond then_ else_] computes the If-Then-Else operation. Equivalent to
    [(cond && then_) || (not cond && else_)].

    Complexity: O(|cond| × |then_| × |else_|) *)

(** Syntax for convenient infix operators. Open locally with
    [let open Theo.Syntax in ...] *)
module Syntax : sig
  val ( && ) : t -> t -> t
  val ( || ) : t -> t -> t
  val not : t -> t

  val ( ==> ) : t -> t -> t
  (** Implication *)

  val ( <=> ) : t -> t -> t
  (** Biconditional (iff) *)

  val ( <+> ) : t -> t -> t
  (** Exclusive OR (xor) *)

  module String : sig
    val ( = ) : string var -> string -> t
    val ( <> ) : string var -> string -> t
  end

  module Version : sig
    val ( < ) : version var -> version -> t
    val ( <= ) : version var -> version -> t
    val ( > ) : version var -> version -> t
    val ( >= ) : version var -> version -> t
    val ( = ) : version var -> version -> t
    val ( <> ) : version var -> version -> t
  end
end

(** {1 Properties} *)

val is_tautology : t -> bool
(** [is_tautology expr] returns true if [expr] is the constant true.

    Complexity: O(1) *)

val is_satisfiable : t -> bool
(** [is_satisfiable expr] returns true if [expr] has at least one satisfying
    assignment. Equivalent to [sat expr <> None] but more efficient.

    Complexity: O(1) *)

val equivalent : t -> t -> bool
(** [equivalent a b] checks if [a] and [b] are structurally identical. Due to
    hash-consing, structurally identical BDDs represent the same logical
    function.

    Complexity: O(1) *)

val size : t -> int
(** [size expr] returns the number of unique nodes in the BDD. Useful for
    analyzing BDD complexity.

    Complexity: O(|expr|) *)

val restrict : t -> atom_constraint list -> t
(** [restrict expr constraints] simplifies [expr] by assuming the specified
    constraints hold. Supports Boolean, String, and Version constraints.

    Example:
    [let s = restrict expr [ Boolean (b1, true); String (s1, `Eq, "a") ]]

    Complexity: O(|expr|) *)

type constant_result = Constant of bool | NonConstant

val ite_constant : t -> t -> t -> constant_result
(** [ite_constant f g h] evaluates if the result of [ite f g h] is a constant
    boolean without fully constructing the BDD. Returns [Constant b] if the
    result corresponds to [b], or [NonConstant] otherwise. *)

val logical_implies : t -> t -> bool
(** [logical_implies a b] checks if [a] logically implies [b] (i.e., [a => b] is
    valid/tautology) without fully constructing the result. *)

val is_disjoint : t -> t -> bool
(** [is_disjoint a b] checks if [a] and [b] are disjoint (i.e., [a /\ b] is
    unsatisfiable) without fully constructing the result. *)

val is_exhaustive : t -> t -> bool
(** [is_exhaustive a b] checks if [a] and [b] cover the entire space (i.e.,
    [a \/ b] is a tautology) without fully constructing the result. *)

(** {1 Quantifiers} *)

val exists : 'a var -> t -> t
(** [exists v expr] eliminates variable [v] from [expr] by computing the
    disjunction over all possible values. For a boolean variable, this is
    equivalent to
    [restrict expr [Boolean(v, true)] || restrict expr [Boolean(v, false)]]. For
    string and version variables, it quantifies over all atoms mentioning [v].

    Example: [let expr' = exists b (and_ (atom b) (atom c))] (* Result: atom c
    *)

    Complexity: O(|expr|²) *)

val forall : 'a var -> t -> t
(** [forall v expr] eliminates variable [v] from [expr] by computing the
    conjunction over all possible values. For a boolean variable, this is
    equivalent to
    [restrict expr [Boolean(v, true)] && restrict expr [Boolean(v, false)]].

    Example: [let expr' = forall b (or_ (atom b) (atom c))] (* Result: atom c *)

    Complexity: O(|expr|²) *)

(** {1 Solving} *)

val sat : t -> atom_constraint list option
(** [sat expr] finds a satisfying set of constraints for [expr], if one exists.
    Returns [Some constraints] where [constraints] is a list of atomic
    constraints that make the expression true. Returns [None] if the expression
    is unsatisfiable (equivalent to [false_]). *)

val shortest_sat : t -> atom_constraint list option
(** [shortest_sat expr] finds a satisfying set of constraints with the minimum
    number of atomic constraints (shortest path in the BDD DAG). Returns [None]
    if unsatisfiable. *)

(** {1 Batch Operations} *)

val and_list : t list -> t
(** [and_list exprs] computes the conjunction of all expressions in [exprs].
    Returns [true_] for an empty list. More efficient than folding [and_]
    manually due to better cache utilization.

    Example: [let expr = and_list [e1; e2; e3]]

    Complexity: O(Σ|eᵢ|²) *)

val or_list : t list -> t
(** [or_list exprs] computes the disjunction of all expressions in [exprs].
    Returns [false_] for an empty list.

    Example: [let expr = or_list [e1; e2; e3]]

    Complexity: O(Σ|eᵢ|²) *)

(** {1 Debugging} *)

val to_string : t -> string
(** [to_string expr] returns a human-readable representation of the BDD
    structure. Shows the decision tree with atoms and branches. *)

val print_dot : out_channel -> t -> unit
(** [print_dot chan expr] prints the BDD in Graphviz DOT format to the given
    channel. *)
