(** Comparison operators for the PCTL [P] operator *)
type comparison = Geq | Gt

(** Probabilities for the PCTL [P] operator *)
type prob = One | Pr of float | Zero

val compare_prob_with_op : comparison -> float -> float -> bool
(** [compare_prob_with_op op p p'] compares [p] and [p'] according to the formed expression [p op p'] *)

(** Discrete time-steps for PCTL path operators *)
type time = T of int | Infinity

(** PCTL state formulae *)
type s =
  | Bool of bool
  | Prop of string
  | Neg of s
  | Or of s * s
  | And of s * s
  | Impl of s * s
  | P of comparison * prob * p
  | A of p
  | E of p

(** PCTL path formulae *)
and p =
  | Strong_until of time * s * s
  | Weak_until of time * s * s
  | Generally of time * s
  | Finally of time * s
  | Leads_to of time * s * s

type t = s
(** Top-level PCTL formulae must be state formulae *)

val canonicalise : t -> t
(** Convert PCTL formulae to (somewhat) canonical form, used for comparisons *)

val compare : t -> t -> int

module Set : Set.S with type elt := t

val f_in_state_labels : Set.t Int_map.t -> int -> t -> bool
(** [f_in_state_labels s i f] holds if [f] is in the set of labels for state [i] *)

val print_state_labels : Set.t Int_map.t -> unit
