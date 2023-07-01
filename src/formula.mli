
(** Comparison operators for the PCTL [P] operator *)
type comparison = Geq | Gt

(** Probabilities for the PCTL [P] operator *)
type prob = One | Pr of float | Zero

(** [compare_prob_with_op op p p'] compares [p] and [p'] according to the formed expression [p op p'] *)
val compare_prob_with_op : comparison -> float -> float -> bool

(** Discrete time-steps for PCTL path operators *)
type time = T of int | Infinity

(** PCTL state formulae *)
type s =
  | Bool of bool
  | Prop of Ap.m
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

(** Top-level PCTL formulae must be state formulae *)
type t = s

(** Convert PCTL formulae to (somewhat) canonical form, used for comparisons *)
val canonicalise : t -> t
val compare : t -> t -> int

module Set : Set.S with type elt := t

(** [f_in_state_labels s i f] holds if [f] is in the set of labels for state [i] *)
val f_in_state_labels : Set.t Int_map.t -> int -> t -> bool
val print_state_labels : Set.t Int_map.t -> unit
