(** Atomic propositions *)
module Aprop = struct
  type t = Green | Red | Amber [@@deriving compare]
end

module Aprop_set = Set.Make (Aprop)
module Int_map = Map.Make (Int)

(** States in a temporal model *)
module State = struct
  type t = { t : (int * float) list; l : Aprop_set.t }
  (** [id] is the state's unique identifier.
      [t] is list of transitions out of this state,
        where for a given [(s', p)] s' is the
        destination state and p is the probability
        of taking that transition. The transition
        probabilities for a state must sum to 1.
      [l] is the set of labels that hold in the state. *)

  let prop_holds t ap = Aprop_set.mem ap t.l

  type map = t Int_map.t
end

(** PCTL state and path formulae *)
module Pctl = struct
  type comparison = Geq | Gt [@@deriving compare]

  (* To satisfy the [compare] PPX below *)
  let compare_float = Float.compare

  (** State formulae *)
  type s =
    | Prop of Aprop.t
    | Neg of s
    | Or of s * s
    | And of s * s
    | Impl of s * s
    | Pgeq of float * p
  [@@deriving compare]

  (** Path formulae *)
  and p = U of comparison * float * s * s | W of comparison * float * s * s
  [@@deriving compare]

  type t = s [@@deriving compare]
  (** Top-level PCTL formulae must be state formulae *)
end

module Pctl_set = Set.Make (Pctl)
