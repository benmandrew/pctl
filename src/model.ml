(** Atomic propositions *)
module Aprop = struct
  type m = Green | Red | Amber [@@deriving compare]

  module Set = Set.Make (struct
    type t = m

    let compare = compare_m
  end)

  type t = m [@@deriving compare]
end

module Int_map = Map.Make (Int)

(** States in a temporal model *)
module State = struct
  type t = { t : (int * float) list; l : Aprop.Set.t }
  (** [id] is the state's unique identifier.
      [t] is list of transitions out of this state,
        where for a given [(s', p)] s' is the
        destination state and p is the probability
        of taking that transition. The transition
        probabilities for a state must sum to 1.
      [l] is the set of labels that hold in the state. *)

  let prop_holds t ap = Aprop.Set.mem ap t.l

  type map = t Int_map.t
end
