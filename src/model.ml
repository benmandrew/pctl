module type APROP = sig
  type t

  val pp : Format.formatter -> t -> unit
  val compare : t -> t -> int

  module Set : Set.S
end

module Make (Aprop : APROP) = struct
  module Aprop = Aprop

  (** States in a temporal model *)
  module State = struct
    type t = { t : float Int_map.t; l : Aprop.Set.t }
    (** [id] is the state's unique identifier.
        [t] is list of transitions out of this state,
          where for a given [(s', p)] s' is the
          destination state and p is the probability
          of taking that transition. The transition
          probabilities for a state must sum to 1.
        [l] is the set of labels that hold in the state. *)

    let prop_holds t ap = Aprop.Set.mem ap t.l
    let t_prob t j = Int_map.find_opt j t.t |> Option.value ~default:0.0

    let v_list t l =
      let t = Int_map.of_seq @@ List.to_seq t in
      let l = Aprop.Set.of_list l in
      { t; l }
  end

  module Kripke = struct
    type t = { states : State.t Int_map.t; initial : int }

    let v initial states =
      assert (Int_map.exists (fun id _ -> id = initial) states);
      { initial; states }

    let v_list initial states =
      let states = Int_map.of_seq @@ List.to_seq states in
      v initial states

    let prop_holds_in_state k s ap =
      match Int_map.find_opt s k.states with
      | Some s -> State.prop_holds s ap
      | None -> false

    let t_prob t i j = State.t_prob (Int_map.find i t.states) j
    let states t = t.states

    let indices t =
      Int_map.fold
        (fun i _ indices -> Int_set.add i indices)
        t.states Int_set.empty
  end
end

include Make (Ap)
