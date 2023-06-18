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

  let prop_holds t ap =
    Aprop_set.find_opt ap t.l |> function Some _ -> true | None -> false

  type map = t Int_map.t
end

(** PCTL state and path formulae *)
module Pctl = struct
  type comparison = Leq [@@deriving compare]

  (* To satisfy the [compare] PPX below *)
  let compare_float = Float.compare

  type s =
    | Prop of Aprop.t
    | Neg of s
    | Or of s * s
    | And of s * s
    | Impl of s * s
    | Pgeq of float * p
  [@@deriving compare]

  and p = U of comparison * float * s * s | W of comparison * float * s * s
  [@@deriving compare]

  (* Top-level PCTL formulae must be state formulae *)
  type t = s [@@deriving compare]
end

module Pctl_set = Set.Make (Pctl)

(* module Kripke = struct
     type t = { states : State.map; initial : int }

     let v initial (states : State.map) =
       assert (Int_map.exists (fun id _ -> id = initial) states);
       (* assert (List.exists (fun s -> s.State.id = initial) states); *)
       { initial; states }

     let prop_holds_in_state k s ap =
       match Int_map.find_opt s k.states with
       | Some s -> State.prop_holds s ap
       | None -> false
   end *)

let label_init states =
  let init_props s =
    Aprop_set.fold
      (fun p f -> Pctl_set.add (Pctl.Prop p) f)
      s.State.l Pctl_set.empty
  in
  let add_state i s labels =
    let l = init_props s in
    Int_map.add i l labels
  in
  Int_map.fold add_state states Int_map.empty
