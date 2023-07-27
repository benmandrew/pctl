module Aprop : sig
  type t = Ap.m

  val pp : Format.formatter -> t -> unit
  val compare : t -> t -> int

  module Set : Set.S with type elt := t with type t := Ap.Set.t
end

module State : sig
  type t = { t : float Int_map.t; l : Ap.Set.t }

  val prop_holds : t -> Ap.m -> bool
  val v_list : (int * float) list -> Ap.m list -> t
end

module Kripke : sig
  type t = { states : State.t Int_map.t; initial : int }

  val v : int -> State.t Int_map.t -> t
  val v_list : int -> (int * State.t) list -> t
  val prop_holds_in_state : t -> int -> Ap.m -> bool
end
