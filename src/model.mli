module State : sig
  type t = { t : float Int_map.t; l : Str_set.t }

  val prop_holds : t -> string -> bool
  val t_prob : t -> int -> float
  val v_list : (int * float) list -> string list -> t
end

module Kripke : sig
  type t = { states : State.t Int_map.t; initial : int }

  val v : int -> State.t Int_map.t -> t
  val v_list : int -> (int * State.t) list -> t
  val prop_holds_in_state : t -> int -> string -> bool
  val t_prob : t -> int -> int -> float
  val states : t -> State.t Int_map.t
  val indices : t -> Int_set.t
end
