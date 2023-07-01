val label_init : Model.State.t Int_map.t -> Formula.Set.t Int_map.t

val add_f_to_state :
  Formula.Set.t Int_map.t -> int -> Formula.s -> Formula.Set.t Int_map.t

val v : Model.Kripke.t -> Formula.s -> bool
