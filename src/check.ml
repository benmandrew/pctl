module Int_map = Map.Make (Int)

let label_init states =
  let init_props s =
    Model.Aprop.Set.fold
      (fun p f -> Formula.Set.add (Formula.Prop p) f)
      s.Model.State.l Formula.Set.empty
  in
  let add_state i s labels =
    let l = init_props s in
    Int_map.add i l labels
  in
  Int_map.fold add_state states Int_map.empty

(* Add formula [f] to the set of labels for the state with index [i] *)
let add_f_to_state labels i f =
  let s = Formula.Set.add f (Int_map.find i labels) in
  Int_map.add i s labels

(** Bottom-to-top traversal of the formula tree [f],
    repeatedly adding subformulae to [labels] *)
let rec label states labels f =
  match f with
  | Formula.Prop _ -> labels
  | _ ->
      let labels = label states labels f in
      let pred labels i =
        match f with
        | Formula.Prop _ -> false
        | Neg f -> not (Formula.f_in_state_labels labels i f)
        | Or (f, f') ->
            Formula.f_in_state_labels labels i f
            || Formula.f_in_state_labels labels i f'
        | And (f, f') ->
            Formula.f_in_state_labels labels i f
            && Formula.f_in_state_labels labels i f'
        | Impl (f, f') ->
            (not (Formula.f_in_state_labels labels i f))
            || Formula.f_in_state_labels labels i f'
        | Pgeq (_, _) -> false
      in
      Int_map.fold
        (fun i _ labels ->
          if pred labels i then add_f_to_state labels i f else labels)
        states labels
