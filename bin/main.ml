open Pctl

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

let f_in_state_labels labels i f = Int_map.find i labels |> Pctl_set.mem f

(* Add formula [f] to the set of labels for the state with index [i] *)
let add_f_to_state labels i f =
  let s = Pctl_set.add f (Int_map.find i labels) in
  Int_map.add i s labels

(** Bottom-to-top traversal of the formula tree [f],
    repeatedly adding subformulae to [labels] *)
let rec label states labels f =
  match f with
  | Pctl.Prop _ -> labels
  | _ ->
      let labels = label states labels f in
      let pred labels i =
        match f with
        | Pctl.Prop _ -> false
        | Neg f -> not (f_in_state_labels labels i f)
        | Or (f, f') ->
            f_in_state_labels labels i f || f_in_state_labels labels i f'
        | And (f, f') ->
            f_in_state_labels labels i f && f_in_state_labels labels i f'
        | Impl (f, f') ->
            (not (f_in_state_labels labels i f))
            || f_in_state_labels labels i f'
        | Pgeq (_, _) -> false
      in
      Int_map.fold
        (fun i _ labels ->
          if pred labels i then add_f_to_state labels i f else labels)
        states labels
