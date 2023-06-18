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

let merge_labels _ s s' =
  match (s, s') with
  | None, None -> None
  | s, s' ->
      let s = Option.value s ~default:Formula.Set.empty in
      let s' = Option.value s' ~default:Formula.Set.empty in
      Some (Formula.Set.union s s')

(** Bottom-to-top traversal of the formula tree [f],
    repeatedly adding subformulae to [labels] for all states *)
let rec label states labels f =
  match f with
  | Formula.Prop _ -> labels
  | _ ->
      let pred labels =
        match f with
        | Formula.Prop _ -> fun _ -> false
        | Neg f ->
            let labels = label states labels f in
            fun i -> not (Formula.f_in_state_labels labels i f)
        | Or (f, f') ->
            let labels =
              Int_map.merge merge_labels (label states labels f)
                (label states labels f')
            in
            fun i ->
              Formula.f_in_state_labels labels i f
              || Formula.f_in_state_labels labels i f'
        | And (f, f') ->
            let labels =
              Int_map.merge merge_labels (label states labels f)
                (label states labels f')
            in
            fun i ->
              Formula.f_in_state_labels labels i f
              && Formula.f_in_state_labels labels i f'
        | Impl (f, f') ->
            let labels =
              Int_map.merge merge_labels (label states labels f)
                (label states labels f')
            in
            fun i ->
              (not (Formula.f_in_state_labels labels i f))
              || Formula.f_in_state_labels labels i f'
        | P (op, p, path_f) -> (
            match path_f with
            | U (t, f, f') ->
                let labels =
                  Int_map.merge merge_labels (label states labels f)
                    (label states labels f')
                in
                let b = Modal.until states labels ~t ~p ~op f f' in
                fun i -> b.(i)
            | W (t, f, f') ->
                let labels =
                  Int_map.merge merge_labels (label states labels f)
                    (label states labels f')
                in
                ignore t;
                ignore labels;
                fun _ -> false)
      in
      Int_map.fold
        (fun i _ labels ->
          if pred labels i then add_f_to_state labels i f else labels)
        states labels

let v k f =
  let states = k.Model.Kripke.states in
  let starting_labels = label_init states in
  let labels = label states starting_labels f in
  let labels_for_state = Int_map.find k.Model.Kripke.initial labels in
  Formula.Set.mem f labels_for_state
