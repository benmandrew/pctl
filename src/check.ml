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

module Label = struct
  let rec v_neg states labels f =
    let labels = v_state states labels f in
    fun i -> not (Formula.f_in_state_labels labels i f)

  and v_or states labels f f' =
    let labels =
      Int_map.merge merge_labels (v_state states labels f)
        (v_state states labels f')
    in
    fun i ->
      Formula.f_in_state_labels labels i f
      || Formula.f_in_state_labels labels i f'

  and v_and states labels f f' =
    let labels =
      Int_map.merge merge_labels (v_state states labels f)
        (v_state states labels f')
    in
    fun i ->
      Formula.f_in_state_labels labels i f
      && Formula.f_in_state_labels labels i f'

  and v_impl states labels f f' =
    let labels =
      Int_map.merge merge_labels (v_state states labels f)
        (v_state states labels f')
    in
    fun i ->
      (not (Formula.f_in_state_labels labels i f))
      || Formula.f_in_state_labels labels i f'

  and v_forall states labels f = v_path states labels ~p:1.0 ~op:Formula.Geq f
  and v_exists states labels f = v_path states labels ~p:0.0 ~op:Formula.Gt f

  and v_strong_until states labels ~t ~p ~op f f' =
    let labels =
      Int_map.merge merge_labels (v_state states labels f)
        (v_state states labels f')
    in
    let b = Modal.strong_until states labels ~t ~p ~op f f' in
    fun i -> b.(i)

  and v_weak_until states labels ~t ~p ~op f f' =
    let p = 1.0 -. p in
    let op = match op with Formula.Geq -> Formula.Gt | Gt -> Geq in
    fun i ->
      not
        (v_strong_until states labels ~t ~p ~op (Neg f')
           (And (Neg f, Neg f'))
           i)

  and v_generally states labels ~t ~p ~op f =
    v_weak_until states labels ~t ~p ~op f (Formula.Bool false)

  and v_finally states labels ~t ~p ~op f =
    v_strong_until states labels ~t ~p ~op (Formula.Bool true) f

  and v_leads_to states labels ~t ~p ~op f f' =
    let f =
      Formula.(Generally (Infinity, Impl (f, P (op, p, Finally (t, f')))))
    in
    v_forall states labels f

  (** Bottom-to-top traversal of the formula tree [f],
      repeatedly adding subformulae to [labels] for all states *)
  and v_state states labels f =
    let pred labels =
      match f with
      | Formula.Bool b -> fun _ -> b
      | Prop _ -> fun _ -> false
      | Neg f -> v_neg states labels f
      | Or (f, f') -> v_or states labels f f'
      | And (f, f') -> v_and states labels f f'
      | Impl (f, f') -> v_impl states labels f f'
      | A f -> v_path states labels ~p:1.0 ~op:Formula.Geq f
      | E f -> v_path states labels ~p:0.0 ~op:Formula.Gt f
      | P (op, p, f) -> v_path states labels ~p ~op f
    in
    Int_map.fold
      (fun i _ labels ->
        if pred labels i then add_f_to_state labels i f else labels)
      states labels

  and v_path states labels ~p ~op = function
    | Formula.Strong_until (t, f, f') ->
        v_strong_until states labels ~t ~p ~op f f'
    | Weak_until (t, f, f') -> v_weak_until states labels ~t ~p ~op f f'
    | Generally (t, f) -> v_generally states labels ~t ~p ~op f
    | Finally (t, f) -> v_finally states labels ~t ~p ~op f
    | Leads_to (t, f, f') -> v_leads_to states labels ~t ~p ~op f f'

  let v = v_state
end

let v k f =
  let states = k.Model.Kripke.states in
  let starting_labels = label_init states in
  let labels = Label.v states starting_labels f in
  let labels_for_state = Int_map.find k.Model.Kripke.initial labels in
  Formula.Set.mem f labels_for_state
