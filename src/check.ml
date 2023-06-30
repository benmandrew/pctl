let label_init states =
  let init_props s =
    Model.Aprop.Set.fold
      (fun p f -> Formula.Set.add (Formula.Prop p) f)
      s.Model.State.l
      (Formula.Set.singleton (Formula.Bool true))
  in
  let add_state i s labels =
    let l = init_props s in
    Int_map.add i l labels
  in
  Int_map.fold add_state states Int_map.empty

(** Add formula [f] to the set of labels for the state with index [i] *)
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
  let add_on_condition labels f cond =
    Int_map.mapi
      (fun i s_labels ->
        if cond i then Formula.Set.add f s_labels else s_labels)
      labels

  let rec v_neg states labels f =
    let labels = v_state states labels f in
    let cond i = not (Formula.f_in_state_labels labels i f) in
    add_on_condition labels (Formula.Neg f) cond

  and v_or states labels f f' =
    let labels =
      Int_map.merge merge_labels (v_state states labels f)
        (v_state states labels f')
    in
    let cond i =
      Formula.f_in_state_labels labels i f
      || Formula.f_in_state_labels labels i f'
    in
    add_on_condition labels (Formula.Or (f, f')) cond

  and v_and states labels f f' =
    let labels =
      Int_map.merge merge_labels (v_state states labels f)
        (v_state states labels f')
    in
    let cond i =
      Formula.f_in_state_labels labels i f
      && Formula.f_in_state_labels labels i f'
    in
    add_on_condition labels (Formula.And (f, f')) cond

  and v_impl states labels f f' =
    let labels =
      Int_map.merge merge_labels (v_state states labels f)
        (v_state states labels f')
    in
    let cond i =
      (not (Formula.f_in_state_labels labels i f))
      || Formula.f_in_state_labels labels i f'
    in
    add_on_condition labels (Formula.Impl (f, f')) cond

  and v_forall states labels f =
    Formula.(v_path states labels ~p:(Pr 1.0) ~op:Geq f)

  and v_exists states labels f =
    Formula.(v_path states labels ~p:(Pr 0.0) ~op:Gt f)

  and v_strong_until states labels ~t ~p ~op f f' =
    let labels =
      Int_map.merge merge_labels (v_state states labels f)
        (v_state states labels f')
    in
    Modal.strong_until states labels ~t ~p ~op f f'

  and v_weak_until states labels ~t ~p ~op f f' =
    let p =
      match p with
      | Formula.Pr p -> Formula.Pr (1.0 -. p)
      | One -> Zero
      | Zero -> One
    in
    let op = match op with Formula.Geq -> Formula.Gt | Gt -> Geq in
    v_strong_until states labels ~t ~p ~op (Neg f') (And (Neg f, Neg f'))

  and v_generally states labels ~t ~p ~op f =
    v_weak_until states labels ~t ~p ~op f (Formula.Bool false)

  and v_finally states labels ~t ~p ~op f =
    v_strong_until states labels ~t ~p ~op (Formula.Bool true) f

  and v_leads_to states labels ~t ~p ~op f f' =
    let f =
      Formula.(Generally (Infinity, Impl (f, P (op, p, Finally (t, f')))))
    in
    v_forall states labels f

  (** [v_state states labels f] is a bottom-to-top traversal of the formula tree [f],
      repeatedly adding subformulae to [labels] for all [states] *)
  and v_state states labels = function
    | Formula.Bool _ -> labels
    | Prop _ -> labels
    | Neg f -> v_neg states labels f
    | Or (f, f') -> v_or states labels f f'
    | And (f, f') -> v_and states labels f f'
    | Impl (f, f') -> v_impl states labels f f'
    | A f -> v_path states labels ~p:One ~op:Geq f
    | E f -> v_path states labels ~p:Zero ~op:Gt f
    | P (op, p, f) -> v_path states labels ~p ~op f

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
