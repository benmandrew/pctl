let matrix states inconclusive_states =
  let f i j =
    if Int_map.mem i inconclusive_states then
      let s = Int_map.find i states in
      Int_map.find j s.Model.State.t
    else if i = j then 1.0
    else 0.0
  in
  let n = Int_map.cardinal states in
  Array.init n (fun i -> Array.init n (fun j -> f i j))

let state_inconclusive labels i f f' =
  Formula.f_in_state_labels labels i f
  && not (Formula.f_in_state_labels labels i f')

let mu_measure_until (states : Model.State.map) labels i f f' =
  let inconclusive_states, _ =
    Int_map.partition (fun i _ -> state_inconclusive labels i f f') states
  in
  ()
