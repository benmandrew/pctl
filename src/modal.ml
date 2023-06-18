let matrix n states inconclusive_states =
  let f i j =
    if Int_map.mem i inconclusive_states then
      let s = Int_map.find i states in
      Int_map.find j s.Model.State.t
    else if i = j then 1.0
    else 0.0
  in
  Array.init n (fun i -> Array.init n (fun j -> f i j))

let state_inconclusive labels i f f' =
  Formula.f_in_state_labels labels i f
  && not (Formula.f_in_state_labels labels i f')

let matrix_mul =
  Array.(map2 (fun row e -> fold_left (fun e' acc -> (e *. e') +. acc) e row))

let mu_measure_until (states : Model.State.t Int_map.t) labels t f f' =
  let inconclusive_states, _ =
    Int_map.partition (fun i _ -> state_inconclusive labels i f f') states
  in
  let n = Int_map.cardinal states in
  let m = matrix n states inconclusive_states in
  let v =
    Array.init n (fun i ->
        if Formula.f_in_state_labels labels i f' then 1.0 else 0.0)
  in
  let rec f acc = function 0 -> acc | n -> f (matrix_mul m acc) (n - 1) in
  f v t

let until states labels ~t ~p ~op f f' =
  let probabilities = mu_measure_until states labels t f f' in
  Array.map (fun p' -> Formula.compare_probability op p p') probabilities
