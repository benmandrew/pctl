module type MODAL = functor (M : Model.MODEL) (F : Formula.FORMULA) -> sig

  val strong_until : M.State.t Int_map.t -> F(M.Aprop).Set.t Int_map.t -> t:F(M.Aprop).inf_nat -> p:float -> op:F(M.Aprop).comparison -> F(M.Aprop).t -> F(M.Aprop).t -> bool array
end

module Make (M : Model.MODEL) (F : Formula.FORMULA) = struct
  module F = F (M.Aprop)

  let matrix n states inconclusive_states =
    let f i j =
      if Int_map.mem i inconclusive_states then
        let s = Int_map.find i states in
        Int_map.find_opt j s.Model.State.t |> Option.value ~default:0.0
      else if i = j then 1.0
      else 0.0
    in
    Array.init n (fun i -> Array.init n (fun j -> f i j))

  let state_inconclusive labels i f f' =
    F.f_in_state_labels labels i f
    && not (F.f_in_state_labels labels i f')

  let matrix_mul =
    Array.(map2 (fun row e -> fold_left (fun e' acc -> (e *. e') +. acc) 0.0 row))

  let print_vector r =
    Array.iter (Printf.printf "%4.2f ") r;
    Printf.printf "\n"

  let print_matrix = Array.iter print_vector

  let mu_measure_until (states : Model.State.t Int_map.t) labels t f f' =
    let inconclusive_states, _ =
      Int_map.partition (fun i _ -> state_inconclusive labels i f f') states
    in
    let n = Int_map.cardinal states in
    let m = matrix n states inconclusive_states in
    let v =
      Array.init n (fun i ->
          if F.f_in_state_labels labels i f' then 1.0 else 0.0)
    in
    let rec f acc = function 0 -> acc | n -> f (matrix_mul m acc) (n - 1) in
    f v t

  let strong_until states labels ~t ~p ~op f f' =
    match t with
    | F.Infinity -> raise Exit
    | N t ->
        let probabilities = mu_measure_until states labels t f f' in
        Array.map (fun p' -> F.compare_probability op p' p) probabilities
end