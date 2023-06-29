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
  Formula.(f_in_state_labels labels i f && not (f_in_state_labels labels i f'))

(** [partition states labels f f'] returns the set of [states] partitioned into three maps [(s_s, s_f, s_i)]. 
    - [s_s] is the set of success states, where for a given state [f'] is in the set of labels
    - [s_f] is the set of failure states, where for a given state neither [f] nor [f'] are in the set of labels
    - [s_i] is the set of inconclusive states, where for a given state [f] is in the set of labels but [f'] is not *)
let partition_states states labels f f' =
  let f i s (s_s, s_f, s_i) =
    if Formula.f_in_state_labels labels i f' then (Int_map.add i s s_s, s_f, s_i)
    else if
      Formula.(
        (not (f_in_state_labels labels i f))
        && not (f_in_state_labels labels i f))
    then (s_s, Int_map.add i s s_f, s_i)
    else (s_s, s_f, Int_map.add i s s_i)
  in
  Int_map.fold f states Int_map.(empty, empty, empty)

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
        if Formula.f_in_state_labels labels i f' then 1.0 else 0.0)
  in
  let rec f acc = function 0 -> acc | n -> f (matrix_mul m acc) (n - 1) in
  f v t

module Int_set = Set.Make (Int)

let get_next_fringe unseen next_states_condition =
  let add_s_conditional i s acc =
    let next_states =
      let possible_transitions =
        Int_map.filter (fun _ p -> Float.compare p 0.0 > 0) s.Model.State.t
      in
      Int_map.fold
        (fun i _ prev_states -> Int_set.add i prev_states)
        possible_transitions Int_set.empty
    in
    if next_states_condition next_states then Int_set.add i acc else acc
  in
  Int_map.fold add_s_conditional unseen Int_set.empty

(** [label_eu states labels ~t f f'] labels states for the case of the until operator {m f U^{\geq t}_{>0} f'} *)
let label_eu states labels ~t f f' =
  let rec aux labels unseen fringe = function
    | 0 -> labels
    | n ->
        (* {m \forall x \in fringe do addlabel(s,f)} *)
        let labels =
          Int_map.fold
            (fun i _ labels ->
              let s = Formula.Set.add f (Int_map.find i labels) in
              Int_map.add i s labels)
            fringe labels
        in
        (* {m unseen := unseen - fringe} *)
        let unseen = Int_map.key_difference unseen fringe in
        (* {m fringe := \{ s : (s \in unseen \wedge \exists s' \in fringe : (T(s,s') > 0)) \}} *)
        let fringe =
          let next_fringe =
            get_next_fringe unseen
              (Int_set.exists (fun i -> Int_map.mem i fringe))
          in
          Int_set.fold
            (fun i m -> Int_map.(add i (find i unseen) m))
            next_fringe Int_map.empty
        in
        aux labels unseen fringe (n - 1)
  in
  let fringe, _, unseen = partition_states states labels f f' in
  let mr = Int.min (Int_map.cardinal unseen) t in
  aux labels unseen fringe mr

let label_au states labels ~t f f' =
  let rec aux labels unseen fringe seen = function
    | 0 -> labels
    | n ->
        let labels =
          Int_map.fold
            (fun i _ labels ->
              let s = Formula.Set.add f (Int_map.find i labels) in
              Int_map.add i s labels)
            fringe labels
        in
        let unseen = Int_map.key_difference unseen fringe in
        let seen =
          Int_map.union
            (fun i _ _ ->
              failwith
                (Printf.sprintf "State %d is in both [seen] and [fringe]" i))
            seen fringe
        in
        let fringe =
          let next_fringe =
            get_next_fringe unseen
              (Int_set.for_all (fun i -> Int_map.mem i seen))
          in
          Int_set.fold
            (fun i m -> Int_map.(add i (find i unseen) m))
            next_fringe Int_map.empty
        in
        aux labels unseen fringe seen (n - 1)
  in
  let fringe, _, unseen = partition_states states labels f f' in
  let seen = Int_map.empty in
  let mr = Int.min (Int_map.cardinal unseen) t in
  aux labels unseen fringe seen mr

let strong_until states labels ~t ~p ~op f f' =
  match (t, p, op) with
  | Formula.T t, Formula.Zero, Formula.Gt ->
      let n = Int_map.cardinal states in
      let labels = label_eu states labels ~t f f' in
      Array.init n (fun i -> Formula.f_in_state_labels labels i f')
  | Infinity, Zero, Gt ->
      let n_inconclusive =
        let _, _, unseen = partition_states states labels f f' in
        Int_map.cardinal unseen
      in
      let n = Int_map.cardinal states in
      let labels = label_eu states labels ~t:n_inconclusive f f' in
      Array.init n (fun i -> Formula.f_in_state_labels labels i f')
  | Infinity, Pr _, Geq -> raise Exit
  | T t, Pr p, _ ->
      let probabilities = mu_measure_until states labels t f f' in
      Array.map (fun p' -> Formula.compare_probability op p' p) probabilities
  | _, _, _ -> raise Exit
