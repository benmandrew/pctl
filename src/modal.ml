let matrix n states inconclusive_states =
  let f i j =
    if Int_map.mem i inconclusive_states then
      let s = Int_map.find i states in
      Int_map.find_opt j s.Model.State.t |> Option.value ~default:0.0
    else if i = j then 1.0
    else 0.0
  in
  Linalg.Mat.init n f

let state_inconclusive labels i f f' =
  Formula.(f_in_state_labels labels i f && not (f_in_state_labels labels i f'))

(** [partition states labels f f'] returns the set of [states] partitioned into three maps [(s_s, s_f, s_i)]. 
    - [s_s] is the set of success states, where for a given state [f'] is in the set of labels
    - [s_f] is the set of failure states, where for a given state neither [f] nor [f'] are in the set of labels
    - [s_i] is the set of inconclusive states, where for a given state [f] is in the set of labels but [f'] is not *)
let partition_states states labels f f' =
  let f i _ (s_s, s_f, s_i) =
    if Formula.f_in_state_labels labels i f' then (Int_set.add i s_s, s_f, s_i)
    else if
      Formula.(
        (not (f_in_state_labels labels i f))
        && not (f_in_state_labels labels i f'))
    then (s_s, Int_set.add i s_f, s_i)
    else (s_s, s_f, Int_set.add i s_i)
  in
  Int_map.fold f states Int_set.(empty, empty, empty)

let matrix_mul m v =
  let open Array in
  let product v0 v1 =
    map2 (fun a b -> a *. b) v0 v1 |> fold_left (fun acc a -> acc +. a) 0.0
  in
  mapi (fun i _ -> product v m.(i)) v

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

(** {m \{ s : s \in unseen \wedge (\exists s' \in fringe : T(s,s') > 0) \} } *)
let get_next_fringe states unseen next_states_condition =
  let add_s_conditional i acc =
    let next_states =
      let transitions = (Int_map.find i states).Model.State.t in
      let possible_transitions =
        Int_map.filter (fun _ p -> Float.compare p 0.0 > 0) transitions
      in
      Int_map.fold
        (fun i _ prev_states -> Int_set.add i prev_states)
        possible_transitions Int_set.empty
    in
    if next_states_condition next_states then Int_set.add i acc else acc
  in
  Int_set.fold add_s_conditional unseen Int_set.empty

let strong_until_f ~t ~p ~op f f' = Formula.(P (op, p, Strong_until (t, f, f')))

(** [label_states labels states f] labels all states in [states] with [f],
    adding to the existing [labels] *)
let label_states labels states f =
  let f i labels =
    let formulae = Int_map.find i labels |> Formula.Set.add f in
    Int_map.add i formulae labels
  in
  Int_set.fold f states labels

(** [label_all_conditional labels ~p ~op f probabilities] labels states
    indexed by [i] with [f] if [probabilities.(i) op p], adding to the
    existing [labels] *)
let label_all_conditional labels ~p ~op f probabilities =
  Int_map.mapi
    (fun i s ->
      let p' = probabilities.(i) in
      if Formula.compare_prob_with_op op p' p then Formula.Set.add f s else s)
    labels

(** [filter_eu states labels ~t f f'] returns states which would be
    labelled for the case of the until operator {m f U^{\geq t}_{>0} f'} *)
let filter_eu states labels ~t f f' =
  let rec aux acc unseen fringe = function
    | 0 -> acc
    | n ->
        (* {m unseen := unseen - fringe} *)
        let unseen = Int_set.diff unseen fringe in
        (* {m fringe := \{ s : (s \in unseen \wedge \exists s' \in fringe : (T(s,s') > 0)) \}} *)
        let fringe =
          get_next_fringe states unseen
            (Int_set.exists (fun i -> Int_set.mem i fringe))
        in
        aux (Int_set.union acc fringe) unseen fringe (n - 1)
  in
  let fringe, _, unseen = partition_states states labels f f' in
  let mr = Int.min (Int_set.cardinal unseen) t in
  aux fringe unseen fringe mr

(** [filter_au states labels ~t f f'] returns states which would be
    labelled for the case of the until operator {m f U^{\geq t}_{\geq 1} f'} *)
let filter_au states labels ~t f f' =
  let rec aux acc unseen fringe seen = function
    | 0 -> acc
    | n ->
        (* {m unseen := unseen - fringe} *)
        let unseen = Int_set.diff unseen fringe in
        (* {m seen := seen \cup fringe} *)
        let seen = Int_set.union seen fringe in
        (* {m fringe := \{ s : (s \in unseen \wedge \forall s' \in seen : (T(s,s') > 0)) \}} *)
        let fringe =
          get_next_fringe states unseen
            (Int_set.for_all (fun i -> Int_set.mem i seen))
        in
        aux (Int_set.union acc fringe) unseen fringe seen (n - 1)
  in
  let fringe, _, unseen = partition_states states labels f f' in
  let seen = Int_set.empty in
  let mr = Int.min (Int_set.cardinal unseen) t in
  aux fringe unseen fringe seen mr

(** [label_eu states labels ~t f f'] labels states for the case of the
    until operator {m f U^{\geq t}_{>0} f'} *)
let label_eu states labels ~t f f' =
  let f_main = strong_until_f ~t:(T t) ~p:Zero ~op:Gt f f' in
  let s = filter_eu states labels ~t f f' in
  label_states labels s f_main

(** [label_au states labels ~t f f'] labels states for the case of the
    until operator {m f U^{\geq t}_{\geq 1} f'} *)
let label_au states labels ~t f f' =
  let f_main = strong_until_f ~t:(T t) ~p:One ~op:Geq f f' in
  let s = filter_au states labels ~t f f' in
  label_states labels s f_main

(** [gaussian_matrix n r q states] creates the system of linear equations defined by:

    {math P(\infty, s) = \begin{align*}
      \text{if } s \in R \text{ then } 1 \\
      \text{else if } s \in Q \text{ then } 0 \\
      \text{else } \sum_{s' \in S} T(s, s') \cdot P(\infty, s')
    \end{align*} } *)
let infinite_fixpoint_linear_eqs r unknown_states states =
  let n = Int_set.cardinal unknown_states in
  let f_mat i j =
    let s = Int_map.find i states in
    let v = Model.State.t_prob s j in
    if i = j then 1.0 -. v else v
  in
  let f_vec i =
    Int_set.fold
      (fun r acc ->
        let s = Int_map.find i states in
        acc +. Model.State.t_prob s r)
      r 0.0
  in
  Linalg.(Mat.init n f_mat, Vec.init n f_vec)

let get_unknown_probabilities states success_states failure_states =
  let all_states =
    Int_map.fold (fun i _ indices -> Int_set.add i indices) states Int_set.empty
  in
  let unknown_states, n_unknown =
    let u_s =
      Int_set.diff (Int_set.diff all_states success_states) failure_states
    in
    (u_s, Int_set.cardinal u_s)
  in
  let state_to_vec_index =
    Int_set.fold
      (fun i (i', indices) ->
        if Int_set.mem i unknown_states then (i' + 1, Int_map.add i i' indices)
        else (i', indices))
      all_states (0, Int_map.empty)
    |> snd
  in
  let m, v =
    infinite_fixpoint_linear_eqs success_states unknown_states states
  in
  let m' = Linalg.gaussian_elim n_unknown m in
  let unknown_probabilities = Linalg.back_substitute n_unknown m' v in
  fun i ->
    let i' = Int_map.find i state_to_vec_index in
    unknown_probabilities.(i')

let mu_measure_until_infinite states labels f f' =
  let s_s, s_f, s_i = partition_states states labels f f' in
  let t = Int_set.cardinal s_i in
  let failure_states =
    let unreachable = Int_set.diff s_i (filter_eu states labels ~t f f') in
    Int_set.union s_f unreachable
  in
  let success_states =
    let guaranteed = filter_au states labels ~t f f' in
    Int_set.union s_s guaranteed
  in
  let n = Int_map.cardinal states in
  let unknown_probabilities =
    get_unknown_probabilities states success_states failure_states
  in
  Array.init n (fun i ->
      if Int_set.mem i success_states then 1.0
      else if Int_set.mem i failure_states then 0.0
      else unknown_probabilities i)

let strong_until states labels ~t ~p ~op f f' =
  match (t, p, op) with
  | Formula.T t, Formula.Zero, Formula.Gt -> label_eu states labels ~t f f'
  | Infinity, Zero, Gt ->
      let n_inconclusive =
        let _, _, unseen = partition_states states labels f f' in
        Int_set.cardinal unseen
      in
      label_eu states labels ~t:n_inconclusive f f'
  | T t, One, Geq -> label_au states labels ~t f f'
  | Infinity, One, Geq ->
      let n_inconclusive =
        let _, _, unseen = partition_states states labels f f' in
        Int_set.cardinal unseen
      in
      label_au states labels ~t:n_inconclusive f f'
  | T t, Pr p, _ ->
      let f_main = Formula.(P (op, Pr p, Strong_until (T t, f, f'))) in
      let probabilities = mu_measure_until states labels t f f' in
      label_all_conditional labels ~p ~op f_main probabilities
  | _, One, Gt -> labels
  | t, Zero, Geq ->
      let state_ids =
        Int_map.bindings states |> List.map fst |> Int_set.of_list
      in
      label_states labels state_ids (strong_until_f ~t ~p ~op f f')
  | Infinity, Pr p, _ ->
      let f_main = Formula.(P (op, Pr p, Strong_until (Infinity, f, f'))) in
      let probabilities = mu_measure_until_infinite states labels f f' in
      label_all_conditional labels ~p ~op f_main probabilities
