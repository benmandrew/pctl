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

module Int_set = Set.Make (Int)

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

let add_labels labels fringe f =
  Int_set.fold
    (fun i labels ->
      let s = Formula.Set.add f (Int_map.find i labels) in
      Int_map.add i s labels)
    fringe labels

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

(** [label_eu states labels ~t f f'] labels states for the case of the until operator {m f U^{\geq t}_{>0} f'} *)
let label_eu states labels ~t f f' =
  let f_main = strong_until_f ~t:(T t) ~p:Zero ~op:Gt f f' in
  let rec aux labels unseen fringe = function
    | 0 ->
        (* {m \forall x \in fringe do addlabel(s,f_{main})} *)
        add_labels labels fringe f_main
    | n ->
        (* {m \forall x \in fringe do addlabel(s,f_{main})} *)
        let labels = add_labels labels fringe f_main in
        (* {m unseen := unseen - fringe} *)
        let unseen = Int_set.diff unseen fringe in
        (* {m fringe := \{ s : (s \in unseen \wedge \exists s' \in fringe : (T(s,s') > 0)) \}} *)
        let fringe =
          get_next_fringe states unseen
            (Int_set.exists (fun i -> Int_set.mem i fringe))
        in
        aux labels unseen fringe (n - 1)
  in
  let fringe, _, unseen = partition_states states labels f f' in
  let mr = Int.min (Int_set.cardinal unseen) t in
  aux labels unseen fringe mr

(** [label_eu states labels ~t f f'] labels states for the case of the until operator {m f U^{\geq t}_{\geq 1} f'} *)
let label_au states labels ~t f f' =
  let f_main = strong_until_f ~t:(T t) ~p:One ~op:Geq f f' in
  let rec aux labels unseen fringe seen = function
    | 0 ->
        (* {m \forall x \in fringe do addlabel(s,f_{main})} *)
        add_labels labels fringe f_main
    | n ->
        (* {m \forall x \in fringe do addlabel(s,f_{main})} *)
        let labels = add_labels labels fringe f_main in
        (* {m unseen := unseen - fringe} *)
        let unseen = Int_set.diff unseen fringe in
        (* {m seen := seen \cup fringe} *)
        let seen = Int_set.union seen fringe in
        (* {m fringe := \{ s : (s \in unseen \wedge \forall s' \in seen : (T(s,s') > 0)) \}} *)
        let fringe =
          get_next_fringe states unseen
            (Int_set.for_all (fun i -> Int_set.mem i seen))
        in
        aux labels unseen fringe seen (n - 1)
  in
  let fringe, _, unseen = partition_states states labels f f' in
  let seen = Int_set.empty in
  let mr = Int.min (Int_set.cardinal unseen) t in
  aux labels unseen fringe seen mr

let strong_until states labels ~t ~p ~op f f' =
  match (t, p, op) with
  | Formula.T t, Formula.Zero, Formula.Gt -> label_eu states labels ~t f f'
  | Infinity, Zero, Gt ->
      let n_inconclusive =
        let _, _, unseen = partition_states states labels f f' in
        Int_set.cardinal unseen
      in
      label_eu states labels ~t:n_inconclusive f f'
  | Formula.T t, Formula.One, Formula.Geq -> label_au states labels ~t f f'
  | Infinity, One, Geq ->
      let n_inconclusive =
        let _, _, unseen = partition_states states labels f f' in
        Int_set.cardinal unseen
      in
      label_au states labels ~t:n_inconclusive f f'
  | T t, Pr p, _ ->
      let f_main = Formula.(P (op, Pr p, Strong_until (T t, f, f'))) in
      let probabilities = mu_measure_until states labels t f f' in
      Int_map.mapi
        (fun i s ->
          let p' = probabilities.(i) in
          if Formula.compare_prob_with_op op p' p then Formula.Set.add f_main s
          else s)
        labels
  | _, One, Gt -> labels
  | t, Zero, Geq ->
      let state_ids =
        Int_map.bindings states |> List.map fst |> Int_set.of_list
      in
      add_labels labels state_ids (strong_until_f ~t ~p ~op f f')
  | Infinity, Pr _, _ ->
      failwith "General case of infinite-length paths is not handled"
