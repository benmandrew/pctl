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
        && not (f_in_state_labels labels i f))
    then (s_s, Int_set.add i s_f, s_i)
    else (s_s, s_f, Int_set.add i s_i)
  in
  Int_map.fold f states Int_set.(empty, empty, empty)

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
    (* Int_set.iter (Printf.printf "next %d\n") next_states; *)
    if next_states_condition next_states then
      (*Printf.printf "add %d\n" i; *)
      Int_set.add i acc
    else acc
  in
  Int_set.fold add_s_conditional unseen Int_set.empty

(** [label_eu states labels ~t f f'] labels states for the case of the until operator {m f U^{\geq t}_{>0} f'} *)
let label_eu states labels ~t f f' =
  let f_main = Formula.(P (Gt, Zero, Strong_until (T t, f, f'))) in
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

let label_au states labels ~t f f' =
  let f_main = Formula.(P (Geq, One, Strong_until (T t, f, f'))) in
  let rec aux labels unseen fringe seen = function
    | 0 -> labels
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
  | Infinity, Pr _, Geq -> raise Exit
  | Formula.T t, Formula.One, Formula.Geq -> label_au states labels ~t f f'
  | T t, Pr p, _ ->
      let f_main = Formula.(P (op, Pr p, Strong_until (T t, f, f'))) in
      let probabilities = mu_measure_until states labels t f f' in
      Int_map.mapi
        (fun i s ->
          let p' = probabilities.(i) in
          if Formula.compare_probability op p' p then Formula.Set.add f_main s
          else s)
        labels
  | _, _, _ -> raise Exit
