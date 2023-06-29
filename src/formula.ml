open Ppx_compare_lib.Builtin

(** Comparison operators for PCTL path operators *)
type comparison = Geq | Gt [@@deriving compare]

let compare_probability c p p' =
  match c with Geq -> Float.compare p p' >= 0 | Gt -> Float.compare p p' > 0

type time = T of int | Infinity [@@deriving compare]

let v_time = function
  | T t ->
      assert (t >= 0);
      T t
  | t -> t

type prob = One | Pr of float | Zero [@@deriving compare]

let v_prob = function
  | Pr p ->
      assert (Float.(compare p 1.0 < 0 && compare p 0.0 > 0));
      Pr p
  | p -> p

(** PCTL state formulae *)
type s =
  | Bool of bool
  | Prop of Model.Aprop.t
  | Neg of s
  | Or of s * s
  | And of s * s
  | Impl of s * s
  | P of comparison * prob * p
  | A of p
  | E of p
[@@deriving compare]

(** PCTL path formulae *)
and p =
  | Strong_until of time * s * s
  | Weak_until of time * s * s
  | Generally of time * s
  | Finally of time * s
  | Leads_to of time * s * s
[@@deriving compare]

type t = s [@@deriving compare]
(** Top-level PCTL formulae must be state formulae *)

module Set = Set.Make (struct
  type t = s

  let compare = compare_s
end)

let f_in_state_labels labels i f = Int_map.find i labels |> Set.mem f
