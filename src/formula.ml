open Ppx_compare_lib.Builtin

(** Comparison operators for PCTL path operators *)
type comparison = Geq | Gt [@@deriving compare]

let compare_probability c p p' =
  match c with Geq -> Float.compare p p' >= 0 | Gt -> Float.compare p p' > 0

type inf_nat = N of int | Infinity [@@deriving compare]

(** PCTL state formulae *)
type s =
  | Bool of bool
  | Prop of Model.Aprop.t
  | Neg of s
  | Or of s * s
  | And of s * s
  | Impl of s * s
  | P of comparison * float * p
  | A of p
  | E of p
[@@deriving compare]

(** PCTL path formulae *)
and p =
  | Strong_until of inf_nat * s * s
  | Weak_until of inf_nat * s * s
  | Generally of inf_nat * s
  | Finally of inf_nat * s
  | Leads_to of inf_nat * s * s
[@@deriving compare]

type t = s [@@deriving compare]
(** Top-level PCTL formulae must be state formulae *)

module Set = Set.Make (struct
  type t = s

  let compare = compare_s
end)

let f_in_state_labels labels i f = Int_map.find i labels |> Set.mem f
