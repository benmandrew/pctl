(** PCTL state and path formulae *)

type comparison = Geq | Gt [@@deriving compare]

(* To satisfy the [compare] PPX below *)
let compare_float = Float.compare

(** State formulae *)
type s =
  | Prop of Model.Aprop.t
  | Neg of s
  | Or of s * s
  | And of s * s
  | Impl of s * s
  | Pgeq of float * p
[@@deriving compare]

(** Path formulae *)
and p = U of comparison * float * s * s | W of comparison * float * s * s
[@@deriving compare]

type t = s [@@deriving compare]
(** Top-level PCTL formulae must be state formulae *)

module Set = Set.Make (struct
  type t = s

  let compare = compare_s
end)

let f_in_state_labels labels i f = Int_map.find i labels |> Set.mem f
