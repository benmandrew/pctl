open Ppx_compare_lib.Builtin

(** Comparison operators for PCTL path operators *)
type comparison = Geq | Gt [@@deriving compare]

let compare_probability c p p' =
  match c with Geq -> Float.compare p p' >= 0 | Gt -> Float.compare p p' > 0

(** PCTL state formulae *)
type s =
  | B of bool
  | Prop of Model.Aprop.t
  | Neg of s
  | Or of s * s
  | And of s * s
  | Impl of s * s
  | P of comparison * float * p
[@@deriving compare]

(** PCTL path formulae *)
and p = U of int * s * s | W of int * s * s [@@deriving compare]

type t = s [@@deriving compare]
(** Top-level PCTL formulae must be state formulae *)

module Set = Set.Make (struct
  type t = s

  let compare = compare_s
end)

let f_in_state_labels labels i f = Int_map.find i labels |> Set.mem f
