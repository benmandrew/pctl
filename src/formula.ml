open Ppx_compare_lib.Builtin

(** Comparison operators for PCTL path operators *)
type comparison = Geq | Gt [@@deriving compare, show]

let compare_probability c p p' =
  match c with Geq -> Float.compare p p' >= 0 | Gt -> Float.compare p p' > 0

type time = T of int | Infinity [@@deriving compare, show]

let v_time = function
  | T t ->
      assert (t >= 0);
      T t
  | t -> t

type prob = One | Pr of float | Zero [@@deriving compare, show]

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
[@@deriving compare, show]

(** PCTL path formulae *)
and p =
  | Strong_until of time * s * s
  | Weak_until of time * s * s
  | Generally of time * s
  | Finally of time * s
  | Leads_to of time * s * s
[@@deriving compare, show]

type t = s [@@deriving compare, show]
(** Top-level PCTL formulae must be state formulae *)

let canonicalise =
  let rec c_s = function
    | A f -> c_s (P (Geq, One, f))
    | E f -> c_s (P (Gt, Zero, f))
    | P (op, p, Weak_until (t, f, f')) ->
        let p =
          match p with Pr p -> Pr (1.0 -. p) | One -> Zero | Zero -> One
        in
        let op = match op with Geq -> Gt | Gt -> Geq in
        P (op, p, Strong_until (t, Neg f', And (Neg f, Neg f')))
    | P (op, p, Leads_to (t, f, f')) ->
        c_s (A (Generally (Infinity, Impl (f, P (op, p, Finally (t, f'))))))
    | P (op, p, Generally (t, f)) ->
        c_s (P (op, p, Weak_until (t, f, Bool false)))
    | Neg f -> c_s f
    | Or (f, f') -> Or (c_s f, c_s f')
    | And (f, f') -> And (c_s f, c_s f')
    | Impl (f, f') -> Impl (c_s f, c_s f')
    | P (op, p, f) -> P (op, p, c_p f)
    | f -> f
  and c_p = function
    | Strong_until (t, f, f') -> Strong_until (t, c_s f, c_s f')
    | Finally (t, f) -> Strong_until (t, Bool true, f)
    | f -> f
  in
  c_s

let compare t t' = compare_s (canonicalise t) (canonicalise t')

module Set = Set.Make (struct
  type t = s

  let compare = compare
end)

let f_in_state_labels labels i f = Int_map.find i labels |> Set.mem f
