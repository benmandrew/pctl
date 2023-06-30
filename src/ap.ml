(** Atomic propositions for traffic lights *)
type m = Green | Red | Amber [@@deriving compare, show]

module Set = Set.Make (struct
  type t = m

  let compare = compare_m
end)

type t = m [@@deriving compare, show]
