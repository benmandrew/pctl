val strong_until :
  Model.State.t Int_map.t ->
  Formula.Set.t Int_map.t ->
  t:Formula.time ->
  p:Formula.prob ->
  op:Formula.comparison ->
  Formula.s ->
  Formula.s ->
  Formula.Set.t Int_map.t
