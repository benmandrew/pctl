module Int_map = Map.Make (Int)
include Int_map

let key_difference a b = Int_map.filter (fun i _ -> Int_map.mem i b) a
