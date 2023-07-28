type t = float Array.t Array.t

let init n f : t = Array.init n (fun i -> Array.init n (fun j -> f i j))
let mapi f t = Array.mapi (fun i r -> Array.mapi (fun j v -> f i j v) r) t

let print t =
  Array.iter
    (fun r ->
      Array.iter (fun v -> Printf.printf "%.2f " v) r;
      Printf.printf "\n")
    t

let column_arg_max n h k t =
  let i_max = ref 0 in
  for i = h to n - 1 do
    if Float.compare (abs_float t.(i).(k)) (abs_float t.(!i_max).(k)) > 0 then
      i_max := i
  done;
  !i_max

let swap_rows i j (t : t) =
  let tmp = t.(i) in
  t.(i) <- t.(j);
  t.(j) <- tmp

let f_eq v0 v1 = Float.(compare (abs (v0 -. v1)) 0.0001 < 0)

(** https://en.wikipedia.org/wiki/Gaussian_elimination#Pseudocode *)
let gaussian_elim n t =
  print t;
  let rec f h k t =
    if h >= n || k >= n then t
    else
      let i_max = column_arg_max n h k t in
      if f_eq t.(i_max).(k) 0.0 then f h (k + 1) t
      else (
        swap_rows h i_max t;
        for i = h + 1 to n - 1 do
          let f = t.(i).(k) /. t.(h).(k) in
          t.(i).(k) <- 0.0;
          for j = k + 1 to n - 1 do
            let v = t.(i).(j) -. (f *. t.(h).(j)) in
            t.(i).(k) <- v
          done
        done;
        f (h + 1) (k + 1) t)
  in
  f 0 0 (Array.copy t)

(** https://www.math.usm.edu/lambers/mat610/sum10/lecture4.pdf *)
let back_substitute n t =
  print t;
  let x = Array.make n 0.0 in
  for i = n - 1 downto 0 do
    for j = i to n - 1 do
      x.(i) <- x.(i) -. (t.(i).(j) *. x.(j))
    done;
    x.(i) <- x.(i) /. t.(i).(i)
  done;
  Array.iter (fun x -> Printf.printf "%f\n" x) x;
  x
