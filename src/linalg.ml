module Vec = struct
  type t = float Array.t

  let init n f : t = Array.init n f
  let mapi f (t : t) : t = Array.mapi f t

  let print t =
    Array.iter (fun v -> Printf.printf "%.2f " v) t;
    Printf.printf "\n"
end

module Mat = struct
  type t = Vec.t Array.t

  let init n f : t = Array.init n (fun i -> Vec.init n (f i))
  let mapi f t : t = Array.mapi (fun i r -> Vec.mapi (f i) r) t
  let print t = Array.iter Vec.print t
  let copy (t : t) : t = Array.map Array.copy t
end

let column_arg_max n h k t =
  let i_max = ref 0 in
  for i = h to n - 1 do
    (* Printf.printf "%d %d %d %d\n" i h k n; *)
    if Float.compare (abs_float t.(i).(k)) (abs_float t.(!i_max).(k)) > 0 then
      i_max := i
  done;
  !i_max

let swap_rows (t : Mat.t) i j =
  let tmp = t.(i) in
  t.(i) <- t.(j);
  t.(j) <- tmp

let f_eq v0 v1 = Float.(compare (abs (v0 -. v1)) 0.0001 < 0)

(** https://en.wikipedia.org/wiki/Gaussian_elimination#Pseudocode *)
let gaussian_elim n m =
  let rec f h k t =
    if h >= n - 1 || k >= n - 1 then t
    else
      let i_max = column_arg_max n h k t in
      if f_eq t.(i_max).(k) 0.0 then f h (k + 1) t
      else (
        swap_rows t h i_max;
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
  f 0 0 (Mat.copy m)

(** https://www.math.usm.edu/lambers/mat610/sum10/lecture4.pdf *)
let back_substitute n m v =
  let x = Array.copy v in
  for i = n - 1 downto 0 do
    for j = i to n - 1 do
      x.(i) <- x.(i) -. (m.(i).(j) *. x.(j))
    done;
    x.(i) <- x.(i) /. m.(i).(i)
  done;
  (* Array.iter (fun x -> Printf.printf "%f\n" x) x; *)
  x

(* module Test = struct
     open Base

     let%test_unit "rev" =
       let m = [|  |] in


       [%test_eq: int list] (List.rev [ 3; 2; 1 ]) [ 3; 2; 1 ]


   end *)
