open Pctl
open Ppx_compare_lib.Builtin
open Sexplib.Std

let%test_unit "Ast.Runtime.exec - assgn" =
  let open Model in
  let states =
    [
      (0, State.v_list [ (0, 0.5); (1, 0.5) ] [ Aprop.Green ]);
      (1, State.v_list [ (0, 0.5); (1, 0.5) ] [ Aprop.Red ]);
    ]
  in
  let k = Kripke.v_list 0 states in
  (* Green /\ Red *)
  let f = Formula.(And (Prop Aprop.Green, Prop Aprop.Red)) in
  let result = Check.v k f in
  [%test_result: bool] result ~expect:false;
  (* Green \/ Red *)
  let f = Formula.(Or (Prop Aprop.Green, Prop Aprop.Red)) in
  let result = Check.v k f in
  [%test_result: bool] result ~expect:true;
  (* Green /\ (~ Red) *)
  let f = Formula.(And (Prop Aprop.Green, Neg (Prop Aprop.Red))) in
  let result = Check.v k f in
  [%test_result: bool] result ~expect:true
