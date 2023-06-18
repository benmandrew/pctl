open Pctl
open Ppx_compare_lib.Builtin
open Sexplib.Std

let%test_unit "Model checking for non-modal operators" =
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

let%test_unit "Model checking for until modal operator, short" =
  let open Model in
  let states =
    [
      (0, State.v_list [ (0, 0.1); (1, 0.9) ] [ Aprop.Green ]);
      (1, State.v_list [ (0, 0.9); (1, 0.1) ] [ Aprop.Red ]);
    ]
  in
  let k = Kripke.v_list 0 states in
  (* P_{p >= 0.5} ( true U_{t <= 5} Red ) *)
  let f = Formula.(P (Geq, 0.99, U (5, B true, Prop Aprop.Red))) in
  let result = Check.v k f in
  [%test_result: bool] result ~expect:true

let%test_unit "Model checking for until modal operator, long" =
  let open Model in
  let states =
    [
      (0, State.v_list [ (0, 0.99); (1, 0.01) ] [ Aprop.Green ]);
      (1, State.v_list [ (0, 0.0); (1, 1.0) ] [ Aprop.Red ]);
    ]
  in
  let k = Kripke.v_list 0 states in
  (* P_{p >= 0.5} ( true U_{t <= 5} Red ) *)
  let f = Formula.(P (Geq, 0.5, U (60, B true, Prop Aprop.Red))) in
  let result = Check.v k f in
  [%test_result: bool] result ~expect:false;
  let f = Formula.(P (Geq, 0.5, U (70, B true, Prop Aprop.Red))) in
  let result = Check.v k f in
  [%test_result: bool] result ~expect:true
