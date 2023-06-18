open Pctl
open Ppx_compare_lib.Builtin
open Sexplib.Std

let%test_unit "Model checking for non-modal operators" =
  let open Model in
  let states =
    [
      (0, State.v_list [ (0, 0.5); (1, 0.5) ] [ Ap.Green ]);
      (1, State.v_list [ (0, 0.5); (1, 0.5) ] [ Ap.Red ]);
    ]
  in
  let k = Kripke.v_list 0 states in
  (* Green /\ Red *)
  let f = Formula.(And (Prop Ap.Green, Prop Ap.Red)) in
  let result = Check.v k f in
  [%test_result: bool] result ~expect:false;
  (* Green \/ Red *)
  let f = Formula.(Or (Prop Ap.Green, Prop Ap.Red)) in
  let result = Check.v k f in
  [%test_result: bool] result ~expect:true;
  (* Green /\ (~ Red) *)
  let f = Formula.(And (Prop Ap.Green, Neg (Prop Ap.Red))) in
  let result = Check.v k f in
  [%test_result: bool] result ~expect:true

let%test_unit "Model checking for until modal operator, short" =
  let open Model in
  let states =
    [
      (0, State.v_list [ (0, 0.1); (1, 0.9) ] [ Ap.Green ]);
      (1, State.v_list [ (0, 0.9); (1, 0.1) ] [ Ap.Red ]);
    ]
  in
  let k = Kripke.v_list 0 states in
  (* P_{p >= 0.5} ( true U_{t <= 5} Red ) *)
  let f = Formula.(P (Geq, 0.99, U (5, Prop Ap.Green, Prop Ap.Red))) in
  let result = Check.v k f in
  [%test_result: bool] result ~expect:true

let%test_unit "Model checking for until modal operator, long" =
  let open Model in
  let states =
    [
      (0, State.v_list [ (0, 0.99); (1, 0.01) ] [ Ap.Green ]);
      (1, State.v_list [ (1, 1.0) ] [ Ap.Red ]);
    ]
  in
  let k = Kripke.v_list 0 states in
  (* P_{p >= 0.5} ( true U_{t <= 60} Red ) *)
  let f = Formula.(P (Geq, 0.5, U (60, Prop Ap.Green, Prop Ap.Red))) in
  let result = Check.v k f in
  [%test_result: bool] result ~expect:false;
  (* P_{p >= 0.5} ( true U_{t <= 70} Red ) *)
  let f = Formula.(P (Geq, 0.5, U (70, Prop Ap.Green, Prop Ap.Red))) in
  let result = Check.v k f in
  [%test_result: bool] result ~expect:true

let%test_unit "Model checking for weak until modal operator" =
  let open Model in
  let states =
    [
      (0, State.v_list [ (0, 0.1); (1, 0.9) ] [ Ap.Green ]);
      (1, State.v_list [ (0, 0.9); (2, 0.1) ] [ Ap.Red ]);
      (2, State.v_list [ (1, 0.1); (2, 0.9) ] [ Ap.Amber ]);
    ]
  in
  let k = Kripke.v_list 0 states in
  (* P_{p >= 0.99} ( Green \/ Red W_{t <= 5} Amber ) *)
  let f =
    Formula.(
      P (Geq, 0.99, W (5, Or (Prop Ap.Green, Prop Ap.Red), Prop Ap.Amber)))
  in
  let result = Check.v k f in
  [%test_result: bool] result ~expect:true
