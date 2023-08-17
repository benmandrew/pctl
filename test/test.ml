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
  let f =
    Formula.(P (Geq, Pr 0.99, Strong_until (T 5, Prop Ap.Green, Prop Ap.Red)))
  in
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
  let f =
    Formula.(P (Geq, Pr 0.5, Strong_until (T 60, Prop Ap.Green, Prop Ap.Red)))
  in
  let result = Check.v k f in
  [%test_result: bool] result ~expect:false;
  (* P_{p >= 0.5} ( true U_{t <= 70} Red ) *)
  let f =
    Formula.(P (Geq, Pr 0.5, Strong_until (T 70, Prop Ap.Green, Prop Ap.Red)))
  in
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
  (* P_{p >= 0.99} ( (Green \/ Red) W_{t <= 5} Amber ) *)
  let f =
    Formula.(
      P
        ( Geq,
          Pr 0.99,
          Weak_until (T 5, Or (Prop Ap.Green, Prop Ap.Red), Prop Ap.Amber) ))
  in
  let k = Kripke.v_list 0 states in
  let result = Check.v k f in
  [%test_result: bool] result ~expect:true;
  let k = Kripke.v_list 1 states in
  let result = Check.v k f in
  [%test_result: bool] result ~expect:true;
  let k = Kripke.v_list 2 states in
  let result = Check.v k f in
  [%test_result: bool] result ~expect:true

let%test_unit "Model checking for strong until modal operator with p > 0" =
  let open Model in
  let states =
    [
      (0, State.v_list [ (1, 1.0) ] [ Ap.Green ]);
      (1, State.v_list [ (2, 0.99); (3, 0.01) ] []);
      (2, State.v_list [ (2, 1.0) ] [ Ap.Red ]);
      (3, State.v_list [ (3, 1.0) ] [ Ap.Amber ]);
    ]
  in
  let k = Kripke.v_list 0 states in
  (* P_{p > 0} ( true U_{t <= 2} Amber ) *)
  let f = Formula.(E (Strong_until (T 2, Bool true, Prop Ap.Amber))) in
  let result = Check.v k f in
  [%test_result: bool] result ~expect:true;
  (* P_{p > 0} ( true U_{t <= 10} (Red /\ Amber) ) *)
  let f =
    Formula.(
      E (Strong_until (T 10, Bool true, And (Prop Ap.Red, Prop Ap.Amber))))
  in
  let result = Check.v k f in
  [%test_result: bool] result ~expect:false

let%test_unit "Model checking for strong until modal operator with p >= 1" =
  let open Model in
  let states =
    [
      (0, State.v_list [ (1, 1.0) ] [ Ap.Green ]);
      (1, State.v_list [ (2, 0.99); (3, 0.01) ] []);
      (2, State.v_list [ (2, 1.0) ] [ Ap.Red ]);
      (3, State.v_list [ (3, 1.0) ] [ Ap.Amber ]);
    ]
  in
  let k = Kripke.v_list 0 states in
  (* P_{p >= 1} ( true U_{t <= 2} Amber ) *)
  let f = Formula.(A (Strong_until (T 2, Bool true, Prop Ap.Amber))) in
  let result = Check.v k f in
  [%test_result: bool] result ~expect:false;
  (* P_{p >= 1} ( true U_{t <= 1} Green ) *)
  let f = Formula.(A (Strong_until (T 1, Bool true, Prop Ap.Green))) in
  let result = Check.v k f in
  [%test_result: bool] result ~expect:true

let%test_unit "Model checking for strong until modal operator with t = Inf" =
  let open Model in
  let states =
    [
      (0, State.v_list [ (0, 0.99); (1, 0.01) ] [ Ap.Green ]);
      (1, State.v_list [ (1, 1.0) ] [ Ap.Red ]);
    ]
  in
  let k = Kripke.v_list 0 states in
  (* P_{p >= 0.5} ( Green U_{t <= Infinity} Red ) *)
  let f =
    Formula.(
      P (Geq, Pr 0.5, Strong_until (Infinity, Prop Ap.Green, Prop Ap.Red)))
  in
  let result = Check.v k f in
  [%test_result: bool] result ~expect:true

let%test_unit "Model checking for weak until modal operator with t = Inf" =
  let open Model in
  let states =
    [
      (0, State.v_list [ (0, 0.1); (1, 0.9) ] [ Ap.Green ]);
      (1, State.v_list [ (0, 0.9); (2, 0.1) ] [ Ap.Red ]);
      (2, State.v_list [ (1, 0.1); (2, 0.9) ] [ Ap.Amber ]);
    ]
  in
  (* P_{p >= 0.99} ( (Green \/ Red) W_{t <= 5} Amber ) *)
  let f =
    Formula.(
      P
        ( Geq,
          Pr 0.99,
          Weak_until (Infinity, Or (Prop Ap.Green, Prop Ap.Red), Prop Ap.Amber)
        ))
  in
  let k = Kripke.v_list 0 states in
  let result = Check.v k f in
  [%test_result: bool] result ~expect:true;
  let k = Kripke.v_list 1 states in
  let result = Check.v k f in
  [%test_result: bool] result ~expect:true;
  let k = Kripke.v_list 2 states in
  let result = Check.v k f in
  [%test_result: bool] result ~expect:true
