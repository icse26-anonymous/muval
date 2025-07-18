open OUnit
open Ast
open Ast.LogicOld
open Testutil
open Reclimitprover
open Convert

let int_var name = Term.mk_var (Ident.Tvar name) T_int.SInt Dummy
let pred_var name = Predicate.Var (Ident.Pvar name, [ T_bool.SBool ])

(*** logic.ml ***)
let fml_true = Formula.mk_atom (Atom.mk_true Dummy) Dummy
let fml_false = Formula.mk_atom (Atom.mk_false Dummy) Dummy

(** HES **)
let hes_empty_true = MuCLP.Problem.make [] fml_true

let hes_empty_false = MuCLP.Problem.make [] fml_false

(* forall X. F X *)
let varF = pred_var "F"
let varG = pred_var "G"
let varX = int_var "X"
let varY = int_var "Y"

let query_forall =
  Formula.mk_forall
    [ (Ident.Tvar "X", T_int.SInt) ]
    (Formula.mk_atom (Atom.mk_app varF [ varX ] Dummy) Dummy)
    Dummy

let query_exists =
  Formula.mk_exists
    [ (Ident.Tvar "X", T_int.SInt) ]
    (Formula.mk_atom (Atom.mk_app varF [ varX ] Dummy) Dummy)
    Dummy

(* forall X. F X; F X =nu F (X * 2) *)
let hes_nu =
  MuCLP.Problem.make
    [
      ( Predicate.Nu,
        Ident.Pvar "F",
        [ (Ident.Tvar "X", T_int.SInt) ],
        Formula.mk_atom
          (Atom.mk_app varF
             [ T_int.mk_mul varX (T_int.mk_int (Bigint.of_int 2) Dummy) Dummy ]
             Dummy)
          Dummy );
    ]
    query_forall

(* forall X. F X; F X =nu X >= 5 -> G X; G X =nu X >= 5 /\ (G (X - 1) \/ G (X + 1)) *)
let hes_nunu =
  MuCLP.Problem.make
    [
      ( Predicate.Nu,
        Ident.Pvar "F",
        [ (Ident.Tvar "X", T_int.SInt) ],
        Formula.mk_imply
          (Formula.mk_atom
             (T_int.mk_geq varX (T_int.mk_int (Bigint.of_int 5) Dummy) Dummy)
             Dummy)
          (Formula.mk_atom (Atom.mk_app varG [ varX ] Dummy) Dummy)
          Dummy );
      ( Predicate.Nu,
        Ident.Pvar "G",
        [ (Ident.Tvar "X", T_int.SInt) ],
        Formula.mk_and
          (Formula.mk_atom
             (T_int.mk_geq varX (T_int.mk_int (Bigint.of_int 5) Dummy) Dummy)
             Dummy)
          (Formula.mk_or
             (Formula.mk_atom
                (Atom.mk_app varG
                   [
                     T_int.mk_sub varX
                       (T_int.mk_int (Bigint.of_int 1) Dummy)
                       Dummy;
                   ]
                   Dummy)
                Dummy)
             (Formula.mk_atom
                (Atom.mk_app varG
                   [
                     T_int.mk_add varX
                       (T_int.mk_int (Bigint.of_int 1) Dummy)
                       Dummy;
                   ]
                   Dummy)
                Dummy)
             Dummy)
          Dummy );
    ]
    query_forall

(* forall X. F X; F X =nu (X > 0 => G (X + 1)) /\ (X <= 0 => F (X - 1)); G X =mu (X >= 10 => F (X - 10)) /\ (X < 10 => F X) *)
let hes_numu =
  MuCLP.Problem.make
    [
      ( Predicate.Nu,
        Ident.Pvar "F",
        [ (Ident.Tvar "X", T_int.SInt) ],
        Formula.mk_and
          (Formula.mk_imply
             (Formula.mk_atom
                (T_int.mk_gt varX (T_int.mk_int (Bigint.of_int 0) Dummy) Dummy)
                Dummy)
             (Formula.mk_atom
                (Atom.mk_app varG
                   [
                     T_int.mk_add varX
                       (T_int.mk_int (Bigint.of_int 1) Dummy)
                       Dummy;
                   ]
                   Dummy)
                Dummy)
             Dummy)
          (Formula.mk_imply
             (Formula.mk_atom
                (T_int.mk_leq varX (T_int.mk_int (Bigint.of_int 0) Dummy) Dummy)
                Dummy)
             (Formula.mk_atom
                (Atom.mk_app varG
                   [
                     T_int.mk_sub varX
                       (T_int.mk_int (Bigint.of_int 1) Dummy)
                       Dummy;
                   ]
                   Dummy)
                Dummy)
             Dummy)
          Dummy );
      ( Predicate.Mu,
        Ident.Pvar "G",
        [ (Ident.Tvar "X", T_int.SInt) ],
        Formula.mk_and
          (Formula.mk_imply
             (Formula.mk_atom
                (T_int.mk_geq varX
                   (T_int.mk_int (Bigint.of_int 10) Dummy)
                   Dummy)
                Dummy)
             (Formula.mk_atom
                (Atom.mk_app varF
                   [
                     T_int.mk_sub varX
                       (T_int.mk_int (Bigint.of_int 10) Dummy)
                       Dummy;
                   ]
                   Dummy)
                Dummy)
             Dummy)
          (Formula.mk_imply
             (Formula.mk_atom
                (T_int.mk_lt varX (T_int.mk_int (Bigint.of_int 10) Dummy) Dummy)
                Dummy)
             (Formula.mk_atom (Atom.mk_app varF [ varX ] Dummy) Dummy)
             Dummy)
          Dummy );
    ]
    query_forall

(* forall X. F X; F X =nu X < 1000 *)
let hes_nu2 =
  MuCLP.Problem.make
    [
      ( Predicate.Nu,
        Ident.Pvar "F",
        [ (Ident.Tvar "X", T_int.SInt) ],
        Formula.mk_atom
          (T_int.mk_leq varX (T_int.mk_int (Bigint.of_int 1000) Dummy) Dummy)
          Dummy );
    ]
    query_forall

(* forall X. F X; F X =nu G X X; G X Y =nu X <= 2 * Y /\ G (X + 9) (Y + 4) *)
let hes_nunu2 =
  MuCLP.Problem.make
    [
      ( Predicate.Nu,
        Ident.Pvar "F",
        [ (Ident.Tvar "X", T_int.SInt) ],
        Formula.mk_atom (Atom.mk_app varG [ varX; varX ] Dummy) Dummy );
      ( Predicate.Nu,
        Ident.Pvar "G",
        [ (Ident.Tvar "X", T_int.SInt); (Ident.Tvar "Y", T_int.SInt) ],
        Formula.mk_and
          (Formula.mk_atom
             (T_int.mk_leq varX
                (T_int.mk_mul (T_int.mk_int (Bigint.of_int 2) Dummy) varY Dummy)
                Dummy)
             Dummy)
          (Formula.mk_atom
             (Atom.mk_app varG
                [
                  T_int.mk_add varX (T_int.mk_int (Bigint.of_int 9) Dummy) Dummy;
                  T_int.mk_add varY (T_int.mk_int (Bigint.of_int 4) Dummy) Dummy;
                ]
                Dummy)
             Dummy)
          Dummy );
    ]
    query_forall

(* F 10; F X =mu F (X + 1) *)
let hes_mu2 =
  MuCLP.Problem.make
    [
      ( Predicate.Mu,
        Ident.Pvar "F",
        [ (Ident.Tvar "X", T_int.SInt) ],
        Formula.mk_atom
          (Atom.mk_app varF
             [ T_int.mk_add varX (T_int.mk_int (Bigint.of_int 1) Dummy) Dummy ]
             Dummy)
          Dummy );
    ]
    (Formula.mk_atom
       (Atom.mk_app varF [ T_int.mk_int (Bigint.of_int 10) Dummy ] Dummy)
       Dummy)

(* exists X. F X; F X =mu X = 3 *)
let hes_mu3 =
  MuCLP.Problem.make
    [
      ( Predicate.Mu,
        Ident.Pvar "F",
        [ (Ident.Tvar "X", T_int.SInt) ],
        Formula.eq varX (T_int.mk_int (Bigint.of_int 3) Dummy) );
    ]
    query_exists

(* forall X. F X; F X =mu X < 0 \/ F (X + 1) \/ F (X - 1) *)
let hes_mu_forall =
  MuCLP.Problem.make
    [
      ( Predicate.Mu,
        Ident.Pvar "F",
        [ (Ident.Tvar "X", T_int.SInt) ],
        Formula.mk_or
          (Formula.mk_atom
             (T_int.mk_lt varX (T_int.mk_int (Bigint.of_int 0) Dummy) Dummy)
             Dummy)
          (Formula.mk_or
             (Formula.mk_atom
                (Atom.mk_app varF
                   [
                     T_int.mk_add varX
                       (T_int.mk_int (Bigint.of_int 1) Dummy)
                       Dummy;
                   ]
                   Dummy)
                Dummy)
             (Formula.mk_atom
                (Atom.mk_app varF
                   [
                     T_int.mk_sub varX
                       (T_int.mk_int (Bigint.of_int 1) Dummy)
                       Dummy;
                   ]
                   Dummy)
                Dummy)
             Dummy)
          Dummy );
    ]
    query_forall

(* forall X. F X; F X =mu X >= 100 => G X; G X =mu X > 0 /\ G (X + 1) /\ G (X - 1) *)
let hes_mu_for_approx =
  MuCLP.Problem.make
    [
      ( Predicate.Mu,
        Ident.Pvar "F",
        [ (Ident.Tvar "X", T_int.SInt) ],
        Formula.mk_imply
          (Formula.mk_atom
             (T_int.mk_geq varX (T_int.mk_int (Bigint.of_int 100) Dummy) Dummy)
             Dummy)
          (Formula.mk_atom (Atom.mk_app varG [ varX ] Dummy) Dummy)
          Dummy );
      ( Predicate.Mu,
        Ident.Pvar "G",
        [ (Ident.Tvar "X", T_int.SInt) ],
        Formula.mk_and
          (Formula.mk_atom
             (T_int.mk_gt varX (T_int.mk_int (Bigint.of_int 0) Dummy) Dummy)
             Dummy)
          (Formula.mk_and
             (Formula.mk_atom
                (Atom.mk_app varG
                   [
                     T_int.mk_add varX
                       (T_int.mk_int (Bigint.of_int 1) Dummy)
                       Dummy;
                   ]
                   Dummy)
                Dummy)
             (Formula.mk_atom
                (Atom.mk_app varG
                   [
                     T_int.mk_sub varX
                       (T_int.mk_int (Bigint.of_int 1) Dummy)
                       Dummy;
                   ]
                   Dummy)
                Dummy)
             Dummy)
          Dummy );
    ]
    query_forall

(* forall X. F X; F X =mu F (X + 1) *)
let hes_mu4 =
  MuCLP.Problem.make
    [
      ( Predicate.Mu,
        Ident.Pvar "F",
        [ (Ident.Tvar "X", T_int.SInt) ],
        Formula.mk_atom
          (Atom.mk_app varF
             [ T_int.mk_add varX (T_int.mk_int (Bigint.of_int 1) Dummy) Dummy ]
             Dummy)
          Dummy );
    ]
    query_forall

(*** util ***)
let rec gen_cases solve = function
  | [] -> []
  | (name, hes, expected) :: tail ->
      {
        name;
        actual =
          (fun () ->
            let hes' = Hesutil.simplify hes in
            let result = solve hes' in
            (hes, result));
        expected = (hes, expected);
      }
      :: gen_cases solve tail

(*** solver.ml ***)
let solve_onlynu_onlyforall_tests =
  gen_cases Solver.solve
    [
      ("nu", hes_nu, Status.Valid);
      ("nunu", hes_nunu, Status.Valid);
      ("nu2", hes_nu2, Status.Invalid);
      ("nunu2", hes_nunu2, Status.Invalid);
    ]

let solve_onlymu_onlyexists_tests =
  gen_cases Solver.solve
    [ ("mu2", hes_mu2, Status.Invalid); ("mu3", hes_mu3, Status.Valid) ]

let solve_onlyforall_tests =
  gen_cases Solver.solve
    [
      (* "mu_forall", hes_mu_forall, Status.Valid; *)
      ("mu_for_approx", hes_mu_for_approx, Status.Invalid);
    ]

(*** simpleSolver.ml ***)
let simplesolve_onlynu_onlyforall_tests =
  gen_cases SimpleSolver.solve
    [
      ("nu", hes_nu, Status.Valid);
      ("nunu", hes_nunu, Status.Valid);
      ("nu2", hes_nu2, Status.Invalid);
      ("nunu2", hes_nunu2, Status.Invalid);
    ]

let simplesolve_onlymu_onlyexists_tests =
  gen_cases SimpleSolver.solve
    [
      ("mu2", hes_mu2, Status.Invalid);
      ("mu3", hes_mu3, Status.Valid);
      ("mu_forall", hes_mu_forall, Status.Valid);
      ("mu_for_approx", hes_mu_for_approx, Status.Invalid);
    ]

let msg (hes, expected) (_, actual) =
  (sprintf "Case: %s\n" @@ Hesutil.str_of_hes hes)
  ^ (sprintf "Expected: %s\n" @@ Status.string_of expected)
  ^ sprintf "Result: %s\n" @@ Status.string_of actual

let pp_diff formatter (expected, actual) =
  Format.pp_print_string formatter @@ "\n" ^ msg expected actual

(*** Run Tests ***)
let _ =
  run_test_tt_main
    ("solve_onlynu_onlyforall"
    >::: gen_tests ~pp_diff solve_onlynu_onlyforall_tests)

let _ =
  run_test_tt_main
    ("solve_onlymu_onlyexists"
    >::: gen_tests ~pp_diff solve_onlymu_onlyexists_tests)

let _ =
  run_test_tt_main
    ("solve_onlyforall" >::: gen_tests ~pp_diff solve_onlyforall_tests)

let _ =
  run_test_tt_main
    ("simplesolve_onlynu_onlyforall"
    >::: gen_tests ~pp_diff simplesolve_onlynu_onlyforall_tests)

let _ =
  run_test_tt_main
    ("simplesolve_onlymu_onlyexists"
    >::: gen_tests ~pp_diff simplesolve_onlymu_onlyexists_tests)
