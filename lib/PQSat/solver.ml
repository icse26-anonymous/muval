open Core
open Common
open Common.Ext
open Common.Util
open Ast
open Qsat

module Make (Cfg : Config.ConfigType) = struct
  let config = Cfg.config

  module Debug =
    Debug.Make ((val Debug.Config.(if config.verbose then enable else disable)))

  let solve_by_pdr ?(print_sol = false) g =
    Debug.print
    @@ lazy (sprintf "original input: %s\n" @@ LogicOld.Formula.str_of g);
    let g =
      let senv = Set.to_list @@ LogicOld.Formula.sort_env_of g in
      Normalizer.normalize @@ Evaluator.simplify @@ LogicOld.Formula.rm_div_mod
      @@ LogicOld.Formula.elim_ite @@ Normalizer.normalize
      @@ LogicOld.Formula.elim_let
      @@ Normalizer.normalize_let ~rename:true
      @@ LogicOld.Formula.aconv_tvar
      @@ LogicOld.Formula.mk_exists_if_bounded senv g
    in
    Debug.print @@ lazy (sprintf "input: %s\n" (LogicOld.Formula.str_of g));
    let quantifiers, f = LogicOld.Formula.split_quantifiers g in
    match decide_theory quantifiers with
    | LRA ->
        let open QSAT (Mbp.LRA) in
        let p = solve quantifiers f in
        let solution =
          match p with SAT -> SMT.Problem.Sat [] | UNSAT -> SMT.Problem.Unsat
        in
        if print_sol then
          print_endline @@ sprintf "%s" (SMT.Problem.str_of_solution solution);
        Ok solution
    | LIA ->
        let open QSAT (Mbp.LIA) in
        let p = solve quantifiers f in
        let solution =
          match p with SAT -> SMT.Problem.Sat [] | UNSAT -> SMT.Problem.Unsat
        in
        if print_sol then
          print_endline @@ sprintf "%s" (SMT.Problem.str_of_solution solution);
        Ok solution
    | QBF ->
        let open QSAT (Mbp.Boolean) in
        let p = solve quantifiers f in
        let solution =
          match p with SAT -> SMT.Problem.Sat [] | UNSAT -> SMT.Problem.Unsat
        in
        if print_sol then
          print_endline @@ sprintf "%s" (SMT.Problem.str_of_solution solution);
        Ok solution
    | PLRA ->
        (*(try*)
        let open PQSAT_gen (Mbp.LRA) in
        let p = solve quantifiers f 0.5 in
        let solution =
          match p with SAT -> SMT.Problem.Sat [] | UNSAT -> SMT.Problem.Unsat
        in
        if print_sol then
          print_endline @@ sprintf "%s" (SMT.Problem.str_of_solution solution);
        Ok solution
    (*with _ ->
      let open SampleQSAT(LRA) in
      let p = solve quantifiers f 0.5 in
      let solution = match p with SAT -> SMT.Problem.Sat [] | UNSAT -> SMT.Problem.Unsat in
      if print_sol then print_endline @@
        sprintf "%s" (SMT.Problem.str_of_solution solution);
      Ok solution)*)
    | PLIA ->
        let open PQSAT_gen (Mbp.LIA) in
        let p = solve quantifiers f 0.5 in
        let solution =
          match p with SAT -> SMT.Problem.Sat [] | UNSAT -> SMT.Problem.Unsat
        in
        if print_sol then
          print_endline @@ sprintf "%s" (SMT.Problem.str_of_solution solution);
        Ok solution

  let pcsp_solver =
    let open Or_error in
    match config.mode with
    | PDR -> Or_error.error_string "not used"
    | StratSynth cfg ->
        ExtFile.unwrap cfg.pcsp_solver >>= fun cfg ->
        Ok
          (module PCSPSolver.Solver.Make (struct
            let config = cfg
          end) : PCSPSolver.Solver.SolverType)

  let determinize fml chc det params =
    Debug.print @@ lazy "strategy template:";
    Map.Poly.iteri det ~f:(fun ~key ~data:(senv, t) ->
        Debug.print
        @@ lazy
             (sprintf "%s: %s" (Ident.name_of_tvar key)
                (Logic.ExtTerm.str_of_term Map.Poly.empty
                   (Map.force_merge (Map.Poly.of_alist_exn params) senv)
                   t)));
    Debug.print @@ lazy "";
    let chc =
      ( Map.Poly.empty,
        Logic.Term.mk_apps
          (Logic.BoolTerm.mk_imply ())
          [ fml; Logic.BoolTerm.mk_bool false ] )
      :: chc
    in
    let params = PCSP.Params.make @@ Map.Poly.of_alist_exn params in
    let problem = PCSP.Problem.of_formulas ~params (Set.Poly.of_list chc) in
    Debug.print @@ lazy "recursion-free CHC problem for determinization:";
    Debug.print @@ lazy (PCSP.Problem.str_of problem);
    Debug.print @@ lazy "";
    let open Or_error in
    pcsp_solver >>= fun pcsp_solver ->
    let (module PCSPSolver) = pcsp_solver in
    PCSPSolver.solve problem >>= function
    | PCSP.Problem.Sat subs, _num_iters ->
        Debug.print
        @@ lazy
             ("solution:\n" ^ Logic.str_of_term_subst Logic.ExtTerm.str_of subs);
        Ok
          (Map.Poly.map
             ~f:(fun (senv, t) -> (senv, Logic.ExtTerm.subst subs t))
             det)
    | PCSP.Problem.Unsat _, _num_iters -> assert false
    | PCSP.Problem.Unknown, _num_iters -> assert false
    | PCSP.Problem.OutSpace _, _ -> assert false
    | PCSP.Problem.Timeout, _ -> assert false

  let solve =
    let module Z3interface =
      Z3Smt.Z3interfaceNew.Make (Z3Smt.Z3interfaceNew.ExtTerm) in
    fun senv phi -> Z3interface.check_sat [ phi ] senv (Z3.mk_context [])

  let lia_solve_smt f print_sol to_determinize =
    let open StratSynth in
    let f = LIA.formula_of_term f in
    let f = Option.value_exn f in
    Debug.print @@ lazy (sprintf "theory is LIA");
    Debug.print
    @@ lazy (sprintf "input: %s\n" (LIAStrategySynthesis.formula_to_string f));
    let p, s = LIAStrategySynthesis.nondet_strategy_synthesis solve f in
    Debug.print
    @@ lazy
         (sprintf "strategy skelton for %s:\n%s"
            (LIAStrategySynthesis.player_to_string p)
            (LIAStrategySynthesis.ssforest_to_string s));
    let f =
      match p with SAT -> f | UNSAT -> PreFormula.neg_formula LIA.neg_atom f
    in
    (if to_determinize then
       let fml, chc, det, params = LIAStrategySynthesis.loseCHC [] s f in
       match determinize fml chc det params with
       | Ok ds ->
           Debug.print
           @@ lazy
                (sprintf "determinized strategy for %s:"
                   (LIAStrategySynthesis.player_to_string p));
           Map.Poly.iteri ds ~f:(fun ~key ~data:(senv, t) ->
               Debug.print
               @@ lazy
                    (sprintf "%s: %s" (Ident.name_of_tvar key)
                       (Logic.ExtTerm.str_of_term Map.Poly.empty senv t)))
       | Error err -> failwith (Error.to_string_hum err));
    let solution =
      match p with
      | SAT -> SMT.Problem.Sat [] (*ToDo*)
      | UNSAT -> SMT.Problem.Unsat
    in
    Debug.print @@ lazy "=========================";
    if print_sol then
      print_endline @@ sprintf "%s" (SMT.Problem.str_of_solution solution);
    Ok solution

  let lra_solve_smt f print_sol to_determinize =
    let open StratSynth in
    let f = LRA.formula_of_term f in
    let f = Option.value_exn f in
    Debug.print @@ lazy (sprintf "theory is LRA");
    Debug.print
    @@ lazy (sprintf "input: %s\n" (LRAStrategySynthesis.formula_to_string f));
    let p, s = LRAStrategySynthesis.nondet_strategy_synthesis solve f in
    Debug.print
    @@ lazy
         (sprintf "strategy skelton for %s:\n%s"
            (LRAStrategySynthesis.player_to_string p)
            (LRAStrategySynthesis.ssforest_to_string s));
    let f =
      match p with SAT -> f | UNSAT -> PreFormula.neg_formula LRA.neg_atom f
    in
    (if to_determinize then
       let fml, chc, det, params = LRAStrategySynthesis.loseCHC [] s f in
       match determinize fml chc det params with
       | Ok ds ->
           Debug.print
           @@ lazy
                (sprintf "determinized strategy for %s:"
                   (LRAStrategySynthesis.player_to_string p));
           Map.Poly.iteri ds ~f:(fun ~key ~data:(senv, t) ->
               Debug.print
               @@ lazy
                    (sprintf "%s: %s" (Ident.name_of_tvar key)
                       (Logic.ExtTerm.str_of_term Map.Poly.empty senv t)))
       | Error err -> failwith (Error.to_string_hum err));
    let solution =
      match p with
      | SAT -> SMT.Problem.Sat [] (*ToDo*)
      | UNSAT -> SMT.Problem.Unsat
    in
    Debug.print @@ lazy "=========================";
    if print_sol then
      print_endline @@ sprintf "%s" (SMT.Problem.str_of_solution solution);
    Ok solution

  let solve_by_strat_synth determinize ?(print_sol = false) f =
    let senv = Set.to_list @@ LogicOld.Formula.term_sort_env_of f in
    let f =
      Evaluator.simplify @@ LogicOld.Formula.rm_div_mod @@ Normalizer.normalize
      @@ LogicOld.Formula.mk_exists_if_bounded senv
      @@ LogicOld.Formula.aconv_tvar f
    in
    Debug.print
    @@ lazy (sprintf "original input: %s\n" (LogicOld.Formula.str_of f));
    let f = Logic.ExtTerm.of_old_formula f in
    Debug.print
    @@ lazy (sprintf "original input: %s\n" (Logic.ExtTerm.str_of f));
    if Option.is_some @@ StratSynth.LIA.formula_of_term f then
      lia_solve_smt f print_sol determinize
    else lra_solve_smt f print_sol determinize

  let solve =
    match config.mode with
    | PDR -> solve_by_pdr
    | StratSynth cfg -> solve_by_strat_synth cfg.determinize
end

(*module RandomFormula = struct
  let random_affine vars =
    let vars' = None::List.map ~f:(fun x -> Some x) vars in
    let max = 20 in
    List.map ~f:(fun x -> x, Z.of_int (Random.int max - max / 2)) vars' |> Map.Poly.of_alist_exn
  let random_atom_gt0 vars = LIA.Gt0 (random_affine vars)
  let random_atom_div vars = LIA.Div (Z.of_int (Random.int 10 + 1), random_affine vars)
  let random_atom = if Random.bool () then random_atom_gt0 else random_atom_div
  let rec random_formula depth vars var_prefix r =
    let open PreFormula in
    let get_newvar () = let n = !r in r := n + 1; Ident.Tvar (var_prefix ^ string_of_int n) in
    if depth <= 0 then
      Atom (random_atom vars)
    else
      match Random.int 5 with
      | 0 -> Atom (random_atom_gt0 vars)
      | 1 -> And (List.init (Random.int 5) ~f:(fun _ -> random_formula (depth - 1) vars var_prefix r))
      | 2 -> Or (List.init (Random.int 5) ~f:(fun _ -> random_formula (depth - 1) vars var_prefix r))
      | 3 -> let newvar = get_newvar () in Bind (Forall, (newvar, IntTerm.SInt), random_formula (depth - 1) (newvar::vars) var_prefix r)
      | 4 -> let newvar = get_newvar () in Bind (Exists, (newvar, IntTerm.SInt), random_formula (depth - 1) (newvar::vars) var_prefix r)
      | _ -> assert false

  let rec winning ds =
    let open LIAStrategySynthesis in
    let open PreFormula in
    function
    | Atom a -> LIA.term_of_atom a, []
    | And l ->
      let fs, vars = List.map ~f:(winning ds) l |> List.unzip in
      BoolTerm.and_of fs, List.concat vars
    | Or l ->
      let fs, vars = List.map ~f:(winning ds) l |> List.unzip in
      BoolTerm.or_of fs, List.concat vars
    | Bind (Forall, v, f) ->
      let f', vars = winning ds f in
      f', v::vars
    | Bind (Exists, (tvar, _), f) ->
      let f', vars = winning ds f in
      let _, t = Map.Poly.find_exn ds tvar in
      Term.subst (Map.Poly.singleton tvar t) f', vars
  let test n =
    let open LIAStrategySynthesis in
    for _ = 1 to n do
      let depth = Random.int 10 in
      let f = random_formula depth [] "x" (ref 0) in
      printf "input: %s\n" (formula_to_string f);
      let p, s = nondet_strategy_synthesis f in
      printf "%s\n%s\n" (player_to_string p) (ssforest_to_string s);
      let f = match p with SAT -> f | UNSAT -> PreFormula.neg_formula LIA.neg_atom f in
      (match determinize solve_pcsp s f with
       | Ok ds ->
         print_endline "strategy:";
         Map.Poly.iteri ~f:(fun ~key ~data:(senv, t) -> printf "%s: %s\n" (Ident.name_of_tvar key) (Logic.ExtTerm.str_of_term senv t)) ds;
         let win, vars = winning ds f in
         let not_win = BoolTerm.neg_of win in
         let module Z3interface = Z3Smt.Z3interfaceNew.Make(Z3Smt.Z3interfaceNew.ExtTerm) in
         assert (Option.is_none (Z3interface.check_sat [not_win] vars (Z3.mk_context [])))
       | Error _ -> assert false)
    done
  end

  let () =
  let open LIAStrategySynthesis in
  let open PreFormula in
  (match SMT.Smtlib2.from_smt2_file (Sys.get_argv ()).(1) with
   | Ok f ->
     print_endline @@ LogicOld.Formula.str_of f;
     let f = Logic.ExtTerm.of_old_formula f |> LIA.formula_of_term in
     let f = Option.value_exn f in
     printf "input: %s\n" (formula_to_string f);
     let p, s = nondet_strategy_synthesis f in
     printf "%s\n%s\n" (player_to_string p) (ssforest_to_string s);
     let f = match p with SAT -> f | UNSAT -> PreFormula.neg_formula LIA.neg_atom f in
     (match determinize solve_pcsp s f with
      | Ok ds ->
        Map.Poly.iteri ~f:(fun ~key ~data:(senv, t) -> printf "%s: %s\n" (Ident.name_of_tvar key) (Logic.ExtTerm.str_of_term senv t)) ds
      | Error _ -> ())
   | Error _ -> assert false);
  print_string "random test\n";
  Random.self_init ();
  RandomFormula.test 100
*)
