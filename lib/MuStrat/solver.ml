open Core
open Common
open Common.Ext
open Common.Util
open Common.Combinator
open Ast
open MuCLP.Problem
open Preprocessing

module Make (Cfg : Config.ConfigType) = struct
  let config = Cfg.config

  module Debug =
    Debug.Make ((val Debug.Config.(if config.verbose then enable else disable)))

  module Reducer = MuCLP.Reducer.Make ((
    struct
      let config =
        MuCLP.Reducer.Config.{ verbose = config.verbose; use_dwf = true }
    end :
      MuCLP.Reducer.Config.ConfigType))

  module Qelim = MuCLP.Qelim.Make ((
    struct
      let config =
        MuCLP.Qelim.Config.{ verbose = config.verbose; mode = SkolemPred }
    end :
      MuCLP.Qelim.Config.ConfigType))

  let chc_solver () =
    let open Or_error in
    ExtFile.unwrap config.chc_solver >>= fun cfg ->
    PCSPSolver.Solver.(
      Ok
        (module Make (struct
          let config = cfg
        end) : SolverType))

  let chc_timeout = ref 1
  let chc_timeout_backup = ref 1

  let backup_chc_solver () =
    let open Or_error in
    ExtFile.unwrap config.backup_chc_solver >>= fun cfg ->
    PCSPSolver.Solver.(
      Ok
        (module Make (struct
          let config = cfg
        end) : SolverType))

  let pcsp_solver () =
    let open Or_error in
    ExtFile.unwrap config.pcsp_solver >>= fun cfg ->
    PCSPSolver.Solver.(
      Ok
        (module Make (struct
          let config = cfg
        end) : SolverType))

  let optimizer_cfg = ExtFile.unwrap config.optimizer
  let verbose = false

  let preprocess ?(id = None) ?(elim_forall = true) ?(elim_exists = true)
      ?(elim_pvar_args = true) muclp =
    let open Or_error in
    optimizer_cfg >>= fun optimizer_cfg ->
    Ok (MuCLP.Optimizer.make optimizer_cfg)
    >>= fun (module Optimizer : MuCLP.Optimizer.OptimizerType) ->
    let muclp = if config.check_problem then check_problem muclp else muclp in
    Debug.print ~id @@ lazy (sprintf "before optimization: %s\n" @@ str_of muclp);
    let muclp =
      Optimizer.f ~id ~elim_forall ~elim_exists ~elim_pvar_args (simplify muclp)
    in
    Debug.print ~id @@ lazy (sprintf "after optimization: %s\n" @@ str_of muclp);
    Ok muclp

  let to_pfwcsp muclp =
    let unknowns = (Map.Poly.empty, Map.Poly.empty) in
    (* Skolemize quantifiers *)
    if verbose then
      Debug.print @@ lazy (sprintf "Input muCLP: %s\n" @@ str_of muclp);
    let muclp, unknowns =
      Qelim.elim_exists ~forall_dom:true (muclp, unknowns)
    in
    Debug.print ~id:None @@ lazy (sprintf "Skolemized: %s\n" @@ str_of muclp);
    let muclp =
      let pvs = Kind.pred_sort_env_map_of unknowns in
      muclp |> aconv_tvar |> complete_tsort |> complete_psort pvs
    in
    if verbose then
      Debug.print @@ lazy (sprintf "Preprocessed muCLP: %s\n" @@ str_of muclp);
    let pfwcsp =
      Reducer.f ~id:None ~exchange:false ~messenger:None muclp unknowns
      |> PCSP.Problem.add_formulas
         @@ Set.Poly.filter_map
              ~f:(fun (x, s) ->
                if Kind.is_ord @@ Map.Poly.find_exn (snd unknowns) x then
                  let args =
                    Logic.mk_fresh_sort_env_list @@ Logic.Sort.args_of s
                  in
                  let papp =
                    Logic.ExtTerm.mk_var_app x
                      (List.map ~f:(fst >> Logic.ExtTerm.mk_var) args)
                  in
                  Some
                    ( Map.Poly.of_alist_exn args,
                      Logic.BoolTerm.imply_of papp
                        (Logic.BoolTerm.mk_bool false) )
                else None)
              (Map.to_set @@ fst unknowns)
    in
    Debug.print ~id:None
    @@ lazy
         (sprintf "******* Generated pfwCSP:\n%s" @@ PCSP.Problem.str_of pfwcsp);
    pfwcsp |> PCSP.Problem.map ~f:Logic.Term.refresh

  let let_conc t =
    let open Ast.LogicOld in
    if Term.is_var t then
      Formula.mk_atom
      @@ Atom.mk_pvar_app
           (Ident.tvar_to_pvar @@ fst @@ fst @@ Term.let_var t)
           [] []
    else if T_bool.is_formula t then T_bool.let_formula t
    else failwith @@ Term.str_of t

  let rec let_asserted t =
    let open Ast.LogicOld in
    let ts =
      try
        let fvar, _, _, ts, _ = Term.let_fvar_app t in
        assert (String.(Ident.name_of_tvar fvar = "asserted"));
        ts
      with _ ->
        let sym, ts, _ = Term.let_app t in
        Debug.print @@ lazy ("why " ^ Term.str_of_funsym sym);
        ts
    in
    match ts with
    | [ t ] -> let_conc t
    | _ ->
        if T_bool.is_formula t && (Formula.is_eq @@ T_bool.let_formula t) then
          let phi = T_bool.let_formula t in
          let t, _ (*ToDo*), _ = Formula.let_eq phi in
          let_asserted t
        else failwith @@ "let_asserted: " ^ Term.str_of t

  let rec let_hyper_res t =
    let open Ast.LogicOld in
    let ts =
      try
        let fvar, _, _, ts, _ = Term.let_fvar_app t in
        assert (String.(Ident.name_of_tvar fvar = "hyper-res"));
        ts
      with _ ->
        let sym, ts, _ = Term.let_app t in
        Debug.print @@ lazy ("why " ^ Term.str_of_funsym sym);
        ts
    in
    match ts with
    | asserted :: rest ->
        let hress, con = List.rest_last rest in
        (let_asserted asserted, hress, let_conc con)
    | _ ->
        if T_bool.is_formula t && (Formula.is_eq @@ T_bool.let_formula t) then
          let phi = T_bool.let_formula t in
          let t, _ (*ToDo*), _ = Formula.let_eq phi in
          let_hyper_res t
        else failwith @@ "let_hyper_res: " ^ Term.str_of t

  let let_mp phi =
    let open Ast.LogicOld in
    let t, _, _ = Formula.let_eq phi in
    let ts =
      try
        let fvar, _, _, ts, _ = Term.let_fvar_app t in
        assert (String.(Ident.name_of_tvar fvar = "mp"));
        ts
      with _ ->
        let sym, ts, _ = Term.let_app t in
        Debug.print @@ lazy ("why " ^ Term.str_of_funsym sym);
        ts
    in
    match ts with
    | [ ant1; ant2; con ] -> (ant1, let_asserted ant2, let_conc con)
    | _ -> assert false

  let rec analyze_cex hres ren =
    let open Ast.LogicOld in
    let ant, hress, con0 = let_hyper_res hres in
    let senv, ant, _ =
      if Formula.is_forall ant then Formula.let_forall ant else ([], ant, Dummy)
    in
    let (ants1, ants2), con =
      if Formula.is_imply ant then
        let ant, con, _ = Formula.let_imply ant in
        ( List.partition_tf ~f:(fun phi ->
              Formula.is_atom phi
              && (Atom.is_pvar_app @@ fst @@ Formula.let_atom phi))
          @@ Formula.conjuncts_list_of ant,
          con )
      else (([], []), ant)
    in
    let css, ants1 =
      List.unzip
      @@ List.map2_exn hress ants1 ~f:(fun hres ant ->
             let pvs = Formula.pvs_of ant in
             let ren =
               Map.of_set_exn
               @@ Set.Poly.map pvs ~f:(fun pvar ->
                      ( pvar,
                        Ident.mk_fresh_pvar
                          ~prefix:(Some (Ident.name_of_pvar pvar ^ "$"))
                          () ))
             in
             (analyze_cex hres ren, Formula.rename_pvars ren ant))
    in
    let css1, css2 = List.unzip css in
    ( Set.add (Set.Poly.union_list css1)
      @@ Formula.mk_forall_if_bounded senv
      @@ Formula.mk_imply
           (Formula.and_of @@ ants1 @ ants2)
           (Formula.rename_pvars ren con),
      Set.add (Set.Poly.union_list css2) @@ Formula.rename_pvars ren con0 )

  exception NoRefinement

  let solspace =
    ref
      (Map.Poly.of_alist_exn
         [
           (SolSpace.ND, Some 1);
           (SolSpace.NC, Some 1);
           (SolSpace.NP, Some 1);
           (SolSpace.NDC, Some 1);
           (SolSpace.NL, Some 1);
         ])

  let refine_solspace wf fn =
    let f = function
      | None -> None
      | Some None -> Some 1
      | Some (Some n) -> Some (n + 1)
    in
    solspace :=
      if fn then
        Map.Poly.update
          (Map.Poly.update !solspace SolSpace.ND ~f)
          ~f SolSpace.NC
      else !solspace;
    solspace :=
      if wf then
        Map.Poly.update
          (Map.Poly.update
             (Map.Poly.update !solspace SolSpace.NP ~f)
             ~f SolSpace.NDC)
          SolSpace.NL ~f
      else !solspace

  let refine_strat solve cex (primal_strat_wf, primal_strat_fn)
      (dual_strat_wf, dual_strat_fn) =
    let open Ast.LogicOld in
    (*if verbose then*)
    Debug.print @@ lazy (sprintf "cex: %s" (Formula.str_of cex));
    let hres, query, _ = let_mp cex in
    let ren, query =
      let ant, con, _ = Formula.let_imply query in
      let pvs = Formula.pvs_of ant in
      let ren =
        Map.of_set_exn
        @@ Set.Poly.map pvs ~f:(fun pvar ->
               ( pvar,
                 Ident.mk_fresh_pvar
                   ~prefix:(Some (Ident.name_of_pvar pvar ^ "$"))
                   () ))
      in
      (ren, Formula.mk_imply (Formula.rename_pvars ren ant) con)
    in
    let problem, model =
      let cs, model = analyze_cex hres ren in
      let cs = Set.add cs query in
      let model =
        Set.Poly.map model ~f:(fun phi ->
            let pvar, _sorts, ts, _ =
              Atom.let_pvar_app @@ fst @@ Formula.let_atom phi
            in
            (pvar, List.map ~f:Logic.ExtTerm.of_old_term ts))
      in
      let params =
        PCSP.Params.make @@ Logic.of_old_sort_env_map @@ Map.of_set_exn
        @@ Set.concat_map cs
             ~f:(Formula.pred_sort_env_of >> Term.pred_to_sort_env)
      in
      let cs =
        Set.Poly.map cs ~f:(fun phi ->
            let senv, phi = Formula.rm_quant ~forall:true phi in
            (Map.of_set_exn senv, phi))
      in
      (PCSP.Problem.of_old_formulas ~params cs, model)
    in
    let primal_strat_wf', primal_strat_fn' =
      let module Preprocessor = Preprocessor.Make (struct
        let config = Preprocessor.Config.make true false Int.max_value 4 false
      end) in
      let keys_wf = Map.Poly.key_set primal_strat_wf in
      let keys_fn = Map.Poly.key_set primal_strat_fn in
      let senv =
        Map.Poly.filter_keys (PCSP.Problem.senv_of problem) ~f:(fun x ->
            Set.exists (Set.union keys_wf keys_fn) ~f:(fun key ->
                String.is_prefix (Ident.name_of_tvar x)
                  ~prefix:(Ident.name_of_tvar key ^ "$")))
      in
      let bpvs = Map.Poly.key_set senv in
      let _, problem = Preprocessor.preprocess problem ~bpvs in
      let pfwcsp =
        let ren =
          Map.Poly.mapi senv ~f:(fun ~key:x ~data:_ ->
              Set.find_exn (Set.union keys_wf keys_fn) ~f:(fun key ->
                  String.is_prefix (Ident.name_of_tvar x)
                    ~prefix:(Ident.name_of_tvar key ^ "$")))
        in
        let cs =
          PCSP.Problem.clauses_of problem
          |> Set.Poly.map ~f:(Clause.rename ren)
          |> Set.Poly.filter_map ~f:(fun (uni_senv, pos, neg, phi) ->
                 let pos1, pos2 (*empty?*) =
                   Set.partition_tf pos ~f:(fun t ->
                       Set.mem keys_fn (Logic.Term.pvar_of_atom t))
                 in
                 (* ToDo: better to consider primal_strat_fn ? *)
                 let neg1, neg2 (*empty?*) =
                   Set.partition_tf neg ~f:(fun t ->
                       Set.mem keys_wf (Logic.Term.pvar_of_atom t))
                 in
                 let phis_neg =
                   Set.Poly.map neg1 ~f:(Logic.ExtTerm.subst primal_strat_wf)
                 in
                 if Set.is_empty neg1 && Set.is_empty pos1 then None
                 else
                   Some
                     ( uni_senv,
                       Set.union pos2 neg1,
                       Set.union neg2 pos1,
                       Logic.BoolTerm.or_of (phi :: Set.to_list phis_neg) ))
        in
        let params =
          let kind_map =
            Kind.add_kinds keys_wf Kind.WF
              (Kind.add_kinds keys_fn Kind.FN Map.Poly.empty)
          in
          PCSP.Params.make ~kind_map (Map.rename_keys_map ren senv)
        in
        PCSP.Problem.set_params_sol_space
          (PCSP.Problem.of_clauses ~params cs)
          (Map.of_set_exn
          @@ Set.Poly.map (Set.union keys_wf keys_fn) ~f:(fun key ->
                 (key, !solspace)))
      in
      (*if verbose then*)
      Debug.print
      @@ lazy
           (sprintf "\npfwCSP for ranking and Skolem function synthesis:\n%s\n"
           @@ PCSP.Problem.str_of pfwcsp);
      match solve pfwcsp with
      | Result.Ok (PCSP.Problem.Sat sol, _) ->
          ( Map.Poly.mapi primal_strat_wf ~f:(fun ~key ~data ->
                let args, term = Logic.Term.let_lam data in
                match Map.Poly.find sol key with
                | None -> data
                | Some _ ->
                    let phi =
                      Logic.ExtTerm.subst sol
                      @@ Logic.Term.mk_var_app key
                           (List.map args ~f:(fst >> Logic.Term.mk_var))
                    in
                    Debug.print
                    @@ lazy
                         (sprintf "%s(%s) := %s" (Ident.name_of_tvar key)
                            (String.concat_map_list ~sep:","
                               ~f:(fst >> Ident.name_of_tvar)
                               args)
                            (Formula.str_of @@ Evaluator.simplify
                            @@ Logic.ExtTerm.to_old_fml Map.Poly.empty
                                 (Map.Poly.of_alist_exn args)
                                 phi));
                    Logic.Term.mk_lambda args
                    @@ Logic.BoolTerm.or_of [ term; phi ]),
            Map.Poly.mapi primal_strat_fn ~f:(fun ~key ~data ->
                let args, term = Logic.Term.let_lam data in
                match Map.Poly.find sol key with
                | None -> data
                | Some _ ->
                    let phi =
                      Logic.ExtTerm.subst sol
                      @@ Logic.Term.mk_var_app key
                           (List.map args ~f:(fst >> Logic.Term.mk_var))
                    in
                    Debug.print
                    @@ lazy
                         (sprintf "%s(%s) := %s" (Ident.name_of_tvar key)
                            (String.concat_map_list ~sep:","
                               ~f:(fst >> Ident.name_of_tvar)
                               args)
                            (Formula.str_of @@ Evaluator.simplify
                            @@ Logic.ExtTerm.to_old_fml Map.Poly.empty
                                 (Map.Poly.of_alist_exn args)
                                 phi));
                    Logic.Term.mk_lambda args
                    @@ Logic.BoolTerm.or_of [ term; phi ]) )
      | Result.Ok (PCSP.Problem.Unsat _, _) -> raise NoRefinement
      | Result.Ok ((PCSP.Problem.(Unknown | Timeout) as sol), _) ->
          Debug.print @@ lazy (PCSP.Problem.str_of_sol_with_witness sol);
          (primal_strat_wf, primal_strat_fn)
      | Result.Ok ((PCSP.Problem.OutSpace xs as sol), _) ->
          Debug.print @@ lazy (PCSP.Problem.str_of_sol_with_witness sol);
          refine_solspace
            (List.exists xs ~f:(Map.Poly.mem primal_strat_wf))
            (List.exists xs ~f:(Map.Poly.mem primal_strat_fn));
          (primal_strat_wf, primal_strat_fn)
      | Result.Error _ ->
          Debug.print @@ lazy "error";
          (primal_strat_wf, primal_strat_fn (*failwith "refine_strat"*))
    in
    let dual_strat_fn' =
      Map.Poly.mapi dual_strat_fn ~f:(fun ~key ~data ->
          let args, term = Logic.Term.let_lam data in
          let rs =
            Set.filter model ~f:(fun (x, _ts) ->
                String.is_prefix (Ident.name_of_pvar x)
                  ~prefix:(Ident.name_of_tvar key ^ "$"))
          in
          if Set.is_empty rs then data
          else
            let t =
              Logic.BoolTerm.or_of @@ Set.to_list
              @@ Set.Poly.map rs ~f:(fun (_, ts) ->
                     Logic.BoolTerm.and_of
                       (List.map2_exn args ts ~f:(fun (x, s) t ->
                            Logic.BoolTerm.eq_of s (Logic.ExtTerm.mk_var x) t)))
            in
            Debug.print
            @@ lazy
                 (sprintf "%s(%s) := %s" (Ident.name_of_tvar key)
                    (String.concat_map_list ~sep:","
                       ~f:(fst >> Ident.name_of_tvar)
                       args)
                    (Formula.str_of @@ Evaluator.simplify
                    @@ Logic.ExtTerm.to_old_fml Map.Poly.empty
                         (Map.Poly.of_alist_exn args)
                         t));
            Logic.Term.mk_lambda args
              (Logic.BoolTerm.or_of [ term; t (*ToDo*) ]))
    in
    ((primal_strat_wf', primal_strat_fn'), (dual_strat_wf, dual_strat_fn'))

  let rec solve_primal_dual turn ((primal_strat_wf, primal_strat_fn), primal)
      ((dual_strat_wf, dual_strat_fn), dual) =
    let open Or_error.Monad_infix in
    chc_solver () >>= fun (module CHCSolver) ->
    backup_chc_solver () >>= fun (module CHCSolverBackUp) ->
    pcsp_solver () >>= fun (module PCSPSolver) ->
    let chc =
      primal
      |> PCSP.Problem.map_params ~f:(fun params ->
             {
               params with
               kind_map =
                 Map.Poly.map params.kind_map ~f:(function
                   | Kind.FN | Kind.DWF -> Kind.Ord
                   | k -> k);
             })
      |> PCSP.Problem.subst ~elim:false (*ToDo*)
           (Map.Poly.mapi primal_strat_fn ~f:(fun ~key ~data ->
                let params, _ = Logic.Term.let_lam data in
                let args = List.map params ~f:(fst >> Logic.ExtTerm.mk_var) in
                Logic.ExtTerm.mk_lambda params
                @@ Logic.BoolTerm.neg_of
                @@ Logic.ExtTerm.mk_var_app key args))
      |> PCSP.Problem.add_formulas
         @@ Set.Poly.map (Map.to_set primal_strat_fn) ~f:(fun (x, t) ->
                let args, t' = Logic.Term.let_lam t in
                let papp =
                  Logic.ExtTerm.mk_var_app x
                    (List.map ~f:(fst >> Logic.ExtTerm.mk_var) args)
                in
                ( Map.Poly.of_alist_exn args,
                  Logic.BoolTerm.imply_of papp (Logic.BoolTerm.neg_of t') ))
      |> PCSP.Problem.add_formulas
         @@ Set.Poly.map (Map.to_set primal_strat_wf) ~f:(fun (x, t) ->
                let args, t' = Logic.Term.let_lam t in
                let papp =
                  Logic.ExtTerm.mk_var_app x
                    (List.map ~f:(fst >> Logic.ExtTerm.mk_var) args)
                in
                (Map.Poly.of_alist_exn args, Logic.BoolTerm.imply_of papp t'))
      |> PCSP.Problem.cochc_to_chc
    in
    Debug.print
    @@ lazy
         (sprintf
            "\n\
             checking whether the current %s strategy is winning via CHC \
             solving (%d sec.)"
            (if turn then "primal" else "dual")
            !chc_timeout);
    if verbose then
      Debug.print @@ lazy (sprintf "%s\n" @@ PCSP.Problem.str_of chc);
    CHCSolver.solve ~timeout:(Some !chc_timeout) chc >>= function
    | PCSP.Problem.Sat _, _ -> Ok Valid
    | Unsat (Some cex), _ -> (
        try
          let primal_strat, dual_strat =
            refine_strat PCSPSolver.solve cex
              (primal_strat_wf, primal_strat_fn)
              (dual_strat_wf, dual_strat_fn)
          in
          Debug.print
          @@ lazy
               ("strategy refined and pass the turn to "
               ^ (if turn then "dual" else "primal")
               ^ "\n");
          solve_primal_dual (not turn) (dual_strat, dual) (primal_strat, primal)
          >>= fun s -> Ok (MuCLP.Problem.flip_solution s)
        with NoRefinement -> Ok Invalid)
    | Unsat None, _ ->
        Debug.print
        @@ lazy
             ("no cex obtained and pass the turn to "
             ^ (if turn then "dual" else "primal")
             ^ "\n");
        solve_primal_dual (not turn)
          ((dual_strat_wf, dual_strat_fn), dual)
          ((primal_strat_wf, primal_strat_fn), primal)
        >>= fun s -> Ok (MuCLP.Problem.flip_solution s)
    | Unknown, _ -> (
        Debug.print
        @@ lazy
             (sprintf
                "\n\
                 checking again whether the current %s strategy is winning via \
                 CHC solving (%d sec.)"
                (if turn then "primal" else "dual")
                !chc_timeout_backup);
        CHCSolverBackUp.solve ~timeout:(Some !chc_timeout_backup) chc
        >>= function
        | PCSP.Problem.Sat _, _ -> Ok Valid
        | Unsat (Some cex), _ -> (
            try
              let primal_strat, dual_strat =
                refine_strat PCSPSolver.solve cex
                  (primal_strat_wf, primal_strat_fn)
                  (dual_strat_wf, dual_strat_fn)
              in
              Debug.print
              @@ lazy
                   ("strategy refined and pass the turn to "
                   ^ (if turn then "dual" else "primal")
                   ^ "\n");
              solve_primal_dual (not turn) (dual_strat, dual)
                (primal_strat, primal)
              >>= fun s -> Ok (MuCLP.Problem.flip_solution s)
            with NoRefinement -> Ok Invalid)
        | Unsat None, _ ->
            Debug.print
            @@ lazy
                 ("no cex obtained and pass the turn to "
                 ^ (if turn then "dual" else "primal")
                 ^ "\n");
            solve_primal_dual (not turn)
              ((dual_strat_wf, dual_strat_fn), dual)
              ((primal_strat_wf, primal_strat_fn), primal)
            >>= fun s -> Ok (MuCLP.Problem.flip_solution s)
        | Unknown, _ ->
            Debug.print
            @@ lazy
                 ("unknown result and pass the turn to "
                 ^ (if turn then "dual" else "primal")
                 ^ "\n");
            solve_primal_dual (not turn)
              ((dual_strat_wf, dual_strat_fn), dual)
              ((primal_strat_wf, primal_strat_fn), primal)
            >>= fun s -> Ok (MuCLP.Problem.flip_solution s)
        | Timeout, _ ->
            chc_timeout_backup := !chc_timeout_backup * 2;
            Debug.print
            @@ lazy
                 ("timeout and pass the turn to "
                 ^ (if turn then "dual" else "primal")
                 ^ "\n");
            solve_primal_dual (not turn)
              ((dual_strat_wf, dual_strat_fn), dual)
              ((primal_strat_wf, primal_strat_fn), primal)
            >>= fun s -> Ok (MuCLP.Problem.flip_solution s)
        | OutSpace _, _ -> failwith "out of space" (* TODO *))
    | Timeout, _ ->
        chc_timeout := !chc_timeout * 2;
        Debug.print
        @@ lazy
             ("timeout and pass the turn to "
             ^ (if turn then "dual" else "primal")
             ^ "\n");
        solve_primal_dual (not turn)
          ((dual_strat_wf, dual_strat_fn), dual)
          ((primal_strat_wf, primal_strat_fn), primal)
        >>= fun s -> Ok (MuCLP.Problem.flip_solution s)
    | OutSpace _, _ -> failwith "out of space" (* TODO *)

  let init_strat_of pfwcsp =
    let dwfpvs_senv = PCSP.Problem.dwfpvs_senv_of pfwcsp in
    let fnpvs_senv = PCSP.Problem.fnpvs_senv_of pfwcsp in
    ( Map.Poly.map dwfpvs_senv ~f:(fun sort ->
          let args, ret = Logic.Sort.args_ret_of sort in
          assert (Logic.BoolTerm.is_bool_sort ret);
          let params = Logic.sort_env_list_of_sorts args in
          Logic.ExtTerm.mk_lambda params @@ Logic.BoolTerm.mk_bool false),
      Map.Poly.map fnpvs_senv ~f:(fun sort ->
          let args, ret = Logic.Sort.args_ret_of sort in
          assert (Logic.BoolTerm.is_bool_sort ret);
          let params = Logic.sort_env_list_of_sorts args in
          let args, ret = List.rest_last params in
          Logic.ExtTerm.mk_lambda params
          @@ Logic.BoolTerm.or_of
          @@ List.map ~f:(fun t ->
                 Logic.BoolTerm.eq_of (snd ret)
                   (Logic.ExtTerm.mk_var (fst ret))
                   t)
          @@ Logic.ExtTerm.mk_dummy (snd ret)
             :: List.filter_map args ~f:(fun (x, s) ->
                    if Stdlib.(s = snd ret) then Some (Logic.ExtTerm.mk_var x)
                    else None)) )

  let solve ?(print_sol = false) muclp =
    let open Or_error.Monad_infix in
    Debug.print @@ lazy "======== MuStrat ========";
    Debug.print @@ lazy "-=-=-=-= proving/disproving -=-=-=-=";
    preprocess ~elim_forall:true ~elim_exists:true ~elim_pvar_args:true muclp
    >>= fun muclp ->
    let primal =
      (*PCSP.Problem.to_cnf @@ PCSP.Problem.to_nnf @@*) to_pfwcsp muclp
    in
    let dual =
      (*PCSP.Problem.to_cnf @@ PCSP.Problem.to_nnf @@*)
      to_pfwcsp (MuCLP.Util.get_dual muclp)
    in
    Debug.print
    @@ lazy (sprintf "\nPrimal Problem:\n%s\n" @@ PCSP.Problem.str_of primal);
    Debug.print
    @@ lazy (sprintf "Dual Problem:\n%s\n" @@ PCSP.Problem.str_of dual);
    solve_primal_dual true
      (init_strat_of primal, primal)
      (init_strat_of dual, dual)
    >>= function
    | sol ->
        Debug.print @@ lazy "=========================";
        if print_sol then
          print_endline
          @@ sprintf "%s"
               ((if config.output_yes_no then lts_str_of_solution
                 else str_of_solution)
                  sol);
        Or_error.return (sol, -1, "" (*ToDo*))

  let solve_pcsp ?(print_sol = false) pcsp =
    let (module Preprocessor : Preprocessor.PreprocessorType) =
      Preprocessor.(make @@ Config.make true config.verbose 4 4 true)
    in
    Debug.print
    @@ lazy "************* converting pfwCSP to muCLP ***************";
    Preprocessor.solve
      (fun ?oracle pcsp ->
        ignore oracle;
        let open Or_error.Monad_infix in
        solve ~print_sol:false (MuCLP.Util.of_chc ~print:Debug.print pcsp)
        >>= fun (sol, _, _) ->
        let sol =
          match sol with
          | Valid -> PCSP.Problem.Sat Map.Poly.empty (* ToDo *)
          | Invalid -> PCSP.Problem.Unsat None (* ToDo *)
          | Unknown -> PCSP.Problem.Unknown
          | Timeout -> PCSP.Problem.Timeout
        in
        if print_sol then
          print_endline @@ sprintf "%s" (PCSP.Problem.str_of_solution sol);
        Or_error.return (sol, { PCSatCommon.State.num_cegis_iters = -1 }))
      pcsp
end
