open Core
open Common.Ext
open Common.Combinator
open Ast
open Ast.LogicOld

type theory = QBF | LRA | LIA | PLRA | PLIA

let decide_theory quantifiers =
  let sortlist =
    List.fold quantifiers ~init:[] ~f:(fun l (_binder, sortenv) ->
        let _, sort = List.unzip sortenv in
        l @ sort)
  in
  let rec loop theory = function
    | [] -> theory
    | T_bool.SBool :: tl -> loop theory tl
    | T_real.SReal :: tl -> (
        match theory with QBF | LRA -> loop LRA tl | _ -> assert false)
    | T_int.SInt :: tl -> (
        match theory with QBF | LIA -> loop LIA tl | _ -> assert false)
    | _ -> assert false
  in
  let theory = loop QBF sortlist in
  if List.exists quantifiers ~f:(fst >> Formula.is_random) then
    match theory with LRA -> PLRA | LIA -> PLIA | _ -> assert false
  else theory

let level_exists atom vlevel =
  Set.fold (Atom.tvs_of atom) ~init:Z.zero ~f:(fun level tvar ->
      match Map.Poly.find vlevel tvar with
      | Some (l, _) -> if Z.is_odd l then Z.max level l else level
      | None -> level)

let level_forall atom vlevel =
  Set.fold (Atom.tvs_of atom) ~init:Z.zero ~f:(fun level tvar ->
      match Map.Poly.find vlevel tvar with
      | Some (l, _) -> if Z.is_even l then Z.max level l else level
      | None -> level)

let level_j j atom vlevel =
  if Z.is_odd j then level_exists atom vlevel else level_forall atom vlevel

let rec level_j_atomterm j vlevel = function
  | Formula.Atom (a, _) -> level_j j a vlevel
  | UnaryOp (Not, phi, _) -> level_j_atomterm j vlevel phi
  | _ -> assert false

let strategy model j atoms vlevel =
  if Map.Poly.is_empty model then [ Atom.mk_true () ]
  else
    let atoms =
      Set.filter atoms ~f:(fun a ->
          Z.Compare.(level_j j a vlevel <= Z.(j - Z.of_int 2)))
    in
    List.map (Set.to_list atoms) ~f:(Mbp.sign model)

let rec bool_var_atom = function
  | Formula.Atom (App (Predicate.Var (x, _), [], _), _) ->
      First (Atom.of_bool_var (Ident.pvar_to_tvar x))
  | UnaryOp (Not, Atom (App (Predicate.Var (x, _), [], _), _), _) ->
      First (Atom.of_neg_bool_var (Ident.pvar_to_tvar x))
  | UnaryOp (Not, UnaryOp (Not, phi, _), _) -> bool_var_atom phi
  | Atom (atm, _) -> Second atm
  | UnaryOp (Not, Atom (atm, _), _) ->
      Second
        (match Atom.negate atm with
        | None -> failwith "[bool_var_atom]"
        | Some neg_atm -> neg_atm)
  | _ -> assert false

(*This QSAT supports bool, LIA and LRA.*)
module QSAT (A : sig
  val let_sort : string Set.Poly.t -> TermSubst.t -> TermSubst.t

  val model_based_projection :
    TermSubst.t -> Ident.tvar -> Atom.t Set.Poly.t -> Atom.t Set.Poly.t
end) =
struct
  open Formula

  type player = SAT | UNSAT

  let rec level_of level = function
    | [] -> Map.Poly.empty
    | (Exists, sortenv) :: tl ->
        let level = if Z.is_odd level then level else Z.succ level in
        let map =
          Map.Poly.map (Map.Poly.of_alist_exn sortenv) ~f:(fun s -> (level, s))
        in
        Map.force_merge map (level_of level tl)
    | (Forall, sortenv) :: tl ->
        let level = if Z.is_even level then level else Z.succ level in
        let map =
          Map.Poly.map (Map.Poly.of_alist_exn sortenv) ~f:(fun s -> (level, s))
        in
        Map.force_merge map (level_of level tl)
    | (Random _, _) :: _ -> assert false

  let add_dontcare model vlevel =
    Map.Poly.fold vlevel ~init:model ~f:(fun ~key ~data:(_, sort) model ->
        match Map.Poly.find model key with
        | Some _ -> model
        | None -> Map.Poly.add_exn model ~key ~data:(Term.mk_dummy sort))

  let tail j vlevel =
    Map.Poly.filter vlevel ~f:(fun (level, _) ->
        Z.Compare.(level >= Z.(j - Z.one)))

  let rec mbp model j vlevel core =
    let core, bcore =
      Set.fold core ~init:(Set.Poly.empty, Set.Poly.empty)
        ~f:(fun (c, bc) phi ->
          match bool_var_atom phi with
          | First phi' -> (c, Set.add bc phi')
          | Second atm -> (Set.add c atm, bc))
    in
    if false then (
      print_endline
        ("core: " ^ List.to_string ~f:Atom.str_of @@ Set.to_list core);
      print_endline
        ("bcore: " ^ List.to_string ~f:Atom.str_of @@ Set.to_list bcore);
      print_endline "");
    let mbp_theory model tail phis bphis =
      let phis, bphis =
        Map.Poly.fold tail ~init:(phis, bphis)
          ~f:(fun ~key:tvar ~data:(_, sort) (phis, bphis) ->
            if Term.is_bool_sort sort then
              (phis, Mbp.Boolean.model_based_projection model tvar bphis)
            else (A.model_based_projection model tvar phis, bphis))
      in
      Set.union phis bphis
    in
    let tail = tail j vlevel in
    let jformulas =
      Set.Poly.map ~f:Evaluator.simplify_atom
      @@ mbp_theory model tail core bcore
    in
    let index = if Z.is_odd j then Z.one else Z.of_int 2 in
    let index =
      Set.fold jformulas ~init:index ~f:(fun i jterm ->
          Z.max i (level_j_atomterm j vlevel jterm))
    in
    if Z.Compare.(index = Z.(j - Z.of_int 2)) then
      (and_of @@ Set.to_list jformulas, index)
    else mbp model Z.(index + Z.of_int 2) vlevel jformulas

  let update_formulas formulas atoms j jformula =
    let newformulas =
      if Z.is_odd j then
        Map.Poly.mapi formulas ~f:(fun ~key ~data ->
            if Z.Compare.(key < j) then data
            else if Z.is_odd key then mk_and data (negate jformula)
            else data)
      else
        Map.Poly.mapi formulas ~f:(fun ~key ~data ->
            if Z.Compare.(key < j) then data
            else if Z.is_even key then mk_and data (negate jformula)
            else data)
    in
    let newatoms =
      let pos, neg = atoms_of jformula in
      Set.Poly.union_list [ atoms; pos; neg ]
    in
    (newformulas, newatoms)

  let solve quantifiers f =
    let open Z3Smt.Z3interface in
    if false then (
      List.iter quantifiers ~f:(fun (binder, sortenv) ->
          print_string
            (str_of_binder binder
            ^ str_of_sort_env_list Term.str_of_sort sortenv
            ^ " "));
      print_endline "";
      print_endline (str_of f));
    let vlevel = level_of Z.one quantifiers in
    let clausenames = Set.Poly.singleton "main" in
    let formulas =
      Map.Poly.add_exn
        (Map.Poly.singleton Z.one f)
        ~key:(Z.of_int 2) ~data:(negate f)
    in
    let atoms =
      let pos, neg = atoms_of f in
      Set.union pos neg
    in
    let fenv = Map.Poly.empty in
    (*TODO: generate fenv*)
    let rec loop model j formulas atoms clausenames =
      let formula = Map.Poly.find_exn formulas j in
      let str = strategy model j atoms vlevel in
      if false then (
        print_endline (Z.to_string j);
        print_endline ("Formula: " ^ str_of formula);
        print_endline ("Strategy: " ^ List.to_string ~f:Atom.str_of str));
      let pvar_clause_map, clausenames =
        List.foldi str
          ~init:(Map.Poly.singleton "main" formula, clausenames)
          ~f:(fun i (map, names) phi ->
            let name = "|#S_" ^ string_of_int i ^ "|" in
            let names = Set.add names name in
            (Map.Poly.add_exn map ~key:name ~data:(Formula.mk_atom phi), names))
      in
      match check_sat_unsat_core ~id:None fenv pvar_clause_map with
      | `Unsat core ->
          if Z.Compare.(j = Z.one) then UNSAT
          else if Z.Compare.(j = Z.of_int 2) then SAT
          else
            let core =
              List.filter_opt
              @@ List.map core ~f:(function
                   | "main" -> None
                   | v -> Map.Poly.find pvar_clause_map v)
            in
            let jformula, j = mbp model j vlevel (Set.Poly.of_list core) in
            let jformula =
              Evaluator.simplify @@ Normalizer.normalize jformula
            in
            if false then (
              print_endline ("core: " ^ List.to_string ~f:str_of core);
              print_endline ("jformula: " ^ str_of jformula));
            let formulas, atoms = update_formulas formulas atoms j jformula in
            loop Map.Poly.empty j formulas atoms clausenames
      | `Sat model ->
          let model =
            remove_dontcare model |> Map.Poly.of_alist_exn
            |> A.let_sort clausenames
          in
          let model = add_dontcare model vlevel in
          if false then print_endline ("model: " ^ TermSubst.str_of model);
          let formulas =
            Map.Poly.update formulas (Z.succ j) ~f:(function
              | Some phi -> phi
              | None -> Map.Poly.find_exn formulas (Z.pred j))
          in
          loop model (Z.succ j) formulas atoms clausenames
      | _ -> assert false
    in
    loop Map.Poly.empty Z.one formulas atoms clausenames
end

(*sample based algorithm*)
module SampleQSAT (A : sig
  val let_sort : string Set.Poly.t -> TermSubst.t -> TermSubst.t

  val model_based_projection :
    TermSubst.t -> Ident.tvar -> Atom.t Set.Poly.t -> Atom.t Set.Poly.t
end) =
struct
  open Formula

  type player = SAT | UNSAT

  let rec level_of level = function
    | [] -> (Map.Poly.empty, Map.Poly.empty)
    | (Exists, sortenv) :: tl ->
        let level = if Z.is_odd level then level else Z.succ level in
        let map =
          List.fold sortenv ~init:Map.Poly.empty ~f:(fun map (tvar, sort) ->
              Map.Poly.add_exn map ~key:tvar ~data:(level, sort))
        in
        let vlevel, plevel = level_of level tl in
        (Map.force_merge map vlevel, plevel)
    | (Forall, sortenv) :: tl ->
        let level =
          if Z.Compare.(level = Z.zero) then Z.of_int 2
          else if Z.is_even level then level
          else Z.succ level
        in
        let map =
          List.fold sortenv ~init:Map.Poly.empty ~f:(fun map (tvar, sort) ->
              Map.Poly.add_exn map ~key:tvar ~data:(level, sort))
        in
        let vlevel, plevel = level_of level tl in
        (Map.force_merge map vlevel, plevel)
    | (Random r, sortenv) :: tl ->
        let level = Z.succ level in
        let map =
          List.fold sortenv ~init:Map.Poly.empty ~f:(fun map (tvar, _sort) ->
              Map.Poly.add_exn map ~key:tvar ~data:(level, r))
        in
        let vlevel, plevel = level_of level tl in
        (vlevel, Map.force_merge map plevel)

  let add_dontcare model vlevel plevel =
    let model =
      Map.Poly.fold vlevel ~init:model ~f:(fun ~key ~data:(_, sort) model ->
          match Map.Poly.find model key with
          | Some _ -> model
          | None -> Map.Poly.add_exn model ~key ~data:(Term.mk_dummy sort))
    in
    Map.Poly.fold plevel ~init:model ~f:(fun ~key ~data:(_, rand) model ->
        match Map.Poly.find model key with
        | Some _ -> model
        | None ->
            Map.Poly.add_exn model ~key
              ~data:(Term.mk_dummy (Rand.sort_of rand)))

  let level_random atom plevel =
    Set.fold (Atom.tvs_of atom) ~init:Z.zero ~f:(fun level tvar ->
        match Map.Poly.find plevel tvar with
        | Some (l, _) -> Z.max level l
        | None -> level)

  let tail j vlevel plevel =
    let t1 =
      Map.Poly.filter vlevel ~f:(fun (level, _) ->
          Z.Compare.(level >= Z.(j - Z.one)))
    in
    let t2 =
      Map.Poly.fold plevel ~init:Map.Poly.empty
        ~f:(fun ~key ~data:(level, rand) map ->
          if Z.Compare.(level >= Z.(j - Z.one)) then
            Map.Poly.add_exn map ~key ~data:(level, Rand.sort_of rand)
          else map)
    in
    Map.force_merge t1 t2

  let rec mbp model j vlevel plevel core =
    let core, bcore =
      Set.fold core ~init:(Set.Poly.empty, Set.Poly.empty)
        ~f:(fun (c, bc) phi ->
          match bool_var_atom phi with
          | First phi' -> (c, Set.add bc phi')
          | Second atm -> (Set.add c atm, bc))
    in
    if false then (
      print_endline
        ("core: " ^ List.to_string ~f:Atom.str_of @@ Set.to_list core);
      print_endline
        ("bcore: " ^ List.to_string ~f:Atom.str_of @@ Set.to_list bcore);
      print_endline "");
    let mbp_theory model tail phis bphis =
      let phis, bphis =
        Map.Poly.fold tail ~init:(phis, bphis)
          ~f:(fun ~key:tvar ~data:(_, _sort) (phis, bphis) ->
            if Term.is_bool_sort T_bool.SBool then
              (phis, Mbp.Boolean.model_based_projection model tvar bphis)
            else (A.model_based_projection model tvar phis, bphis))
      in
      Set.union phis bphis
    in
    let tail = tail j vlevel plevel in
    let jformulas =
      Set.Poly.map ~f:Evaluator.simplify_atom
      @@ mbp_theory model tail core bcore
    in
    let index = if Z.is_odd j then Z.one else Z.of_int 2 in
    let index =
      Set.fold jformulas ~init:index ~f:(fun i jterm ->
          Z.max i (level_j_atomterm j vlevel jterm))
    in
    if Z.Compare.(index = Z.(j - Z.of_int 2)) then
      (and_of @@ Set.to_list jformulas, index)
    else mbp model Z.(index + Z.of_int 2) vlevel plevel jformulas

  let update_formulas formulas atoms j jformula =
    let newformulas =
      if Z.is_odd j then
        Map.Poly.mapi formulas ~f:(fun ~key ~data ->
            if Z.Compare.(key < j) then data
            else if Z.is_odd key then mk_and data (negate jformula)
            else data)
      else
        Map.Poly.mapi formulas ~f:(fun ~key ~data ->
            if Z.Compare.(key < j) then data
            else if Z.is_even key then mk_and data (negate jformula)
            else data)
    in
    let newatoms =
      let pos, neg = atoms_of jformula in
      Set.Poly.union_list [ atoms; pos; neg ]
    in
    (newformulas, newatoms)

  let solve quantifiers f theta =
    let open Z3Smt.Z3interface in
    print_endline "sampleQSAT";
    if false then (
      List.iter quantifiers ~f:(fun (binder, sortenv) ->
          print_string
            (str_of_binder binder
            ^ str_of_sort_env_list Term.str_of_sort sortenv
            ^ " "));
      print_endline "");
    let vlevel, plevel = level_of Z.zero quantifiers in
    let clausenames = Set.Poly.singleton "main" in
    let theta = Q.of_float theta in
    let fenv = Map.Poly.empty in
    (*TODO: generate fenv*)
    let rec loop model i j k formulas atoms clausenames =
      if Z.Compare.(i = j) then
        let vars =
          Map.Poly.fold plevel ~init:[]
            ~f:(fun ~key:tvar ~data:(level, rand) l ->
              if Z.Compare.(i = level) then (tvar, rand) :: l else l)
        in
        if List.is_empty vars then
          loop model (Z.succ i) j k formulas atoms clausenames
        else
          let vars =
            List.map vars ~f:(fun (tvar, rand) ->
                let rand = Rand.subst model rand in
                (tvar, rand))
          in
          let vars =
            List.map vars ~f:(fun (tvar, rand) ->
                let samples = Mcmc.samp rand in
                (tvar, samples))
          in
          let sat, unsat, satmodel, unsatmodel =
            compute vars model i j formulas atoms
          in
          let late = Q.make sat Z.(sat + unsat) in
          if Q.(late >= theta) then
            if Z.Compare.(i <= Z.of_int 2) then SAT
            else
              let j = if Z.is_odd i then Z.pred i else Z.(i - Z.of_int 2) in
              let tempcore = strategy satmodel j atoms vlevel in
              let jformula, j =
                mbp satmodel j vlevel plevel
                  (Set.Poly.of_list @@ List.map ~f:Formula.mk_atom tempcore)
              in
              if Z.Compare.(j < k) then SAT
              else
                let formulas, atoms =
                  update_formulas formulas atoms j jformula
                in
                loop Map.Poly.empty (Z.succ j) j k formulas atoms clausenames
          else if Z.Compare.(i <= Z.one) then UNSAT
          else
            let j = if Z.is_even i then Z.pred i else Z.(i - Z.of_int 2) in
            let tempcore = strategy unsatmodel j atoms vlevel in
            let jformula, j =
              mbp unsatmodel j vlevel plevel
                (Set.Poly.of_list @@ List.map ~f:Formula.mk_atom tempcore)
            in
            if Z.Compare.(j < k) then UNSAT
            else
              let formulas, atoms = update_formulas formulas atoms j jformula in
              loop Map.Poly.empty (Z.succ j) j k formulas atoms clausenames
      else
        let formula = Map.Poly.find_exn formulas j in
        let str = strategy model j atoms vlevel in
        if false then (
          print_endline (Z.to_string j);
          print_endline ("Formula: " ^ str_of formula);
          print_endline ("Strategy: " ^ List.to_string ~f:Atom.str_of str));
        let samplemodel =
          Map.Poly.filter_keys model ~f:(fun tvar ->
              match Map.Poly.find plevel tvar with
              | Some (level, _) -> Z.Compare.(level < i)
              | None -> false)
        in
        let formula = subst samplemodel formula in
        let str = List.map str ~f:(Formula.mk_atom >> subst samplemodel) in
        let pvar_clause_map, clausenames =
          List.foldi str
            ~init:(Map.Poly.singleton "main" formula, clausenames)
            ~f:(fun n (map, names) phi ->
              let name = "|#S_" ^ string_of_int n ^ "|" in
              let names = Set.add names name in
              (Map.Poly.add_exn map ~key:name ~data:phi, names))
        in
        match check_sat_unsat_core ~id:None fenv pvar_clause_map with
        | `Unsat core ->
            if Z.Compare.(j = Z.one) then UNSAT
            else if Z.Compare.(j = Z.of_int 2) then SAT
            else
              let core =
                List.filter_opt
                @@ List.map core ~f:(function
                     | "main" -> None
                     | v -> Map.Poly.find pvar_clause_map v)
              in
              let jformula, j =
                mbp model j vlevel plevel (Set.Poly.of_list core)
              in
              if Z.Compare.(j < k) then if Z.is_odd j then UNSAT else SAT
              else (
                if false then (
                  print_endline ("core: " ^ List.to_string ~f:str_of core);
                  print_endline ("jformula: " ^ str_of jformula));
                let formulas, atoms =
                  update_formulas formulas atoms j jformula
                in
                loop Map.Poly.empty (Z.succ j) j k formulas atoms clausenames)
        | `Sat model ->
            let model =
              remove_dontcare model |> Map.Poly.of_alist_exn
              |> A.let_sort clausenames
            in
            let model =
              add_dontcare (Map.force_merge model samplemodel) vlevel plevel
            in
            if false then print_endline ("model: " ^ TermSubst.str_of model);
            let formulas =
              Map.Poly.update formulas (Z.succ j) ~f:(function
                | Some phi -> phi
                | None -> Map.Poly.find_exn formulas (Z.pred j))
            in
            loop model i (Z.succ j) k formulas atoms clausenames
        | _ -> assert false
    and compute vars model i j formulas atoms =
      match vars with
      | [] -> (
          match loop model (Z.succ i) j i formulas atoms clausenames with
          | SAT -> (Z.one, Z.zero, model, Map.Poly.empty)
          | UNSAT -> (Z.zero, Z.one, Map.Poly.empty, model))
      | (tvar, qset) :: tl ->
          Set.fold qset ~init:(Z.zero, Z.zero, Map.Poly.empty, Map.Poly.empty)
            ~f:(fun (sat, unsat, satmodel, unsatmodel) r ->
              let rterm = T_real.mk_real r in
              let model = Map.Poly.update model tvar ~f:(fun _ -> rterm) in
              let sat', unsat', satmodel', unsatmodel' =
                compute tl model i j formulas atoms
              in
              let satmodel =
                if Map.Poly.is_empty satmodel' then satmodel else satmodel'
              in
              let unsatmodel =
                if Map.Poly.is_empty unsatmodel' then unsatmodel
                else unsatmodel'
              in
              (Z.(sat + sat'), Z.(unsat + unsat'), satmodel, unsatmodel))
    in
    let formulas =
      Map.Poly.add_exn
        (Map.Poly.singleton Z.one f)
        ~key:(Z.of_int 2) ~data:(negate f)
    in
    let atoms =
      let pos, neg = atoms_of f in
      Set.union pos neg
    in
    loop Map.Poly.empty Z.one Z.one Z.one formulas atoms clausenames
end

(*PQSAT_gen is way of using Generator.
  assume that there is one random variable and random binder is last*)
module PQSAT_gen (A : sig
  val let_sort : string Set.Poly.t -> TermSubst.t -> TermSubst.t

  val model_based_projection :
    TermSubst.t -> Ident.tvar -> Atom.t Set.Poly.t -> Atom.t Set.Poly.t
end) =
struct
  open Formula

  type player = SAT | UNSAT

  let rec level_of level = function
    | (Exists, sortenv) :: tl ->
        let level = if Z.is_odd level then level else Z.succ level in
        let map =
          List.fold sortenv ~init:Map.Poly.empty ~f:(fun map (tvar, sort) ->
              Map.Poly.add_exn map ~key:tvar ~data:(level, sort))
        in
        let map', random = level_of level tl in
        (Map.force_merge map map', random)
    | (Forall, sortenv) :: tl ->
        let level = if Z.is_even level then level else Z.succ level in
        let map =
          List.fold sortenv ~init:Map.Poly.empty ~f:(fun map (tvar, sort) ->
              Map.Poly.add_exn map ~key:tvar ~data:(level, sort))
        in
        let map', random = level_of level tl in
        (Map.force_merge map map', random)
    (*Random is last binder*)
    | (Random rand, sortenv) :: [] ->
        if List.length sortenv = 1 then
          let tvar, sort = List.hd_exn sortenv in
          (Map.Poly.singleton tvar (Z.zero, sort), (tvar, rand))
        else assert false
    | _ -> assert false

  let maxlevel vlevel =
    let level =
      Map.Poly.fold vlevel ~init:Z.zero ~f:(fun ~key:_ ~data:(level, _) n ->
          Z.max n level)
    in
    if Z.Compare.( > ) level Z.one then level else Z.succ level

  let add_dontcare model vlevel =
    Map.Poly.fold vlevel ~init:model ~f:(fun ~key ~data:(_, sort) model ->
        match Map.Poly.find model key with
        | Some _ -> model
        | None -> Map.Poly.add_exn model ~key ~data:(Term.mk_dummy sort))

  let level_exists atom vlevel =
    Set.fold (Atom.tvs_of atom) ~init:(Z.zero, true)
      ~f:(fun (level, rvar) tvar ->
        let l, _ = Map.Poly.find_exn vlevel tvar in
        if Z.Compare.( = ) l Z.zero then (level, false)
        else if Z.is_odd l then (Z.max level l, rvar)
        else (level, rvar))

  let level_forall atom vlevel =
    Set.fold (Atom.tvs_of atom) ~init:(Z.zero, true)
      ~f:(fun (level, rvar) tvar ->
        let l, _ = Map.Poly.find_exn vlevel tvar in
        if Z.Compare.( = ) l Z.zero then (level, false)
        else if Z.is_even l then (Z.max level l, rvar)
        else (level, rvar))

  let level_j j atom vlevel =
    if Z.is_odd j then level_exists atom vlevel else level_forall atom vlevel

  let rec level_j_atomterm j vlevel = function
    | Atom (a, _) ->
        let level, _ = level_j j a vlevel in
        level
    | UnaryOp (Not, phi, _) -> level_j_atomterm j vlevel phi
    | _ -> assert false

  let strategy model j atoms vlevel =
    if Map.Poly.is_empty model then [ Atom.mk_true () ]
    else
      let atoms =
        Set.filter atoms ~f:(fun a ->
            let level, norvar = level_j j a vlevel in
            norvar && Z.Compare.(level <= Z.(j - Z.of_int 2)))
      in
      List.map (Set.to_list atoms) ~f:(Mbp.sign model)

  let pstrategy model ephi rbounds =
    let atoms =
      let tatoms, fatoms = atoms_of (mk_and ephi rbounds) in
      Set.to_list @@ Set.union tatoms fatoms
    in
    List.map atoms ~f:(Mbp.sign model >> Formula.mk_atom)

  let tail j vlevel =
    Map.Poly.filter vlevel ~f:(fun (level, _) ->
        Z.Compare.(level >= Z.(j - Z.one)))

  let rec mbp model j vlevel core =
    let core, bcore =
      Set.fold core ~init:(Set.Poly.empty, Set.Poly.empty)
        ~f:(fun (c, bc) phi ->
          match bool_var_atom phi with
          | First phi' -> (c, Set.add bc phi')
          | Second atm -> (Set.add c atm, bc))
    in
    if false then (
      print_endline
        ("core: " ^ List.to_string ~f:Atom.str_of @@ Set.to_list core);
      print_endline
        ("bcore: " ^ List.to_string ~f:Atom.str_of @@ Set.to_list bcore);
      print_endline "");
    let mbp_theory model tail phis bphis =
      let phis, bphis =
        Map.Poly.fold tail ~init:(phis, bphis)
          ~f:(fun ~key:tvar ~data:(_, sort) (phis, bphis) ->
            if Term.is_bool_sort sort then
              (phis, Mbp.Boolean.model_based_projection model tvar bphis)
            else (A.model_based_projection model tvar phis, bphis))
      in
      Set.union phis bphis
    in
    let tail = tail j vlevel in
    let jformulas =
      Set.Poly.map ~f:Evaluator.simplify_atom
      @@ mbp_theory model tail core bcore
    in
    let index = if Z.is_odd j then Z.one else Z.of_int 2 in
    let index =
      Set.fold jformulas ~init:index ~f:(fun i jterm ->
          Z.max i (level_j_atomterm j vlevel jterm))
    in
    if Z.Compare.(index = Z.(j - Z.of_int 2)) then
      (and_of @@ Set.to_list jformulas, index)
    else mbp model Z.(index + Z.of_int 2) vlevel jformulas

  let update_formulas formulas atoms j jformula =
    let newformulas =
      if Z.is_odd j then
        Map.Poly.mapi formulas ~f:(fun ~key ~data ->
            if Z.Compare.(key < j) then data
            else if Z.is_odd key then mk_and data (negate jformula)
            else data)
      else
        Map.Poly.mapi formulas ~f:(fun ~key ~data ->
            if Z.Compare.(key < j) then data
            else if Z.is_even key then mk_and data (negate jformula)
            else data)
    in
    let newatoms =
      let pos, neg = atoms_of jformula in
      Set.Poly.union_list [ atoms; pos; neg ]
    in
    (newformulas, newatoms)

  let theta_j theta j = if Z.is_odd j then theta else 1. -. theta

  (*phi is nnf*)
  let rec eval_phi rvar model phi =
    match phi with
    | Atom (atom, _) ->
        let tvs = Atom.tvs_of atom in
        if Set.mem tvs rvar then phi
        else Evaluator.simplify_atom @@ Atom.subst model atom
    | UnaryOp (_, Atom (atom, _), _) ->
        let tvs = Atom.tvs_of atom in
        if Set.mem tvs rvar then phi
        else Evaluator.simplify_atom_neg @@ Atom.subst model atom
    | BinaryOp (binop, phi1, phi2, _) ->
        mk_binop binop (eval_phi rvar model phi1) (eval_phi rvar model phi2)
    | _ -> assert false

  open ApronInterface

  let separate_real_poly ?(tmodel = true) poly term model varmap =
    let t0 = T_real.rzero () in
    let temp = Atom.mk_psym_app T_real.RGeq [ term; t0 ] in
    let atom =
      if tmodel then
        if Evaluator.eval_atom @@ Atom.subst model temp then temp
        else Atom.mk_psym_app T_real.RGt [ term; t0 ]
      else if Evaluator.eval_atom @@ Atom.subst model temp then
        Atom.mk_psym_app T_real.RGt [ term; t0 ]
      else temp
    in
    let negatom =
      Normalizer.normalize_atom
      @@
      match Atom.negate atom with
      | None -> failwith "[separate_real_poly]"
      | Some neg_atom -> neg_atom
    in
    let atom = Normalizer.normalize_atom atom in
    if false then print_endline ("separate atom is " ^ Atom.str_of atom);
    ( separate_real_polyhedron poly atom varmap,
      separate_real_polyhedron poly negatom varmap )

  let print_vt vertex =
    List.iter vertex ~f:(fun (m, lb, ub) ->
        print_endline ("vt:" ^ TermSubst.str_of m);
        print_string "lb:";
        Set.iter lb ~f:(Term.str_of >> print_string);
        print_endline "";
        print_string "ub:";
        Set.iter ub ~f:(Term.str_of >> print_string);
        print_endline "")

  let real_pcore rvar rand str ephi vlevel theta =
    let theta = Q.of_float theta in
    let rt1, rt2 = Rand.let_uniform rand in
    let vars = Map.Poly.keys vlevel in
    let stratoms =
      List.map str ~f:(Formula.to_atom >> Normalizer.normalize_atom)
    in
    let varmap = mk_varmap vars in
    let polyhedron = mk_real_polyhedron varmap stratoms in
    if is_eq ephi then ([ mk_real_atoms polyhedron varmap ], [])
    else
      let rec loop poly =
        if false then (
          print_endline "Loop";
          print_endline (real_poly_to_string poly varmap));
        let vertex = mk_vertex poly varmap in
        let vertex = List.map vertex ~f:(fun g -> Map.Poly.remove g rvar) in
        if false then
          List.iter vertex ~f:(fun m -> print_endline (TermSubst.str_of m));
        let atoms = mk_real_atoms poly varmap in
        let vte =
          List.map vertex ~f:(fun vt ->
              Generator.lb_and_ub vt rvar ephi rt1 rt2)
        in
        let tvt, thetavt, fvt =
          Generator.separate_vt vte rt1 rt2 theta Generator.compute_real
        in
        (* if false then (
           print_endline "tvt";
           print_vt tvt;
           print_endline "thetavt";
           print_vt thetavt;
           print_endline "fvt";
           print_vt fvt); *)
        if List.is_empty tvt then
          let ray = mk_ray poly varmap in
          if List.is_empty ray then [ atoms ]
          else
            let fvertex, rayvt = Generator.mk_rayvertex fvt (List.hd_exn ray) in
            let rayvertex = Generator.lb_and_ub rayvt rvar ephi rt1 rt2 in
            if
              Q.(
                Generator.compute_real fvertex rt1 rt2
                >= Generator.compute_real rayvertex rt1 rt2)
            then [ atoms ]
            else
              let num = Generator.mk_numterm rayvertex in
              let den = Generator.mk_denterm rayvt rt1 rt2 in
              let newterm = Generator.mk_newterm num den theta in
              let fmodel, _ = fvertex in
              let poly1, poly2 =
                separate_real_poly ~tmodel:false poly newterm fmodel varmap
              in
              loop poly1 @ loop poly2
        else if List.is_empty fvt then
          let ray = mk_ray poly varmap in
          if List.is_empty ray then []
          else
            let tvertex, rayvt = Generator.mk_rayvertex tvt (List.hd_exn ray) in
            let rayvertex = Generator.lb_and_ub rayvt rvar ephi rt1 rt2 in
            if
              Q.(
                Generator.compute_real tvertex rt1 rt2
                <= Generator.compute_real rayvertex rt1 rt2)
            then []
            else
              let num = Generator.mk_numterm rayvertex in
              let den = Generator.mk_denterm rayvt rt1 rt2 in
              let newterm = Generator.mk_newterm num den theta in
              let tmodel, _ = tvertex in
              let poly1, poly2 =
                separate_real_poly poly newterm tmodel varmap
              in
              loop poly1 @ loop poly2
        else
          let line =
            List.find_map fvt ~f:(fun (vt, e) ->
                match Generator.find_same e (tvt @ thetavt) with
                | None -> None
                | Some (tvt, e) -> Some (tvt, vt, e))
          in
          let tvt, num, den =
            match line with
            | Some (tvt, fvt, e) ->
                let mid = Generator.midpoint tvt fvt in
                ( tvt,
                  Generator.mk_numterm (mid, e),
                  Generator.mk_denterm mid rt1 rt2 )
            | None -> assert false
          in
          let newterm = Generator.mk_newterm num den theta in
          let poly1, poly2 = separate_real_poly poly newterm tvt varmap in
          loop poly1 @ loop poly2
      in
      let pcores = loop polyhedron in
      if List.is_empty pcores then (pcores, [ mk_real_atoms polyhedron varmap ])
      else (pcores, [])

  let separate_int_poly ?(tmodel = true) poly term model varmap =
    let t0 = T_real.rzero () in
    let temp = Atom.mk_psym_app T_real.RGeq [ term; t0 ] in
    let psym =
      if tmodel then
        if Evaluator.eval_atom @@ Atom.subst model temp then T_int.Geq
        else T_int.Gt
      else if Evaluator.eval_atom @@ Atom.subst model temp then T_int.Gt
      else T_int.Geq
    in
    let t0 = T_int.zero () in
    let term =
      let to_int_term term =
        AffineTerm.mk_int_term @@ AffineTerm.real_to_int
        @@ Normalizer.linear_real_monomials_of (Value.Real Q.one) term
      in
      to_int_term term
    in
    let atom =
      Normalizer.normalize_atom @@ Atom.mk_psym_app psym [ term; t0 ]
    in
    let negatom =
      Normalizer.normalize_atom
      @@
      match Atom.negate atom with
      | None -> failwith "[separate_int_poly]"
      | Some neg_atom -> neg_atom
    in
    if false then print_endline ("separate atom is " ^ Atom.str_of atom);
    ( separate_int_polyhedron poly atom varmap,
      separate_int_polyhedron poly negatom varmap )

  let int_pcore rvar rand str ephi vlevel theta =
    let theta = Q.of_float theta in
    let rt1, rt2 = Rand.let_int_uniform rand in
    let rt1, rt2 =
      let to_real_term term =
        AffineTerm.mk_real_term @@ AffineTerm.int_to_real
        @@ Normalizer.linear_int_monomials_of (Value.Int Z.one) term
      in
      (to_real_term rt1, to_real_term rt2)
    in
    let vars = Map.Poly.keys vlevel in
    let stratoms =
      List.map str ~f:(Formula.to_atom >> Normalizer.normalize_atom)
    in
    let varmap = mk_varmap vars in
    let polyhedron = mk_int_polyhedron varmap stratoms in
    let rec loop poly =
      if false then (
        print_endline "Loop";
        print_endline (int_poly_to_string poly varmap));
      let vertex = mk_vertex poly varmap in
      let vertex = List.map vertex ~f:(Fn.flip Map.Poly.remove rvar) in
      let atoms = mk_int_atoms poly varmap in
      let vtlbub =
        List.map vertex ~f:(fun vt -> Generator.lb_and_ub vt rvar ephi rt1 rt2)
      in
      let tvt, thetavt, fvt =
        Generator.separate_vt vtlbub rt1 rt2 theta Generator.compute_int
      in
      if List.is_empty tvt then
        let ray = mk_ray poly varmap in
        if List.is_empty ray then [ atoms ]
        else
          let fvertex, rayvt = Generator.mk_rayvertex fvt (List.hd_exn ray) in
          let rayvertex = Generator.lb_and_ub rayvt rvar ephi rt1 rt2 in
          if
            Q.(
              Generator.compute_int fvertex rt1 rt2
              >= Generator.compute_int rayvertex rt1 rt2)
          then [ atoms ]
          else
            let num = Generator.mk_int_numterm rayvertex in
            let den = Generator.mk_int_denterm rayvt rt1 rt2 in
            let newterm = Generator.mk_newterm num den theta in
            let poly1, poly2 = separate_int_poly poly newterm rayvt varmap in
            loop poly1 @ loop poly2
      else if List.is_empty fvt then
        let ray = mk_ray poly varmap in
        if List.is_empty ray then []
        else
          let tvertex, rayvt = Generator.mk_rayvertex tvt (List.hd_exn ray) in
          let rayvertex = Generator.lb_and_ub rayvt rvar ephi rt1 rt2 in
          if
            Q.(
              Generator.compute_int tvertex rt1 rt2
              <= Generator.compute_int rayvertex rt1 rt2)
          then []
          else
            let num = Generator.mk_int_numterm rayvertex in
            let den = Generator.mk_int_denterm rayvt rt1 rt2 in
            let newterm = Generator.mk_newterm num den theta in
            let poly1, poly2 = separate_int_poly poly newterm rayvt varmap in
            loop poly1 @ loop poly2
      else
        let line =
          List.find_map fvt ~f:(fun (vt, e) ->
              match Generator.find_same e (tvt @ thetavt) with
              | None -> None
              | Some (tvt, e) -> Some (tvt, vt, e))
        in
        let tvt, num, den =
          match line with
          | Some (tvt, fvt, e) ->
              let mid = Generator.midpoint tvt fvt in
              ( tvt,
                Generator.mk_int_numterm (mid, e),
                Generator.mk_int_denterm mid rt1 rt2 )
          | None -> assert false
        in
        let newterm = Generator.mk_newterm num den theta in
        let poly1, poly2 = separate_int_poly poly newterm tvt varmap in
        loop poly1 @ loop poly2
    in
    let pcores = loop polyhedron in
    if List.is_empty pcores then (pcores, [ mk_int_atoms polyhedron varmap ])
    else (pcores, [])

  let pcore rvar rand str ephi vlevel theta =
    let pcores, wins =
      match Rand.sort_of rand with
      | T_real.SReal -> real_pcore rvar rand str ephi vlevel theta
      | T_int.SInt -> int_pcore rvar rand str ephi vlevel theta
      | _ -> assert false
    in
    let rm_rvar atomss =
      List.map atomss
        ~f:
          (List.filter_map ~f:(fun a ->
               if Set.mem (Atom.tvs_of a) rvar then None
               else Some (Formula.mk_atom a)))
    in
    (rm_rvar pcores, rm_rvar wins)

  let solve quantifiers f theta =
    let open Z3Smt.Z3interface in
    if false then (
      List.iter quantifiers ~f:(fun (binder, sortenv) ->
          print_string
            (str_of_binder binder
            ^ str_of_sort_env_list Term.str_of_sort sortenv
            ^ " "));
      print_endline "";
      print_endline (str_of f));
    let vlevel, (rvar, rand) = level_of Z.one quantifiers in
    let maxlevel = maxlevel vlevel in
    let clausenames = Set.add (Set.Poly.singleton "main") "rbounds" in
    let formulas =
      Map.Poly.add_exn
        (Map.Poly.singleton Z.one f)
        ~key:(Z.of_int 2) ~data:(negate f)
    in
    let rbounds =
      Normalizer.normalize @@ Rand.mk_uniform_bounds [ rvar ] rand
    in
    let atoms =
      let rpos, _neg = atoms_of rbounds in
      let pos, neg = atoms_of f in
      Set.union (Set.union pos neg) rpos
    in
    let fenv = Map.Poly.empty in
    (*TODO: generate fenv*)
    let rec loop (tmodel, fmodel) j formulas atoms clausenames =
      let formula = Map.Poly.find_exn formulas j in
      let model = if Z.is_odd j then fmodel else tmodel in
      let str = strategy model j atoms vlevel in
      if false then (
        print_endline (Z.to_string j);
        print_endline ("Formula: " ^ str_of formula);
        print_endline ("Strategy: " ^ List.to_string ~f:Atom.str_of str));
      if Z.Compare.( <= ) j Z.(maxlevel + Z.one) then
        let pvar_clause_map, clausenames =
          List.foldi str
            ~init:(Map.Poly.singleton "main" formula, clausenames)
            ~f:(fun i (map, names) phi ->
              let name = "|#S_" ^ string_of_int i ^ "|" in
              let names = Set.add names name in
              (Map.Poly.add_exn map ~key:name ~data:(Formula.mk_atom phi), names))
        in
        let pvar_clause_map =
          Map.Poly.add_exn pvar_clause_map ~key:"rbounds" ~data:rbounds
        in
        match check_sat_unsat_core ~id:None fenv pvar_clause_map with
        | `Unsat core ->
            if Z.Compare.(j = Z.one) then UNSAT
            else if Z.Compare.(j = Z.of_int 2) then SAT
            else
              let core =
                List.filter_opt
                @@ List.map core ~f:(function
                     | "main" | "rbounds" -> None
                     | v -> Map.Poly.find pvar_clause_map v)
              in
              let jformula, j = mbp model j vlevel (Set.Poly.of_list core) in
              if false then (
                print_endline ("core: " ^ List.to_string ~f:str_of core);
                print_endline ("jformula: " ^ str_of jformula));
              let formulas, atoms = update_formulas formulas atoms j jformula in
              loop (Map.Poly.empty, Map.Poly.empty) j formulas atoms clausenames
        | `Sat model ->
            let model =
              remove_dontcare model |> Map.Poly.of_alist_exn
              |> A.let_sort clausenames
            in
            let model = add_dontcare model vlevel in
            if false then print_endline ("model: " ^ TermSubst.str_of model);
            let formulas =
              Map.Poly.update formulas (Z.succ j) ~f:(function
                | Some phi -> phi
                | None -> Map.Poly.find_exn formulas (Z.pred j))
            in
            if Z.is_odd j then
              loop (model, fmodel) (Z.succ j) formulas atoms clausenames
            else loop (tmodel, model) (Z.succ j) formulas atoms clausenames
        | _ -> assert false
      else
        let thetaj = theta_j theta j in
        let model = if Z.is_odd j then tmodel else fmodel in
        let ephi =
          Normalizer.normalize @@ Evaluator.simplify
          @@ eval_phi rvar model (nnf_of formula)
        in
        let pstr =
          pstrategy model ephi rbounds @ List.map ~f:Formula.mk_atom str
        in
        if false then (
          print_endline ("pcore of " ^ Z.to_string j);
          print_endline ("Formula: " ^ str_of formula);
          print_endline ("PStrategy: " ^ List.to_string ~f:str_of pstr);
          print_endline ("model: " ^ TermSubst.str_of model);
          print_endline ("ephi: " ^ str_of ephi));
        let pcores, wins = pcore rvar rand pstr ephi vlevel thetaj in
        let j, pcores =
          if List.is_empty pcores then (Z.succ j, wins) else (j, pcores)
        in
        if false then (
          print_endline ("PCores of " ^ Z.to_string j);
          List.iter pcores ~f:(fun pcore ->
              print_endline "";
              List.iter pcore ~f:(fun phi -> print_endline (str_of phi))));
        let jformulas, j =
          List.fold pcores ~init:([], Z.zero) ~f:(fun (l, n) pcore ->
              let formula, i = mbp model j vlevel (Set.Poly.of_list pcore) in
              (formula :: l, Z.max n i))
        in
        let formulas, atoms =
          List.fold jformulas ~init:(formulas, atoms) ~f:(fun (fs, ats) f ->
              update_formulas fs ats j f)
        in
        loop (Map.Poly.empty, Map.Poly.empty) j formulas atoms clausenames
    in
    loop (Map.Poly.empty, Map.Poly.empty) Z.one formulas atoms clausenames
end
