open Core
open Common.Ext
open Common.Combinator
open Ast
open Ast.LogicOld

let make n seeds =
  Set.fold seeds
    ~init:(Set.Poly.singleton (n, []))
    ~f:(fun acc (x, _, t) ->
      Set.Poly.union_list
        [
          acc;
          Set.concat_map acc ~f:(fun (n, xts) ->
              Set.Poly.of_list
              @@ List.init n ~f:(fun i ->
                     (n - (i + 1), List.init (i + 1) ~f:(fun _ -> (x, t)) @ xts)));
          Set.concat_map acc ~f:(fun (n, xts) ->
              Set.Poly.of_list
              @@ List.init n ~f:(fun i ->
                     ( n - (i + 1),
                       List.init (i + 1) ~f:(fun _ ->
                           (T_int.mk_neg x, T_int.mk_neg t))
                       @ xts )));
        ])
  |> Set.Poly.filter_map ~f:(fun (_, lrs) ->
         let ls, rs = List.unzip lrs in
         let left, right =
           (T_int.mk_sum (T_int.zero ()) ls, T_int.mk_sum (T_int.zero ()) rs)
         in
         let qual =
           Normalizer.normalize
           @@ Formula.geq left
                (Term.of_value (get_dtenv ()) @@ Evaluator.eval_term right)
         in
         if Formula.is_ground qual then None else Some qual)

let polyhedron_half_spaces_of n sorts examples =
  let params = LogicOld.sort_env_list_of_sorts sorts in
  ( params,
    Set.union
      (Set.Poly.of_list params
      |> Set.Poly.filter_map ~f:(function
           | x, T_bool.SBool -> Some (Term.mk_var x T_bool.SBool)
           | _, T_int.SInt -> None
           | _, T_real.SReal -> failwith "real"
           | _, s -> failwith ("not supported: " ^ Term.str_of_sort s))
      |> Set.Poly.map ~f:(fun x -> Formula.eq x (T_bool.mk_true ())))
      (Set.concat_map examples ~f:(fun terms ->
           List.map2_exn params terms ~f:(fun (x, s) t ->
               (Term.mk_var x s, s, t))
           |> List.filter ~f:(Triple.snd >> Fn.non Term.is_bool_sort)
           |> Set.Poly.of_list |> make n)) )

module Make (Config : sig
  val upper_bound : int
end) =
struct
  let qualifiers_of _pvar sorts labeled_atoms _examples =
    let params, quals =
      polyhedron_half_spaces_of Config.upper_bound sorts
      @@ Set.Poly.filter_map labeled_atoms
           ~f:(fst >> ExAtom.instantiate >> ExAtom.args_of)
    in
    Set.Poly.map quals ~f:(fun qual -> (params, qual))

  let str_of_domain =
    "Polyhedron with upper bound " ^ string_of_int Config.upper_bound
end
