;(set-option :produce-unsat-cores true )
(set-logic ALL_SUPPORTED )
(declare-sort A$ 0 )
(declare-sort A_set$ 0 )
(declare-sort A_bool_fun$ 0 )
(declare-sort A_a_bool_fun_fun$ 0 )
(declare-sort A_llist_bool_fun$ 0 )
(declare-sort A_llist_a_llist_fun$ 0 )
(declare-sort A_llist$ 0)
(declare-fun lNil$ ()A_llist$)
(declare-fun lhd$ (A_llist$)A$)
(declare-fun ltl$ (A_llist$)A_llist$)
(declare-fun lCons$ (A$ A_llist$ )A_llist$)
(declare-fun x$ (A_llist$ )Bool )
(declare-fun uu$ (A$ )A_llist_a_llist_fun$ )
(declare-fun xs$ ()A_llist$ )
(declare-fun max$ (A_a_bool_fun_fun$ A$ A$ )A$ )
(declare-fun min$ (A_a_bool_fun_fun$ A$ A$ )A$ )
(declare-fun atMost$ (A_a_bool_fun_fun$ A$ )A_set$ )
(declare-fun member$ (A$ A_set$ )Bool )
(declare-fun atLeast$ (A_a_bool_fun_fun$ A$ )A_set$ )
(declare-fun fun_app$ (A_llist_a_llist_fun$ A_llist$ )A_llist$ )
(declare-fun less_eq$ ()A_a_bool_fun_fun$ )
(declare-fun lsorted$ (A_a_bool_fun_fun$ )A_llist_bool_fun$ )
(declare-fun fun_app$a (A_llist_bool_fun$ A_llist$ )Bool )
(declare-fun fun_app$b (A_bool_fun$ A$ )Bool )
(declare-fun fun_app$c (A_a_bool_fun_fun$ A$ )A_bool_fun$ )
(declare-fun atLeastAtMost$ (A_a_bool_fun_fun$ A$ A$ )A_set$ )
(assert (! (forall ((?v0 A$ )(?v1 A_llist$ ))(! (= (fun_app$ (uu$ ?v0 )?v1 )(lCons$ ?v0 ?v1 )):pattern ((fun_app$ (uu$ ?v0 )?v1 )))):named a0 ))
(assert (! (not (fun_app$a (lsorted$ less_eq$ )xs$ )):named a1 ))
(assert (! (x$ xs$ ):named a2 ))
(assert (! (forall ((?v0 A$ )(?v1 A$ )(?v2 A$ ))(=> (and (= ?v0 ?v1 )(fun_app$b (fun_app$c less_eq$ ?v1 )?v2 ))(fun_app$b (fun_app$c less_eq$ ?v0 )?v2 ))):named a3 ))
(assert (! (forall ((?v0 A$ )(?v1 A$ )(?v2 A$ ))(=> (and (fun_app$b (fun_app$c less_eq$ ?v0 )?v1 )(= ?v1 ?v2 ))(fun_app$b (fun_app$c less_eq$ ?v0 )?v2 ))):named a4 ))
(assert (! (forall ((?v0 A$ )(?v1 A$ ))(! (= (max$ less_eq$ ?v0 ?v1 )(ite (fun_app$b (fun_app$c less_eq$ ?v0 )?v1 )?v1 ?v0 )):pattern ((max$ less_eq$ ?v0 ?v1 )))):named a5 ))
(assert (! (forall ((?v0 A$ )(?v1 A$ ))(! (= (min$ less_eq$ ?v0 ?v1 )(ite (fun_app$b (fun_app$c less_eq$ ?v0 )?v1 )?v0 ?v1 )):pattern ((min$ less_eq$ ?v0 ?v1 )))):named a6 ))
(assert (! (forall ((?v0 A$ )(?v1 A$ )(?v2 A$ ))(= (member$ ?v0 (atLeastAtMost$ less_eq$ ?v1 ?v2 ))(and (fun_app$b (fun_app$c less_eq$ ?v1 )?v0 )(fun_app$b (fun_app$c less_eq$ ?v0 )?v2 )))):named a7 ))
(assert (! (fun_app$a (lsorted$ less_eq$ )lNil$ ):named a8 ))
(assert (! (forall ((?v0 A$ )(?v1 A$ )(?v2 A_llist$ ))(=> (and (fun_app$b (fun_app$c less_eq$ ?v0 )?v1 )(fun_app$a (lsorted$ less_eq$ )(lCons$ ?v1 ?v2 )))(fun_app$a (lsorted$ less_eq$ )(lCons$ ?v0 (lCons$ ?v1 ?v2 ))))):named a9 ))
(assert (! (forall ((?v0 A$ )(?v1 A$ ))(= (member$ ?v0 (atMost$ less_eq$ ?v1 ))(fun_app$b (fun_app$c less_eq$ ?v0 )?v1 ))):named a10 ))
(assert (! (forall ((?v0 A$ )(?v1 A$ ))(= (member$ ?v0 (atLeast$ less_eq$ ?v1 ))(fun_app$b (fun_app$c less_eq$ ?v1 )?v0 ))):named a11 ))
(assert (! (= (fun_app$a (lsorted$ less_eq$ )lNil$ )true ):named a12 ))
(assert (! (forall ((?v0 A$ )(?v1 A$ )(?v2 A_llist$ ))(! (= (fun_app$a (lsorted$ less_eq$ )(lCons$ ?v0 (lCons$ ?v1 ?v2 )))(and (fun_app$b (fun_app$c less_eq$ ?v0 )?v1 )(fun_app$a (lsorted$ less_eq$ )(lCons$ ?v1 ?v2 )))):pattern ((lCons$ ?v0 (lCons$ ?v1 ?v2 ))))):named a13 ))
(assert (! (forall ((?v0 A_llist$ ))(= (fun_app$a (lsorted$ less_eq$ )?v0 )(or (= ?v0 lNil$ )(or (exists ((?v1 A$ ))(= ?v0 (lCons$ ?v1 lNil$ )))(exists ((?v1 A$ )(?v2 A$ )(?v3 A_llist$ ))(and (= ?v0 (lCons$ ?v1 (lCons$ ?v2 ?v3 )))(and (fun_app$b (fun_app$c less_eq$ ?v1 )?v2 )(fun_app$a (lsorted$ less_eq$ )(lCons$ ?v2 ?v3 ))))))))):named a14 ))
(assert (! (forall ((?v0 A_llist$ ))(=> (and (fun_app$a (lsorted$ less_eq$ )?v0 )(and (=> (= ?v0 lNil$ )false )(and (forall ((?v1 A$ ))(=> (= ?v0 (lCons$ ?v1 lNil$ ))false ))(forall ((?v1 A$ )(?v2 A$ )(?v3 A_llist$ ))(=> (and (= ?v0 (lCons$ ?v1 (lCons$ ?v2 ?v3 )))(and (fun_app$b (fun_app$c less_eq$ ?v1 )?v2 )(fun_app$a (lsorted$ less_eq$ )(lCons$ ?v2 ?v3 ))))false )))))false )):named a15 ))
(assert (! (forall ((?v0 A_llist_bool_fun$ )(?v1 A_llist$ ))(=> (and (fun_app$a ?v0 ?v1 )(forall ((?v2 A_llist$ ))(=> (fun_app$a ?v0 ?v2 )(or (= ?v2 lNil$ )(or (exists ((?v3 A$ ))(= ?v2 (lCons$ ?v3 lNil$ )))(exists ((?v3 A$ )(?v4 A$ )(?v5 A_llist$ ))(and (= ?v2 (lCons$ ?v3 (lCons$ ?v4 ?v5 )))(and (fun_app$b (fun_app$c less_eq$ ?v3 )?v4 )(or (fun_app$a ?v0 (lCons$ ?v4 ?v5 ))(fun_app$a (lsorted$ less_eq$ )(lCons$ ?v4 ?v5 )))))))))))(fun_app$a (lsorted$ less_eq$ )?v1 ))):named a16 ))
(assert (! (forall ((?v0 A$ ))(fun_app$a (lsorted$ less_eq$ )(lCons$ ?v0 lNil$ ))):named a17 ))
(assert (! (forall ((?v0 A$ ))(! (= (fun_app$a (lsorted$ less_eq$ )(lCons$ ?v0 lNil$ ))true ):pattern ((uu$ ?v0 )))):named a18 ))
(check-sat )
;(get-unsat-core )
