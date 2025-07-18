;(set-option :produce-unsat-cores true )
(set-logic ALL_SUPPORTED )
(declare-sort A$ 0 )
(declare-sort A_set$ 0 )
(declare-sort A_bool_fun$ 0 )
(declare-sort A_a_bool_fun_fun$ 0 )
(declare-sort A_llist$ 0)
(declare-fun lNil$ ()A_llist$)
(declare-fun lhd$ (A_llist$)A$)
(declare-fun ltl$ (A_llist$)A_llist$)
(declare-fun lCons$ (A$ A_llist$ )A_llist$)
(declare-fun xs$ ()A_llist$ )
(declare-fun ys$ ()A_llist$ )
(declare-fun max$ (A_a_bool_fun_fun$ A$ A$ )A$ )
(declare-fun min$ (A_a_bool_fun_fun$ A$ A$ )A$ )
(declare-fun atMost$ (A_a_bool_fun_fun$ A$ )A_set$ )
(declare-fun member$ (A$ A_set$ )Bool )
(declare-fun atLeast$ (A_a_bool_fun_fun$ A$ )A_set$ )
(declare-fun fun_app$ (A_bool_fun$ A$ )Bool )
(declare-fun less_eq$ ()A_a_bool_fun_fun$ )
(declare-fun lprefix$ (A_llist$ A_llist$ )Bool )
(declare-fun lsorted$ (A_a_bool_fun_fun$ A_llist$ )Bool )
(declare-fun fun_app$a (A_a_bool_fun_fun$ A$ )A_bool_fun$ )
(declare-fun atLeastAtMost$ (A_a_bool_fun_fun$ A$ A$ )A_set$ )
(assert (! (not (lsorted$ less_eq$ xs$ )):named a0 ))
(assert (! (lprefix$ xs$ ys$ ):named a1 ))
(assert (! (lsorted$ less_eq$ ys$ ):named a2 ))
(assert (! (forall ((?v0 A$ )(?v1 A$ )(?v2 A$ ))(=> (and (= ?v0 ?v1 )(fun_app$ (fun_app$a less_eq$ ?v1 )?v2 ))(fun_app$ (fun_app$a less_eq$ ?v0 )?v2 ))):named a3 ))
(assert (! (forall ((?v0 A$ )(?v1 A$ )(?v2 A$ ))(=> (and (fun_app$ (fun_app$a less_eq$ ?v0 )?v1 )(= ?v1 ?v2 ))(fun_app$ (fun_app$a less_eq$ ?v0 )?v2 ))):named a4 ))
(assert (! (forall ((?v0 A$ )(?v1 A$ ))(! (= (max$ less_eq$ ?v0 ?v1 )(ite (fun_app$ (fun_app$a less_eq$ ?v0 )?v1 )?v1 ?v0 )):pattern ((max$ less_eq$ ?v0 ?v1 )))):named a5 ))
(assert (! (forall ((?v0 A$ )(?v1 A$ ))(! (= (min$ less_eq$ ?v0 ?v1 )(ite (fun_app$ (fun_app$a less_eq$ ?v0 )?v1 )?v0 ?v1 )):pattern ((min$ less_eq$ ?v0 ?v1 )))):named a6 ))
(assert (! (forall ((?v0 A_llist$ ))(lprefix$ ?v0 ?v0 )):named a7 ))
(assert (! (forall ((?v0 A_llist$ ))(lprefix$ ?v0 ?v0 )):named a8 ))
(assert (! (forall ((?v0 A_llist$ )(?v1 A_llist$ ))(=> (and (lprefix$ ?v0 ?v1 )(lprefix$ ?v1 ?v0 ))(= ?v0 ?v1 ))):named a9 ))
(assert (! (forall ((?v0 A_llist$ )(?v1 A_llist$ ))(=> (and (lprefix$ ?v0 ?v1 )(lprefix$ ?v1 ?v0 ))(= ?v0 ?v1 ))):named a10 ))
(assert (! (forall ((?v0 A_llist$ )(?v1 A_llist$ )(?v2 A_llist$ ))(=> (and (lprefix$ ?v0 ?v1 )(lprefix$ ?v2 ?v1 ))(or (lprefix$ ?v0 ?v2 )(lprefix$ ?v2 ?v0 )))):named a11 ))
(assert (! (forall ((?v0 A_llist$ )(?v1 A_llist$ )(?v2 A_llist$ ))(=> (and (lprefix$ ?v0 ?v1 )(lprefix$ ?v1 ?v2 ))(lprefix$ ?v0 ?v2 ))):named a12 ))
(assert (! (forall ((?v0 A_llist$ )(?v1 A_llist$ )(?v2 A_llist$ ))(=> (and (lprefix$ ?v0 ?v1 )(lprefix$ ?v1 ?v2 ))(lprefix$ ?v0 ?v2 ))):named a13 ))
(assert (! (forall ((?v0 A$ )(?v1 A$ )(?v2 A$ ))(= (member$ ?v0 (atLeastAtMost$ less_eq$ ?v1 ?v2 ))(and (fun_app$ (fun_app$a less_eq$ ?v1 )?v0 )(fun_app$ (fun_app$a less_eq$ ?v0 )?v2 )))):named a14 ))
(assert (! (lsorted$ less_eq$ lNil$ ):named a15 ))
(assert (! (forall ((?v0 A$ )(?v1 A$ )(?v2 A_llist$ ))(=> (and (fun_app$ (fun_app$a less_eq$ ?v0 )?v1 )(lsorted$ less_eq$ (lCons$ ?v1 ?v2 )))(lsorted$ less_eq$ (lCons$ ?v0 (lCons$ ?v1 ?v2 ))))):named a16 ))
(assert (! (forall ((?v0 A_llist$ ))(=> (lsorted$ less_eq$ ?v0 )(lsorted$ less_eq$ (ltl$ ?v0 )))):named a17 ))
(assert (! (forall ((?v0 A$ )(?v1 A$ ))(= (member$ ?v0 (atMost$ less_eq$ ?v1 ))(fun_app$ (fun_app$a less_eq$ ?v0 )?v1 ))):named a18 ))
(assert (! (forall ((?v0 A$ )(?v1 A$ ))(= (member$ ?v0 (atLeast$ less_eq$ ?v1 ))(fun_app$ (fun_app$a less_eq$ ?v1 )?v0 ))):named a19 ))
(check-sat )
;(get-unsat-core )
