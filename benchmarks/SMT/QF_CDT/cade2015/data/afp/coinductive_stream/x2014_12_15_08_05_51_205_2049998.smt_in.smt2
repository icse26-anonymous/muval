;(set-option :produce-unsat-cores true )
(set-logic ALL_SUPPORTED )
(declare-sort A$ 0 )
(declare-sort Nat$ 0 )
(declare-sort A_bool_fun$ 0 )
(declare-sort A_llist_set$ 0 )
(declare-sort A_a_bool_fun_fun$ 0 )
(declare-sort A_llist_bool_fun$ 0 )
(declare-sort A_stream_bool_fun$ 0 )
(declare-sort A_llist_a_llist_fun$ 0 )
(declare-sort A_llist_a_stream_bool_fun_fun$ 0 )
(declare-sort A_llist$ 0)
(declare-sort A_stream$ 0)
(declare-fun lNil$ ()A_llist$)
(declare-fun lhd$ (A_llist$)A$)
(declare-fun ltl$ (A_llist$)A_llist$)
(declare-fun lCons$ (A$ A_llist$ )A_llist$)
(declare-fun shd$ (A_stream$)A$)
(declare-fun stl$ (A_stream$)A_stream$)
(declare-fun sCons$ (A$ A_stream$ )A_stream$)
(declare-fun uu$ ()A_a_bool_fun_fun$ )
(declare-fun xs$ ()A_llist$ )
(declare-fun uua$ ()A_llist_bool_fun$ )
(declare-fun ldropn$ (Nat$ )A_llist_a_llist_fun$ )
(declare-fun member$ (A_llist$ A_llist_set$ )Bool )
(declare-fun collect$ (A_llist_bool_fun$ )A_llist_set$ )
(declare-fun fun_app$ (A_llist_bool_fun$ A_llist$ )Bool )
(declare-fun lfinite$ (A_llist$ )Bool )
(declare-fun fun_app$a (A_bool_fun$ A$ )Bool )
(declare-fun fun_app$b (A_a_bool_fun_fun$ A$ )A_bool_fun$ )
(declare-fun fun_app$c (A_stream_bool_fun$ A_stream$ )Bool )
(declare-fun fun_app$d (A_llist_a_stream_bool_fun_fun$ A_llist$ )A_stream_bool_fun$ )
(declare-fun fun_app$e (A_llist_a_llist_fun$ A_llist$ )A_llist$ )
(declare-fun cr_stream$ ()A_llist_a_stream_bool_fun_fun$ )
(declare-fun pcr_stream$ (A_a_bool_fun_fun$ )A_llist_a_stream_bool_fun_fun$ )
(declare-fun lstrict_prefix$ (A_llist$ )A_llist_bool_fun$ )
(declare-fun llist_of_stream$ (A_stream$ )A_llist$ )
(declare-fun stream_of_llist$ (A_llist$ )A_stream$ )
(assert (! (forall ((?v0 A_llist$ ))(! (= (fun_app$ uua$ ?v0 )(not (lfinite$ ?v0 ))):pattern ((fun_app$ uua$ ?v0 )))):named a0 ))
(assert (! (forall ((?v0 A$ )(?v1 A$ ))(! (= (fun_app$a (fun_app$b uu$ ?v0 )?v1 )(= ?v0 ?v1 )):pattern ((fun_app$a (fun_app$b uu$ ?v0 )?v1 )))):named a1 ))
(assert (! (not (fun_app$c (fun_app$d cr_stream$ xs$ )(stream_of_llist$ xs$ ))):named a2 ))
(assert (! (not (lfinite$ xs$ )):named a3 ))
(assert (! (forall ((?v0 A_llist$ ))(=> (not (lfinite$ ?v0 ))(= (llist_of_stream$ (stream_of_llist$ ?v0 ))?v0 ))):named a4 ))
(assert (! (= (pcr_stream$ uu$ )cr_stream$ ):named a5 ))
(assert (! (forall ((?v0 A_stream$ ))(= (stream_of_llist$ (llist_of_stream$ ?v0 ))?v0 )):named a6 ))
(assert (! (forall ((?v0 A_stream$ ))(= (stream_of_llist$ (llist_of_stream$ ?v0 ))?v0 )):named a7 ))
(assert (! (forall ((?v0 A_stream$ ))(not (lfinite$ (llist_of_stream$ ?v0 )))):named a8 ))
(assert (! (forall ((?v0 A_stream_bool_fun$ )(?v1 A_stream$ ))(=> (forall ((?v2 A_llist$ ))(=> (member$ ?v2 (collect$ uua$ ))(fun_app$c ?v0 (stream_of_llist$ ?v2 ))))(fun_app$c ?v0 ?v1 ))):named a9 ))
(assert (! (forall ((?v0 A_stream$ ))(=> (forall ((?v1 A_llist$ ))(=> (and (= ?v0 (stream_of_llist$ ?v1 ))(member$ ?v1 (collect$ uua$ )))false ))false )):named a10 ))
(assert (! (forall ((?v0 A_llist$ )(?v1 A_llist$ ))(=> (and (member$ ?v0 (collect$ uua$ ))(member$ ?v1 (collect$ uua$ )))(= (= (stream_of_llist$ ?v0 )(stream_of_llist$ ?v1 ))(= ?v0 ?v1 )))):named a11 ))
(assert (! (forall ((?v0 A_llist$ )(?v1 A_llist$ ))(=> (fun_app$ (lstrict_prefix$ ?v0 )?v1 )(lfinite$ ?v0 ))):named a12 ))
(assert (! (= (lfinite$ lNil$ )true ):named a13 ))
(assert (! (forall ((?v0 Nat$ )(?v1 A_llist$ ))(= (lfinite$ (fun_app$e (ldropn$ ?v0 )?v1 ))(lfinite$ ?v1 ))):named a14 ))
(assert (! (forall ((?v0 A_llist$ ))(=> (member$ ?v0 (collect$ uua$ ))(= (llist_of_stream$ (stream_of_llist$ ?v0 ))?v0 ))):named a15 ))
(assert (! (forall ((?v0 Nat$ ))(! (= (fun_app$e (ldropn$ ?v0 )lNil$ )lNil$ ):pattern ((ldropn$ ?v0 )))):named a16 ))
(assert (! (= (fun_app$ (lstrict_prefix$ lNil$ )lNil$ )false ):named a17 ))
(assert (! (forall ((?v0 A_stream$ )(?v1 A_stream$ ))(= (= (llist_of_stream$ ?v0 )(llist_of_stream$ ?v1 ))(= ?v0 ?v1 ))):named a18 ))
(assert (! (forall ((?v0 A_llist_bool_fun$ )(?v1 A_llist$ ))(=> (forall ((?v2 A_llist$ ))(=> (forall ((?v3 A_llist$ ))(=> (fun_app$ (lstrict_prefix$ ?v3 )?v2 )(fun_app$ ?v0 ?v3 )))(fun_app$ ?v0 ?v2 )))(fun_app$ ?v0 ?v1 ))):named a19 ))
(assert (! (forall ((?v0 A_llist$ )(?v1 A_llist_bool_fun$ ))(=> (and (member$ ?v0 (collect$ uua$ ))(forall ((?v2 A_stream$ ))(fun_app$ ?v1 (llist_of_stream$ ?v2 ))))(fun_app$ ?v1 ?v0 ))):named a20 ))
(check-sat )
;(get-unsat-core )
