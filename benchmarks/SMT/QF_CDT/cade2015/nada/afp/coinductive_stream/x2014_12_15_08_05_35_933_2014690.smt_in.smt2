;(set-option :produce-unsat-cores true )
(set-logic ALL_SUPPORTED )
(declare-sort A$ 0 )
(declare-sort A_set$ 0 )
(declare-sort A_a_fun$ 0 )
(declare-sort A_bool_fun$ 0 )
(declare-sort A_a_a_fun_fun$ 0 )
(declare-sort A_stream_a_fun$ 0 )
(declare-sort A_stream_a_stream_fun$ 0 )
(declare-sort A_stream_a_stream_a_stream_fun_fun$ 0 )
(declare-sort A_stream_a_stream_fun_a_stream_a_stream_fun_fun$ 0 )
(declare-sort A_llist$ 0)
(declare-sort A_stream$ 0)
(declare-fun lNil$ ()A_llist$)
(declare-fun lhd$ (A_llist$)A$)
(declare-fun ltl$ (A_llist$)A_llist$)
(declare-fun lCons$ (A$ A_llist$ )A_llist$)
(declare-fun shd$ (A_stream$)A$)
(declare-fun stl$ (A_stream$)A_stream$)
(declare-fun sCons$ (A$ A_stream$ )A_stream$)
(declare-fun uu$ ()A_stream_a_fun$ )
(declare-fun xs$ ()A_stream$ )
(declare-fun hld$ (A_set$ A_stream$ )Bool )
(declare-fun uua$ ()A_stream_a_stream_fun$ )
(declare-fun holds$ (A_bool_fun$ A_stream$ )Bool )
(declare-fun lnull$ (A_llist$ )Bool )
(declare-fun smap2$ (A_a_a_fun_fun$ )A_stream_a_stream_a_stream_fun_fun$ )
(declare-fun member$ (A$ A_set$ )Bool )
(declare-fun fun_app$ (A_stream_a_stream_fun$ A_stream$ )A_stream$ )
(declare-fun fun_app$a (A_stream_a_fun$ A_stream$ )A$ )
(declare-fun fun_app$b (A_stream_a_stream_fun_a_stream_a_stream_fun_fun$ A_stream_a_stream_fun$ )A_stream_a_stream_fun$ )
(declare-fun fun_app$c (A_stream_a_stream_a_stream_fun_fun$ A_stream$ )A_stream_a_stream_fun$ )
(declare-fun fun_app$d (A_a_fun$ A$ )A$ )
(declare-fun fun_app$e (A_a_a_fun_fun$ A$ )A_a_fun$ )
(declare-fun fun_app$f (A_bool_fun$ A$ )Bool )
(declare-fun siterate$ (A_a_fun$ A$ )A_stream$ )
(declare-fun sinterleave$ (A_stream$ )A_stream_a_stream_fun$ )
(declare-fun unfold_stream$ (A_stream_a_fun$ )A_stream_a_stream_fun_a_stream_a_stream_fun_fun$ )
(declare-fun llist_of_stream$ (A_stream$ )A_llist$ )
(declare-fun stream_of_llist$ (A_llist$ )A_stream$ )
(assert (! (forall ((?v0 A_stream$ ))(! (= (fun_app$ uua$ ?v0 )(stl$ ?v0 )):pattern ((fun_app$ uua$ ?v0 )))):named a0 ))
(assert (! (forall ((?v0 A_stream$ ))(! (= (fun_app$a uu$ ?v0 )(shd$ ?v0 )):pattern ((fun_app$a uu$ ?v0 )))):named a1 ))
(assert (! (not (= (lhd$ (llist_of_stream$ xs$ ))(shd$ xs$ ))):named a2 ))
(assert (! (forall ((?v0 A_llist$ ))(= (shd$ (stream_of_llist$ ?v0 ))(lhd$ ?v0 ))):named a3 ))
(assert (! (forall ((?v0 A_stream_a_fun$ )(?v1 A_stream_a_stream_fun$ )(?v2 A_stream$ ))(= (shd$ (fun_app$ (fun_app$b (unfold_stream$ ?v0 )?v1 )?v2 ))(fun_app$a ?v0 ?v2 ))):named a4 ))
(assert (! (forall ((?v0 A_stream$ ))(not (lnull$ (llist_of_stream$ ?v0 )))):named a5 ))
(assert (! (forall ((?v0 A_stream$ )(?v1 A_stream$ ))(= (shd$ (fun_app$ (sinterleave$ ?v0 )?v1 ))(shd$ ?v0 ))):named a6 ))
(assert (! (forall ((?v0 A_set$ )(?v1 A_stream$ ))(! (= (hld$ ?v0 ?v1 )(member$ (shd$ ?v1 )?v0 )):pattern ((hld$ ?v0 ?v1 )))):named a7 ))
(assert (! (forall ((?v0 A_a_a_fun_fun$ )(?v1 A_stream$ )(?v2 A_stream$ ))(= (shd$ (fun_app$ (fun_app$c (smap2$ ?v0 )?v1 )?v2 ))(fun_app$d (fun_app$e ?v0 (shd$ ?v1 ))(shd$ ?v2 )))):named a8 ))
(assert (! (forall ((?v0 A_stream$ ))(= (ltl$ (llist_of_stream$ ?v0 ))(llist_of_stream$ (stl$ ?v0 )))):named a9 ))
(assert (! (forall ((?v0 A_bool_fun$ )(?v1 A_stream$ ))(! (= (holds$ ?v0 ?v1 )(fun_app$f ?v0 (shd$ ?v1 ))):pattern ((holds$ ?v0 ?v1 )))):named a10 ))
(assert (! (forall ((?v0 A_a_fun$ )(?v1 A$ ))(= (shd$ (siterate$ ?v0 ?v1 ))?v1 )):named a11 ))
(assert (! (forall ((?v0 A_stream$ ))(= (fun_app$ (fun_app$b (unfold_stream$ uu$ )uua$ )?v0 )?v0 )):named a12 ))
(check-sat )
;(get-unsat-core )
