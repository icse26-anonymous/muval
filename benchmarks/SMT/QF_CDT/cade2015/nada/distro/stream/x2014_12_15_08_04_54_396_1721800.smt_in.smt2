;(set-option :produce-unsat-cores true )
(set-logic ALL_SUPPORTED )
(declare-sort A$ 0 )
(declare-sort A_set$ 0 )
(declare-sort A_bool_fun$ 0 )
(declare-sort A_stream_bool_fun$ 0 )
(declare-sort A_a_stream_bool_fun_fun$ 0 )
(declare-sort A_stream$ 0)
(declare-fun shd$ (A_stream$)A$)
(declare-fun stl$ (A_stream$)A_stream$)
(declare-fun sCons$ (A$ A_stream$ )A_stream$)
(declare-fun s$ ()A_stream$ )
(declare-fun x$ ()A$ )
(declare-fun y$ ()A$ )
(declare-fun sset$ (A_stream$ )A_set$ )
(declare-fun insert$ (A$ A_set$ )A_set$ )
(declare-fun member$ (A$ A_set$ )Bool )
(declare-fun fun_app$ (A_stream_bool_fun$ A_stream$ )Bool )
(declare-fun smember$ (A$ A_stream$ )Bool )
(declare-fun fun_app$a (A_a_stream_bool_fun_fun$ A$ )A_stream_bool_fun$ )
(declare-fun fun_app$b (A_bool_fun$ A$ )Bool )
(declare-fun pred_stream$ (A_bool_fun$ A_stream$ )Bool )
(assert (! (not (= (member$ x$ (sset$ (sCons$ y$ s$ )))(ite (= x$ y$ )true (member$ x$ (sset$ s$ ))))):named a0 ))
(assert (! (forall ((?v0 A$ )(?v1 A_stream$ )(?v2 A$ )(?v3 A_stream$ ))(= (= (sCons$ ?v0 ?v1 )(sCons$ ?v2 ?v3 ))(and (= ?v0 ?v2 )(= ?v1 ?v3 )))):named a1 ))
(assert (! (forall ((?v0 A_stream$ ))(=> (forall ((?v1 A$ )(?v2 A_stream$ ))(=> (= ?v0 (sCons$ ?v1 ?v2 ))false ))false )):named a2 ))
(assert (! (forall ((?v0 A$ )(?v1 A_stream$ )(?v2 A_a_stream_bool_fun_fun$ ))(=> (and (member$ ?v0 (sset$ ?v1 ))(and (forall ((?v3 A$ )(?v4 A_stream$ ))(fun_app$ (fun_app$a ?v2 ?v3 )(sCons$ ?v3 ?v4 )))(forall ((?v3 A$ )(?v4 A_stream$ )(?v5 A$ ))(=> (and (member$ ?v5 (sset$ ?v4 ))(fun_app$ (fun_app$a ?v2 ?v5 )?v4 ))(fun_app$ (fun_app$a ?v2 ?v5 )(sCons$ ?v3 ?v4 ))))))(fun_app$ (fun_app$a ?v2 ?v0 )?v1 ))):named a3 ))
(assert (! (forall ((?v0 A$ )(?v1 A_stream$ ))(=> (and (member$ ?v0 (sset$ ?v1 ))(and (forall ((?v2 A_stream$ ))(=> (= ?v1 (sCons$ ?v0 ?v2 ))false ))(forall ((?v2 A$ )(?v3 A_stream$ ))(=> (and (= ?v1 (sCons$ ?v2 ?v3 ))(member$ ?v0 (sset$ ?v3 )))false ))))false )):named a4 ))
(assert (! (forall ((?v0 A$ )(?v1 A_stream$ )(?v2 A$ ))(=> (member$ ?v0 (sset$ ?v1 ))(member$ ?v0 (sset$ (sCons$ ?v2 ?v1 ))))):named a5 ))
(assert (! (forall ((?v0 A$ )(?v1 A_stream$ ))(member$ ?v0 (sset$ (sCons$ ?v0 ?v1 )))):named a6 ))
(assert (! (forall ((?v0 A$ )(?v1 A_stream$ ))(! (= (smember$ ?v0 ?v1 )(member$ ?v0 (sset$ ?v1 ))):pattern ((smember$ ?v0 ?v1 )))):named a7 ))
(assert (! (forall ((?v0 A_bool_fun$ )(?v1 A$ )(?v2 A_stream$ ))(! (= (pred_stream$ ?v0 (sCons$ ?v1 ?v2 ))(and (fun_app$b ?v0 ?v1 )(pred_stream$ ?v0 ?v2 ))):pattern ((pred_stream$ ?v0 (sCons$ ?v1 ?v2 ))))):named a8 ))
(assert (! (forall ((?v0 A$ )(?v1 A_stream$ ))(! (= (sset$ (sCons$ ?v0 ?v1 ))(insert$ ?v0 (sset$ ?v1 ))):pattern ((sCons$ ?v0 ?v1 )))):named a9 ))
(assert (! (forall ((?v0 A_stream$ ))(member$ (shd$ ?v0 )(sset$ ?v0 ))):named a10 ))
(assert (! (forall ((?v0 A$ )(?v1 A_stream$ ))(! (= (shd$ (sCons$ ?v0 ?v1 ))?v0 ):pattern ((sCons$ ?v0 ?v1 )))):named a11 ))
(assert (! (forall ((?v0 A$ )(?v1 A_stream$ ))(=> (member$ ?v0 (sset$ (stl$ ?v1 )))(member$ ?v0 (sset$ ?v1 )))):named a12 ))
(assert (! (forall ((?v0 A$ )(?v1 A_stream$ ))(! (= (stl$ (sCons$ ?v0 ?v1 ))?v1 ):pattern ((sCons$ ?v0 ?v1 )))):named a13 ))
(check-sat )
;(get-unsat-core )
