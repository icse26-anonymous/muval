;(set-option :produce-unsat-cores true )
(set-logic ALL_SUPPORTED )
(declare-sort A$ 0 )
(declare-sort B$ 0 )
(declare-sort A_bool_fun$ 0 )
(declare-sort A_a_bool_fun_fun$ 0 )
(declare-datatypes ()((Color$ (r$ )(b$ ))(A_b_rbt$ (empty$ )(branch$ (select$ Color$ )(selecta$ A_b_rbt$ )(selectb$ A$ )(selectc$ B$ )(selectd$ A_b_rbt$ )))))
(declare-fun v$ ()B$ )
(declare-fun xa$ ()A$ )
(declare-fun yy$ ()A$ )
(declare-fun zz$ ()A$ )
(declare-fun lta$ ()A_b_rbt$ )
(declare-fun rta$ ()A_b_rbt$ )
(declare-fun less$ ()A_a_bool_fun_fun$ )
(declare-fun fun_app$ (A_bool_fun$ A$ )Bool )
(declare-fun rbt_del$ (A_a_bool_fun_fun$ A$ A_b_rbt$ )A_b_rbt$ )
(declare-fun fun_app$a (A_a_bool_fun_fun$ A$ )A_bool_fun$ )
(declare-fun rbt_less$ (A_a_bool_fun_fun$ A$ A_b_rbt$ )Bool )
(assert (! (not (rbt_less$ less$ yy$ (rbt_del$ less$ xa$ (branch$ b$ lta$ zz$ v$ rta$ )))):named a0 ))
(assert (! (forall ((?v0 A$ )(?v1 A$ ))(= (not (fun_app$ (fun_app$a less$ ?v0 )?v1 ))(or (fun_app$ (fun_app$a less$ ?v1 )?v0 )(= ?v0 ?v1 )))):named a1 ))
(assert (! (forall ((?v0 A$ )(?v1 A$ ))(= (not (= ?v0 ?v1 ))(or (fun_app$ (fun_app$a less$ ?v0 )?v1 )(fun_app$ (fun_app$a less$ ?v1 )?v0 )))):named a2 ))
(assert (! (forall ((?v0 A$ )(?v1 A$ ))(=> (and (=> (fun_app$ (fun_app$a less$ ?v0 )?v1 )false )(and (=> (= ?v0 ?v1 )false )(=> (fun_app$ (fun_app$a less$ ?v1 )?v0 )false )))false )):named a3 ))
(assert (! (forall ((?v0 A$ )(?v1 A$ ))(=> (and (fun_app$ (fun_app$a less$ ?v0 )?v1 )(=> (not false )(fun_app$ (fun_app$a less$ ?v1 )?v0 )))false )):named a4 ))
(assert (! (forall ((?v0 A$ )(?v1 A$ )(?v2 A$ ))(=> (and (fun_app$ (fun_app$a less$ ?v0 )?v1 )(fun_app$ (fun_app$a less$ ?v1 )?v2 ))(fun_app$ (fun_app$a less$ ?v0 )?v2 ))):named a5 ))
(assert (! (forall ((?v0 A$ )(?v1 A$ )(?v2 A$ ))(=> (and (fun_app$ (fun_app$a less$ ?v0 )?v1 )(fun_app$ (fun_app$a less$ ?v1 )?v2 ))(fun_app$ (fun_app$a less$ ?v0 )?v2 ))):named a6 ))
(assert (! (forall ((?v0 A$ )(?v1 A$ )(?v2 A$ ))(=> (and (fun_app$ (fun_app$a less$ ?v0 )?v1 )(fun_app$ (fun_app$a less$ ?v2 )?v0 ))(fun_app$ (fun_app$a less$ ?v2 )?v1 ))):named a7 ))
(assert (! (forall ((?v0 A$ )(?v1 A$ ))(=> (and (fun_app$ (fun_app$a less$ ?v0 )?v1 )(fun_app$ (fun_app$a less$ ?v1 )?v0 ))false )):named a8 ))
(assert (! (forall ((?v0 A$ )(?v1 A$ ))(=> (and (fun_app$ (fun_app$a less$ ?v0 )?v1 )(fun_app$ (fun_app$a less$ ?v1 )?v0 ))false )):named a9 ))
(assert (! (forall ((?v0 A$ )(?v1 A$ ))(=> (and (fun_app$ (fun_app$a less$ ?v0 )?v1 )(fun_app$ (fun_app$a less$ ?v1 )?v0 ))false )):named a10 ))
(assert (! (forall ((?v0 A$ )(?v1 A$ )(?v2 A$ ))(=> (and (fun_app$ (fun_app$a less$ ?v0 )?v1 )(= ?v1 ?v2 ))(fun_app$ (fun_app$a less$ ?v0 )?v2 ))):named a11 ))
(assert (! (forall ((?v0 A$ )(?v1 A$ ))(=> (fun_app$ (fun_app$a less$ ?v0 )?v1 )(= (= ?v1 ?v0 )false ))):named a12 ))
(assert (! (forall ((?v0 A$ )(?v1 A$ ))(=> (fun_app$ (fun_app$a less$ ?v0 )?v1 )(= (= ?v0 ?v1 )false ))):named a13 ))
(assert (! (forall ((?v0 A$ )(?v1 A$ )(?v2 Bool ))(=> (fun_app$ (fun_app$a less$ ?v0 )?v1 )(= (=> (fun_app$ (fun_app$a less$ ?v1 )?v0 )?v2 )true ))):named a14 ))
(assert (! (forall ((?v0 A$ )(?v1 A$ ))(=> (fun_app$ (fun_app$a less$ ?v0 )?v1 )(= (not (fun_app$ (fun_app$a less$ ?v1 )?v0 ))true ))):named a15 ))
(assert (! (forall ((?v0 A$ )(?v1 A$ ))(=> (fun_app$ (fun_app$a less$ ?v0 )?v1 )(not (fun_app$ (fun_app$a less$ ?v1 )?v0 )))):named a16 ))
(assert (! (forall ((?v0 A$ )(?v1 A$ ))(=> (fun_app$ (fun_app$a less$ ?v0 )?v1 )(not (= ?v0 ?v1 )))):named a17 ))
(assert (! (forall ((?v0 A$ )(?v1 A$ ))(=> (fun_app$ (fun_app$a less$ ?v0 )?v1 )(not (= ?v0 ?v1 )))):named a18 ))
(assert (! (forall ((?v0 A$ )(?v1 A$ ))(=> (fun_app$ (fun_app$a less$ ?v0 )?v1 )(not (= ?v1 ?v0 )))):named a19 ))
(assert (! (forall ((?v0 A$ )(?v1 A$ )(?v2 A$ ))(=> (and (= ?v0 ?v1 )(fun_app$ (fun_app$a less$ ?v1 )?v2 ))(fun_app$ (fun_app$a less$ ?v0 )?v2 ))):named a20 ))
(assert (! (forall ((?v0 A$ )(?v1 A$ ))(=> (not (fun_app$ (fun_app$a less$ ?v0 )?v1 ))(= (not (fun_app$ (fun_app$a less$ ?v1 )?v0 ))(= ?v1 ?v0 )))):named a21 ))
(assert (! (forall ((?v0 A$ )(?v1 A$ ))(=> (and (not (= ?v0 ?v1 ))(and (=> (fun_app$ (fun_app$a less$ ?v0 )?v1 )false )(=> (fun_app$ (fun_app$a less$ ?v1 )?v0 )false )))false )):named a22 ))
(assert (! (forall ((?v0 A$ )(?v1 A$ ))(or (fun_app$ (fun_app$a less$ ?v0 )?v1 )(or (= ?v0 ?v1 )(fun_app$ (fun_app$a less$ ?v1 )?v0 )))):named a23 ))
(assert (! (forall ((?v0 A$ ))(not (fun_app$ (fun_app$a less$ ?v0 )?v0 ))):named a24 ))
(check-sat )
;(get-unsat-core )
