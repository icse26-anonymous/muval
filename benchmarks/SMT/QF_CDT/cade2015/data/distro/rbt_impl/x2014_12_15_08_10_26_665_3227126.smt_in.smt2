;(set-option :produce-unsat-cores true )
(set-logic ALL_SUPPORTED )
(declare-sort A$ 0 )
(declare-sort B$ 0 )
(declare-sort Nat$ 0 )
(declare-sort A_bool_fun$ 0 )
(declare-sort A_a_bool_fun_fun$ 0 )
(declare-datatypes ()((Color$ (r$ )(b$ ))(A_b_rbt$ (empty$ )(branch$ (select$ Color$ )(selecta$ A_b_rbt$ )(selectb$ A$ )(selectc$ B$ )(selectd$ A_b_rbt$ )))))
(declare-fun y$ ()A$ )
(declare-fun z$ ()A$ )
(declare-fun bb$ ()A_b_rbt$ )
(declare-fun lt$ ()A_b_rbt$ )
(declare-fun ss$ ()B$ )
(declare-fun va$ ()B$ )
(declare-fun y$a ()A$ )
(declare-fun lta$ ()A_b_rbt$ )
(declare-fun rta$ ()A_b_rbt$ )
(declare-fun inv1$ (A_b_rbt$ )Bool )
(declare-fun inv2$ (A_b_rbt$ )Bool )
(declare-fun less$ ()A_a_bool_fun_fun$ )
(declare-fun inv1l$ (A_b_rbt$ )Bool )
(declare-fun bheight$ (A_b_rbt$ )Nat$ )
(declare-fun fun_app$ (A_bool_fun$ A$ )Bool )
(declare-fun color_of$ (A_b_rbt$ )Color$ )
(declare-fun fun_app$a (A_a_bool_fun_fun$ A$ )A_bool_fun$ )
(declare-fun rbt_del_from_left$ (A_a_bool_fun_fun$ A$ A_b_rbt$ A$ B$ A_b_rbt$ )A_b_rbt$ )
(assert (! (not (and (inv2$ (rbt_del_from_left$ less$ y$ (branch$ b$ lta$ z$ va$ rta$ )y$a ss$ bb$ ))(and (= (bheight$ (rbt_del_from_left$ less$ y$ (branch$ b$ lta$ z$ va$ rta$ )y$a ss$ bb$ ))(bheight$ (branch$ b$ lta$ z$ va$ rta$ )))(or (and (= (color_of$ (branch$ b$ lta$ z$ va$ rta$ ))b$ )(and (= (color_of$ bb$ )b$ )(inv1$ (rbt_del_from_left$ less$ y$ (branch$ b$ lta$ z$ va$ rta$ )y$a ss$ bb$ ))))(and (or (not (= (color_of$ (branch$ b$ lta$ z$ va$ rta$ ))b$ ))(not (= (color_of$ bb$ )b$ )))(inv1l$ (rbt_del_from_left$ less$ y$ (branch$ b$ lta$ z$ va$ rta$ )y$a ss$ bb$ ))))))):named a0 ))
(assert (! (inv1$ lt$ ):named a1 ))
(assert (! (inv2$ lt$ ):named a2 ))
(assert (! (inv1$ bb$ ):named a3 ))
(assert (! (inv2$ bb$ ):named a4 ))
(assert (! (forall ((?v0 A$ )(?v1 A$ ))(= (not (fun_app$ (fun_app$a less$ ?v0 )?v1 ))(or (fun_app$ (fun_app$a less$ ?v1 )?v0 )(= ?v0 ?v1 )))):named a5 ))
(assert (! (forall ((?v0 A$ )(?v1 A$ ))(= (not (= ?v0 ?v1 ))(or (fun_app$ (fun_app$a less$ ?v0 )?v1 )(fun_app$ (fun_app$a less$ ?v1 )?v0 )))):named a6 ))
(assert (! (forall ((?v0 A$ )(?v1 A$ ))(=> (and (=> (fun_app$ (fun_app$a less$ ?v0 )?v1 )false )(and (=> (= ?v0 ?v1 )false )(=> (fun_app$ (fun_app$a less$ ?v1 )?v0 )false )))false )):named a7 ))
(assert (! (forall ((?v0 A$ )(?v1 A$ ))(=> (and (fun_app$ (fun_app$a less$ ?v0 )?v1 )(=> (not false )(fun_app$ (fun_app$a less$ ?v1 )?v0 )))false )):named a8 ))
(assert (! (forall ((?v0 A$ )(?v1 A$ )(?v2 A$ ))(=> (and (fun_app$ (fun_app$a less$ ?v0 )?v1 )(fun_app$ (fun_app$a less$ ?v1 )?v2 ))(fun_app$ (fun_app$a less$ ?v0 )?v2 ))):named a9 ))
(assert (! (forall ((?v0 A$ )(?v1 A$ )(?v2 A$ ))(=> (and (fun_app$ (fun_app$a less$ ?v0 )?v1 )(fun_app$ (fun_app$a less$ ?v1 )?v2 ))(fun_app$ (fun_app$a less$ ?v0 )?v2 ))):named a10 ))
(assert (! (forall ((?v0 A$ )(?v1 A$ )(?v2 A$ ))(=> (and (fun_app$ (fun_app$a less$ ?v0 )?v1 )(fun_app$ (fun_app$a less$ ?v2 )?v0 ))(fun_app$ (fun_app$a less$ ?v2 )?v1 ))):named a11 ))
(assert (! (forall ((?v0 A$ )(?v1 A$ ))(=> (and (fun_app$ (fun_app$a less$ ?v0 )?v1 )(fun_app$ (fun_app$a less$ ?v1 )?v0 ))false )):named a12 ))
(assert (! (forall ((?v0 A$ )(?v1 A$ ))(=> (and (fun_app$ (fun_app$a less$ ?v0 )?v1 )(fun_app$ (fun_app$a less$ ?v1 )?v0 ))false )):named a13 ))
(assert (! (forall ((?v0 A$ )(?v1 A$ ))(=> (and (fun_app$ (fun_app$a less$ ?v0 )?v1 )(fun_app$ (fun_app$a less$ ?v1 )?v0 ))false )):named a14 ))
(assert (! (forall ((?v0 A$ )(?v1 A$ )(?v2 A$ ))(=> (and (fun_app$ (fun_app$a less$ ?v0 )?v1 )(= ?v1 ?v2 ))(fun_app$ (fun_app$a less$ ?v0 )?v2 ))):named a15 ))
(assert (! (forall ((?v0 A$ )(?v1 A$ ))(=> (fun_app$ (fun_app$a less$ ?v0 )?v1 )(= (= ?v1 ?v0 )false ))):named a16 ))
(assert (! (forall ((?v0 A$ )(?v1 A$ ))(=> (fun_app$ (fun_app$a less$ ?v0 )?v1 )(= (= ?v0 ?v1 )false ))):named a17 ))
(check-sat )
;(get-unsat-core )
