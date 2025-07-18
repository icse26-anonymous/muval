;(set-option :produce-unsat-cores true )
(set-logic ALL_SUPPORTED )
(declare-sort A$ 0 )
(declare-sort A_list_set$ 0 )
(declare-sort A_list_bool_fun$ 0 )
(declare-sort A_list_a_llist_fun$ 0 )
(declare-sort A_llist_a_list_fun$ 0 )
(declare-sort A_llist$ 0)
(declare-fun lNil$ ()A_llist$)
(declare-fun lhd$ (A_llist$)A$)
(declare-fun ltl$ (A_llist$)A_llist$)
(declare-fun lCons$ (A$ A_llist$ )A_llist$)
(declare-datatypes ()((A_list$ (nil$ )(cons$ (hd$ A$ )(tl$ A_list$ )))))
(declare-fun top$ ()A_list_set$ )
(declare-fun top$a ()A_list_bool_fun$ )
(declare-fun top$b ()Bool )
(declare-fun inj_on$ (A_list_a_llist_fun$ A_list_set$ )Bool )
(declare-fun member$ (A_list$ A_list_set$ )Bool )
(declare-fun collect$ (A_list_bool_fun$ )A_list_set$ )
(declare-fun fun_app$ (A_list_a_llist_fun$ A_list$ )A_llist$ )
(declare-fun fun_app$a (A_list_bool_fun$ A_list$ )Bool )
(declare-fun fun_app$b (A_llist_a_list_fun$ A_llist$ )A_list$ )
(declare-fun llist_of$ ()A_list_a_llist_fun$ )
(assert (! (not (inj_on$ llist_of$ top$ )):named a0 ))
(assert (! (forall ((?v0 A_list$ )(?v1 A_list$ ))(= (= (fun_app$ llist_of$ ?v0 )(fun_app$ llist_of$ ?v1 ))(= ?v0 ?v1 ))):named a1 ))
(assert (! (forall ((?v0 A_list$ ))(= (member$ ?v0 top$ )true )):named a2 ))
(assert (! (forall ((?v0 A_list$ ))(member$ ?v0 top$ )):named a3 ))
(assert (! (forall ((?v0 A_list$ ))(! (= (fun_app$a top$a ?v0 )top$b ):pattern ((fun_app$a top$a ?v0 )))):named a4 ))
(assert (! (forall ((?v0 A_list_a_llist_fun$ ))(=> (forall ((?v1 A_list$ )(?v2 A_list$ ))(=> (= (fun_app$ ?v0 ?v1 )(fun_app$ ?v0 ?v2 ))(= ?v1 ?v2 )))(inj_on$ ?v0 top$ ))):named a5 ))
(assert (! (forall ((?v0 A_list_a_llist_fun$ )(?v1 A_list$ )(?v2 A_list$ ))(=> (and (inj_on$ ?v0 top$ )(= (fun_app$ ?v0 ?v1 )(fun_app$ ?v0 ?v2 )))(= ?v1 ?v2 ))):named a6 ))
(assert (! (forall ((?v0 A_list_a_llist_fun$ )(?v1 A_list$ )(?v2 A_list$ ))(=> (inj_on$ ?v0 top$ )(= (= (fun_app$ ?v0 ?v1 )(fun_app$ ?v0 ?v2 ))(= ?v1 ?v2 )))):named a7 ))
(assert (! (forall ((?v0 A_list_a_llist_fun$ )(?v1 A_list_set$ ))(= (inj_on$ ?v0 ?v1 )(forall ((?v2 A_list$ ))(=> (member$ ?v2 ?v1 )(forall ((?v3 A_list$ ))(=> (and (member$ ?v3 ?v1 )(= (fun_app$ ?v0 ?v2 )(fun_app$ ?v0 ?v3 )))(= ?v2 ?v3 ))))))):named a8 ))
(assert (! (forall ((?v0 A_list_set$ )(?v1 A_list_a_llist_fun$ )(?v2 A_list_a_llist_fun$ ))(=> (forall ((?v3 A_list$ ))(=> (member$ ?v3 ?v0 )(= (fun_app$ ?v1 ?v3 )(fun_app$ ?v2 ?v3 ))))(= (inj_on$ ?v1 ?v0 )(inj_on$ ?v2 ?v0 )))):named a9 ))
(assert (! (forall ((?v0 A_list_set$ )(?v1 A_llist_a_list_fun$ )(?v2 A_list_a_llist_fun$ ))(=> (forall ((?v3 A_list$ ))(=> (member$ ?v3 ?v0 )(= (fun_app$b ?v1 (fun_app$ ?v2 ?v3 ))?v3 )))(inj_on$ ?v2 ?v0 ))):named a10 ))
(assert (! (forall ((?v0 A_list_set$ )(?v1 A_list_a_llist_fun$ ))(=> (forall ((?v2 A_list$ )(?v3 A_list$ ))(=> (and (member$ ?v2 ?v0 )(and (member$ ?v3 ?v0 )(= (fun_app$ ?v1 ?v2 )(fun_app$ ?v1 ?v3 ))))(= ?v2 ?v3 )))(inj_on$ ?v1 ?v0 ))):named a11 ))
(assert (! (forall ((?v0 A_list_a_llist_fun$ )(?v1 A_list_set$ )(?v2 A_list$ )(?v3 A_list$ ))(=> (and (inj_on$ ?v0 ?v1 )(and (= (fun_app$ ?v0 ?v2 )(fun_app$ ?v0 ?v3 ))(and (member$ ?v2 ?v1 )(member$ ?v3 ?v1 ))))(= ?v2 ?v3 ))):named a12 ))
(assert (! (forall ((?v0 A_list_a_llist_fun$ )(?v1 A_list_set$ )(?v2 A_list$ )(?v3 A_list$ ))(=> (and (inj_on$ ?v0 ?v1 )(and (member$ ?v2 ?v1 )(member$ ?v3 ?v1 )))(= (= (fun_app$ ?v0 ?v2 )(fun_app$ ?v0 ?v3 ))(= ?v2 ?v3 )))):named a13 ))
(assert (! (= top$ (collect$ top$a )):named a14 ))
(assert (! (exists ((?v0 A_list$ ))(member$ ?v0 top$ )):named a15 ))
(assert (! (forall ((?v0 A_list_set$ ))(=> (forall ((?v1 A_list$ ))(member$ ?v1 ?v0 ))(= top$ ?v0 ))):named a16 ))
(assert (! (forall ((?v0 A_list_a_llist_fun$ )(?v1 A_list_set$ )(?v2 A_list$ )(?v3 A_list$ ))(=> (and (inj_on$ ?v0 ?v1 )(and (not (= ?v2 ?v3 ))(and (member$ ?v2 ?v1 )(member$ ?v3 ?v1 ))))(not (= (fun_app$ ?v0 ?v2 )(fun_app$ ?v0 ?v3 ))))):named a17 ))
(check-sat )
;(get-unsat-core )
