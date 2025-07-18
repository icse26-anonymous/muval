;(set-option :produce-unsat-cores true )
(set-logic ALL_SUPPORTED )
(declare-sort A$ 0 )
(declare-sort A_set$ 0 )
(declare-sort A_llist_bool_fun$ 0 )
(declare-sort A_a_llist_bool_fun_fun$ 0 )
(declare-codatatypes ()((A_llist$ (lNil$ )(lCons$ (lhd$ A$ )(ltl$ A_llist$ )))))
(declare-fun x$ ()A$ )
(declare-fun xs$ ()A_llist$ )
(declare-fun lset$ (A_llist$ )A_set$ )
(declare-fun member$ (A$ A_set$ )Bool )
(declare-fun fun_app$ (A_llist_bool_fun$ A_llist$ )Bool )
(declare-fun lappend$ (A_llist$ A_llist$ )A_llist$ )
(declare-fun lfinite$ (A_llist$ )Bool )
(declare-fun fun_app$a (A_a_llist_bool_fun_fun$ A$ )A_llist_bool_fun$ )
(assert (! (not (exists ((?v0 A_llist$ )(?v1 A_llist$ ))(and (= xs$ (lappend$ ?v0 (lCons$ x$ ?v1 )))(and (lfinite$ ?v0 )(not (member$ x$ (lset$ ?v0 ))))))):named a0 ))
(assert (! (member$ x$ (lset$ xs$ )):named a1 ))
(assert (! (forall ((?v0 A$ )(?v1 A_llist$ )(?v2 A$ )(?v3 A_llist$ ))(= (= (lCons$ ?v0 ?v1 )(lCons$ ?v2 ?v3 ))(and (= ?v0 ?v2 )(= ?v1 ?v3 )))):named a2 ))
(assert (! (forall ((?v0 A$ )(?v1 A_llist$ )(?v2 A_llist$ ))(! (= (lappend$ (lCons$ ?v0 ?v1 )?v2 )(lCons$ ?v0 (lappend$ ?v1 ?v2 ))):pattern ((lappend$ (lCons$ ?v0 ?v1 )?v2 )))):named a3 ))
(assert (! (forall ((?v0 A$ )(?v1 A_llist$ ))(! (= (lfinite$ (lCons$ ?v0 ?v1 ))(lfinite$ ?v1 )):pattern ((lCons$ ?v0 ?v1 )))):named a4 ))
(assert (! (forall ((?v0 A$ )(?v1 A_llist$ ))(! (= (lfinite$ (lCons$ ?v0 ?v1 ))(lfinite$ ?v1 )):pattern ((lCons$ ?v0 ?v1 )))):named a5 ))
(assert (! (forall ((?v0 A_llist$ )(?v1 A_llist$ ))(= (lfinite$ (lappend$ ?v0 ?v1 ))(and (lfinite$ ?v0 )(lfinite$ ?v1 )))):named a6 ))
(assert (! (forall ((?v0 A$ )(?v1 A_llist$ )(?v2 A_llist$ ))(= (member$ ?v0 (lset$ (lappend$ ?v1 ?v2 )))(or (member$ ?v0 (lset$ ?v1 ))(and (lfinite$ ?v1 )(member$ ?v0 (lset$ ?v2 )))))):named a7 ))
(assert (! (forall ((?v0 A_llist$ )(?v1 A_llist$ )(?v2 A_llist$ ))(= (lappend$ (lappend$ ?v0 ?v1 )?v2 )(lappend$ ?v0 (lappend$ ?v1 ?v2 )))):named a8 ))
(assert (! (forall ((?v0 A$ )(?v1 A_llist$ )(?v2 A_a_llist_bool_fun_fun$ ))(=> (and (member$ ?v0 (lset$ ?v1 ))(and (forall ((?v3 A$ )(?v4 A_llist$ ))(fun_app$ (fun_app$a ?v2 ?v3 )(lCons$ ?v3 ?v4 )))(forall ((?v3 A$ )(?v4 A_llist$ )(?v5 A$ ))(=> (and (member$ ?v5 (lset$ ?v4 ))(fun_app$ (fun_app$a ?v2 ?v5 )?v4 ))(fun_app$ (fun_app$a ?v2 ?v5 )(lCons$ ?v3 ?v4 ))))))(fun_app$ (fun_app$a ?v2 ?v0 )?v1 ))):named a9 ))
(assert (! (forall ((?v0 A$ )(?v1 A_llist$ ))(=> (and (member$ ?v0 (lset$ ?v1 ))(and (forall ((?v2 A_llist$ ))(=> (= ?v1 (lCons$ ?v0 ?v2 ))false ))(forall ((?v2 A$ )(?v3 A_llist$ ))(=> (and (= ?v1 (lCons$ ?v2 ?v3 ))(member$ ?v0 (lset$ ?v3 )))false ))))false )):named a10 ))
(assert (! (forall ((?v0 A$ )(?v1 A_llist$ )(?v2 A_llist_bool_fun$ ))(=> (and (member$ ?v0 (lset$ ?v1 ))(and (forall ((?v3 A_llist$ ))(fun_app$ ?v2 (lCons$ ?v0 ?v3 )))(forall ((?v3 A$ )(?v4 A_llist$ ))(=> (and (member$ ?v0 (lset$ ?v4 ))(fun_app$ ?v2 ?v4 ))(fun_app$ ?v2 (lCons$ ?v3 ?v4 ))))))(fun_app$ ?v2 ?v1 ))):named a11 ))
(assert (! (forall ((?v0 A$ )(?v1 A_llist$ )(?v2 A_llist_bool_fun$ ))(=> (and (member$ ?v0 (lset$ ?v1 ))(and (forall ((?v3 A_llist$ ))(fun_app$ ?v2 (lCons$ ?v0 ?v3 )))(forall ((?v3 A$ )(?v4 A_llist$ ))(=> (and (member$ ?v0 (lset$ ?v4 ))(and (not (= ?v0 ?v3 ))(fun_app$ ?v2 ?v4 )))(fun_app$ ?v2 (lCons$ ?v3 ?v4 ))))))(fun_app$ ?v2 ?v1 ))):named a12 ))
(assert (! (forall ((?v0 A$ )(?v1 A_llist$ ))(=> (and (member$ ?v0 (lset$ ?v1 ))(and (forall ((?v2 A_llist$ ))(=> (= ?v1 (lCons$ ?v0 ?v2 ))false ))(forall ((?v2 A$ )(?v3 A_llist$ ))(=> (and (= ?v1 (lCons$ ?v2 ?v3 ))(member$ ?v0 (lset$ ?v3 )))false ))))false )):named a13 ))
(assert (! (forall ((?v0 A$ )(?v1 A_llist$ )(?v2 A$ ))(=> (member$ ?v0 (lset$ ?v1 ))(member$ ?v0 (lset$ (lCons$ ?v2 ?v1 ))))):named a14 ))
(assert (! (forall ((?v0 A$ )(?v1 A_llist$ )(?v2 A$ ))(=> (member$ ?v0 (lset$ ?v1 ))(member$ ?v0 (lset$ (lCons$ ?v2 ?v1 ))))):named a15 ))
(assert (! (forall ((?v0 A_llist$ )(?v1 A_llist$ ))(! (=> (not (lfinite$ ?v0 ))(= (lappend$ ?v0 ?v1 )?v0 )):pattern ((lappend$ ?v0 ?v1 )))):named a16 ))
(assert (! (forall ((?v0 A_llist$ )(?v1 A$ ))(=> (lfinite$ ?v0 )(lfinite$ (lCons$ ?v1 ?v0 )))):named a17 ))
(check-sat )
;(get-unsat-core )
