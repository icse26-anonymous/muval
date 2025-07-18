;(set-option :produce-unsat-cores true )
(set-logic ALL_SUPPORTED )
(declare-sort A$ 0 )
(declare-sort B$ 0 )
(declare-sort A_set$ 0 )
(declare-sort A_bool_fun$ 0 )
(declare-sort B_bool_fun$ 0 )
(declare-sort Unit_b_fun$ 0 )
(declare-sort B_a_b_tllist_fun$ 0 )
(declare-sort A_b_tllist_bool_fun$ 0 )
(declare-sort A_a_b_tllist_bool_fun_fun$ 0 )
(declare-sort A_b_tllist$ 0)
(declare-fun terminal$ (A_b_tllist$)B$)
(declare-fun tNil$ (B$ )A_b_tllist$)
(declare-fun thd$ (A_b_tllist$)A$)
(declare-fun ttl$ (A_b_tllist$)A_b_tllist$)
(declare-fun tCons$ (A$ A_b_tllist$ )A_b_tllist$)
(declare-fun p$ (A_b_tllist$ )Bool )
(declare-fun x$ ()A$ )
(declare-fun xs$ ()A_b_tllist$ )
(declare-fun tset$ (A_b_tllist$ )A_set$ )
(declare-fun insert$ (A$ A_set$ )A_set$ )
(declare-fun member$ (A$ A_set$ )Bool )
(declare-fun fun_app$ (A_b_tllist_bool_fun$ A_b_tllist$ )Bool )
(declare-fun tappend$ (A_b_tllist$ B_a_b_tllist_fun$ )A_b_tllist$ )
(declare-fun tfilter$ (Unit_b_fun$ A_bool_fun$ A_b_tllist$ )A_b_tllist$ )
(declare-fun fun_app$a (A_a_b_tllist_bool_fun_fun$ A$ )A_b_tllist_bool_fun$ )
(declare-fun fun_app$b (A_bool_fun$ A$ )Bool )
(declare-fun fun_app$c (B_bool_fun$ B$ )Bool )
(declare-fun tfilter$a (B$ A_bool_fun$ A_b_tllist$ )A_b_tllist$ )
(declare-fun pred_tllist$ (A_bool_fun$ B_bool_fun$ A_b_tllist$ )Bool )
(assert (! (not (p$ xs$ )):named a0 ))
(assert (! (forall ((?v0 A_b_tllist$ ))(p$ (tCons$ x$ ?v0 ))):named a1 ))
(assert (! (forall ((?v0 A_b_tllist$ )(?v1 A$ ))(=> (and (member$ x$ (tset$ ?v0 ))(and (not (= x$ ?v1 ))(p$ ?v0 )))(p$ (tCons$ ?v1 ?v0 )))):named a2 ))
(assert (! (member$ x$ (tset$ xs$ )):named a3 ))
(assert (! (forall ((?v0 A$ )(?v1 A_b_tllist$ )(?v2 A$ )(?v3 A_b_tllist$ ))(= (= (tCons$ ?v0 ?v1 )(tCons$ ?v2 ?v3 ))(and (= ?v0 ?v2 )(= ?v1 ?v3 )))):named a4 ))
(assert (! (forall ((?v0 A$ )(?v1 A_b_tllist$ )(?v2 A_a_b_tllist_bool_fun_fun$ ))(=> (and (member$ ?v0 (tset$ ?v1 ))(and (forall ((?v3 A$ )(?v4 A_b_tllist$ ))(fun_app$ (fun_app$a ?v2 ?v3 )(tCons$ ?v3 ?v4 )))(forall ((?v3 A$ )(?v4 A_b_tllist$ )(?v5 A$ ))(=> (and (member$ ?v5 (tset$ ?v4 ))(fun_app$ (fun_app$a ?v2 ?v5 )?v4 ))(fun_app$ (fun_app$a ?v2 ?v5 )(tCons$ ?v3 ?v4 ))))))(fun_app$ (fun_app$a ?v2 ?v0 )?v1 ))):named a5 ))
(assert (! (forall ((?v0 A$ )(?v1 A_b_tllist$ ))(=> (and (member$ ?v0 (tset$ ?v1 ))(and (forall ((?v2 A_b_tllist$ ))(=> (= ?v1 (tCons$ ?v0 ?v2 ))false ))(forall ((?v2 A$ )(?v3 A_b_tllist$ ))(=> (and (= ?v1 (tCons$ ?v2 ?v3 ))(member$ ?v0 (tset$ ?v3 )))false ))))false )):named a6 ))
(assert (! (forall ((?v0 A$ )(?v1 A_b_tllist$ )(?v2 A$ ))(=> (member$ ?v0 (tset$ ?v1 ))(member$ ?v0 (tset$ (tCons$ ?v2 ?v1 ))))):named a7 ))
(assert (! (forall ((?v0 A$ )(?v1 A_b_tllist$ ))(member$ ?v0 (tset$ (tCons$ ?v0 ?v1 )))):named a8 ))
(assert (! (forall ((?v0 A_bool_fun$ )(?v1 B_bool_fun$ )(?v2 A$ )(?v3 A_b_tllist$ ))(! (= (pred_tllist$ ?v0 ?v1 (tCons$ ?v2 ?v3 ))(and (fun_app$b ?v0 ?v2 )(pred_tllist$ ?v0 ?v1 ?v3 ))):pattern ((pred_tllist$ ?v0 ?v1 (tCons$ ?v2 ?v3 ))))):named a9 ))
(assert (! (forall ((?v0 A$ )(?v1 A_b_tllist$ ))(! (= (tset$ (tCons$ ?v0 ?v1 ))(insert$ ?v0 (tset$ ?v1 ))):pattern ((tCons$ ?v0 ?v1 )))):named a10 ))
(assert (! (forall ((?v0 Unit_b_fun$ )(?v1 A_bool_fun$ )(?v2 A$ )(?v3 A_b_tllist$ ))(! (= (tfilter$ ?v0 ?v1 (tCons$ ?v2 ?v3 ))(ite (fun_app$b ?v1 ?v2 )(tCons$ ?v2 (tfilter$ ?v0 ?v1 ?v3 ))(tfilter$ ?v0 ?v1 ?v3 ))):pattern ((tfilter$ ?v0 ?v1 (tCons$ ?v2 ?v3 ))))):named a11 ))
(assert (! (forall ((?v0 B$ )(?v1 A_bool_fun$ )(?v2 A$ )(?v3 A_b_tllist$ ))(! (= (tfilter$a ?v0 ?v1 (tCons$ ?v2 ?v3 ))(ite (fun_app$b ?v1 ?v2 )(tCons$ ?v2 (tfilter$a ?v0 ?v1 ?v3 ))(tfilter$a ?v0 ?v1 ?v3 ))):pattern ((tfilter$a ?v0 ?v1 (tCons$ ?v2 ?v3 ))))):named a12 ))
(assert (! (forall ((?v0 A$ )(?v1 A_b_tllist$ )(?v2 B_a_b_tllist_fun$ ))(! (= (tappend$ (tCons$ ?v0 ?v1 )?v2 )(tCons$ ?v0 (tappend$ ?v1 ?v2 ))):pattern ((tappend$ (tCons$ ?v0 ?v1 )?v2 )))):named a13 ))
(assert (! (forall ((?v0 A_bool_fun$ )(?v1 B_bool_fun$ )(?v2 B$ ))(! (= (pred_tllist$ ?v0 ?v1 (tNil$ ?v2 ))(fun_app$c ?v1 ?v2 )):pattern ((pred_tllist$ ?v0 ?v1 (tNil$ ?v2 ))))):named a14 ))
(check-sat )
;(get-unsat-core )
