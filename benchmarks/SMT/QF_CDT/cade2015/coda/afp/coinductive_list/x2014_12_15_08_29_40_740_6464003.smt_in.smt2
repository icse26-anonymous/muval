;(set-option :produce-unsat-cores true )
(set-logic ALL_SUPPORTED )
(declare-sort A$ 0 )
(declare-sort A_set$ 0 )
(declare-sort A_bool_fun$ 0 )
(declare-sort A_llist_bool_fun$ 0 )
(declare-sort A_llist_a_set_fun$ 0 )
(declare-sort A_llist_a_llist_fun$ 0 )
(declare-codatatypes ()((A_llist$ (lNil$ )(lCons$ (lhd$ A$ )(ltl$ A_llist$ )))))
(declare-fun p$ ()A_bool_fun$ )
(declare-fun xs$ ()A_llist$ )
(declare-fun bot$ ()A_set$ )
(declare-fun lset$ (A_llist$ )A_set$ )
(declare-fun lsetp$ (A_llist$ )A_bool_fun$ )
(declare-fun member$ (A$ A_set$ )Bool )
(declare-fun fun_app$ (A_llist_a_llist_fun$ A_llist$ )A_llist$ )
(declare-fun lfilter$ (A_bool_fun$ )A_llist_a_llist_fun$ )
(declare-fun lmember$ (A$ )A_llist_bool_fun$ )
(declare-fun fun_app$a (A_bool_fun$ A$ )Bool )
(declare-fun fun_app$b (A_llist_bool_fun$ A_llist$ )Bool )
(declare-fun fun_app$c (A_llist_a_set_fun$ A_llist$ )A_set$ )
(declare-fun gen_lset$ (A_set$ )A_llist_a_set_fun$ )
(declare-fun ldropWhile$ (A_bool_fun$ )A_llist_a_llist_fun$ )
(declare-fun pred_llist$ (A_bool_fun$ )A_llist_bool_fun$ )
(declare-fun finite_lprefix$ (A_llist$ )A_llist_bool_fun$ )
(declare-fun lstrict_prefix$ (A_llist$ )A_llist_bool_fun$ )
(assert (! (not (= (= (fun_app$ (lfilter$ p$ )xs$ )lNil$ )(forall ((?v0 A$ ))(=> (member$ ?v0 (lset$ xs$ ))(not (fun_app$a p$ ?v0 )))))):named a0 ))
(assert (! (forall ((?v0 A_bool_fun$ ))(! (= (fun_app$ (lfilter$ ?v0 )lNil$ )lNil$ ):pattern ((lfilter$ ?v0 )))):named a1 ))
(assert (! (forall ((?v0 A_llist$ )(?v1 A_bool_fun$ ))(! (=> (forall ((?v2 A$ ))(=> (member$ ?v2 (lset$ ?v0 ))(not (fun_app$a ?v1 ?v2 ))))(= (fun_app$ (lfilter$ ?v1 )?v0 )lNil$ )):pattern ((fun_app$ (lfilter$ ?v1 )?v0 )))):named a2 ))
(assert (! (forall ((?v0 A_bool_fun$ )(?v1 A_llist$ ))(= (= (fun_app$ (lfilter$ ?v0 )?v1 )lNil$ )(forall ((?v2 A$ ))(=> (member$ ?v2 (lset$ ?v1 ))(not (fun_app$a ?v0 ?v2 )))))):named a3 ))
(assert (! (forall ((?v0 A$ )(?v1 A_llist$ ))(= (member$ ?v0 (lset$ ?v1 ))(fun_app$b (lmember$ ?v0 )?v1 ))):named a4 ))
(assert (! (forall ((?v0 A$ ))(! (= (fun_app$b (lmember$ ?v0 )lNil$ )false ):pattern ((lmember$ ?v0 )))):named a5 ))
(assert (! (forall ((?v0 A_set$ ))(! (= (fun_app$c (gen_lset$ ?v0 )lNil$ )?v0 ):pattern ((gen_lset$ ?v0 )))):named a6 ))
(assert (! (forall ((?v0 A_llist$ ))(! (= (fun_app$b (finite_lprefix$ ?v0 )lNil$ )(= ?v0 lNil$ )):pattern ((finite_lprefix$ ?v0 )))):named a7 ))
(assert (! (forall ((?v0 A_llist$ ))(! (= (fun_app$b (finite_lprefix$ lNil$ )?v0 )true ):pattern ((fun_app$b (finite_lprefix$ lNil$ )?v0 )))):named a8 ))
(assert (! (= (fun_app$b (lstrict_prefix$ lNil$ )lNil$ )false ):named a9 ))
(assert (! (forall ((?v0 A_bool_fun$ ))(fun_app$b (pred_llist$ ?v0 )lNil$ )):named a10 ))
(assert (! (forall ((?v0 A_bool_fun$ )(?v1 A_llist$ ))(= (= (fun_app$ (ldropWhile$ ?v0 )?v1 )lNil$ )(forall ((?v2 A$ ))(=> (member$ ?v2 (lset$ ?v1 ))(fun_app$a ?v0 ?v2 ))))):named a11 ))
(assert (! (= (lset$ lNil$ )bot$ ):named a12 ))
(assert (! (forall ((?v0 A$ )(?v1 A_llist$ ))(=> (member$ ?v0 (lset$ ?v1 ))(fun_app$a (lsetp$ ?v1 )?v0 ))):named a13 ))
(assert (! (forall ((?v0 A_llist$ )(?v1 A$ ))(=> (fun_app$a (lsetp$ ?v0 )?v1 )(member$ ?v1 (lset$ ?v0 )))):named a14 ))
(assert (! (forall ((?v0 A_bool_fun$ ))(! (= (fun_app$ (ldropWhile$ ?v0 )lNil$ )lNil$ ):pattern ((ldropWhile$ ?v0 )))):named a15 ))
(assert (! (forall ((?v0 A_llist_bool_fun$ )(?v1 A_llist$ ))(=> (forall ((?v2 A_llist$ ))(=> (forall ((?v3 A_llist$ ))(=> (fun_app$b (lstrict_prefix$ ?v3 )?v2 )(fun_app$b ?v0 ?v3 )))(fun_app$b ?v0 ?v2 )))(fun_app$b ?v0 ?v1 ))):named a16 ))
(check-sat )
;(get-unsat-core )
