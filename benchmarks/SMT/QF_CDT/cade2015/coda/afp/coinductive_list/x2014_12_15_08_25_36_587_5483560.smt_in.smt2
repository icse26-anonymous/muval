;(set-option :produce-unsat-cores true )
(set-logic ALL_SUPPORTED )
(declare-sort A$ 0 )
(declare-sort Nat$ 0 )
(declare-sort A_set$ 0 )
(declare-sort A_bool_fun$ 0 )
(declare-sort A_a_bool_fun_fun$ 0 )
(declare-sort A_llist_bool_fun$ 0 )
(declare-sort A_llist_a_llist_bool_fun_fun$ 0 )
(declare-codatatypes ()((A_llist$ (lNil$ )(lCons$ (lhd$ A$ )(ltl$ A_llist$ )))))
(declare-fun p$ ()A_a_bool_fun_fun$ )
(declare-fun uu$ ()A_a_bool_fun_fun$ )
(declare-fun xs$ ()A_llist$ )
(declare-fun uua$ ()A_llist_a_llist_bool_fun_fun$ )
(declare-fun lset$ (A_llist$ )A_set$ )
(declare-fun lsetp$ (A_llist$ )A_bool_fun$ )
(declare-fun ldropn$ (Nat$ A_llist$ )A_llist$ )
(declare-fun member$ (A$ A_set$ )Bool )
(declare-fun fun_app$ (A_llist_bool_fun$ A_llist$ )Bool )
(declare-fun lmember$ (A$ A_llist$ )Bool )
(declare-fun fun_app$a (A_llist_a_llist_bool_fun_fun$ A_llist$ )A_llist_bool_fun$ )
(declare-fun fun_app$b (A_bool_fun$ A$ )Bool )
(declare-fun fun_app$c (A_a_bool_fun_fun$ A$ )A_bool_fun$ )
(declare-fun ldropWhile$ (A_bool_fun$ A_llist$ )A_llist$ )
(declare-fun llist_all2$ (A_a_bool_fun_fun$ )A_llist_a_llist_bool_fun_fun$ )
(assert (! (forall ((?v0 A_llist$ )(?v1 A_llist$ ))(! (= (fun_app$ (fun_app$a uua$ ?v0 )?v1 )(= ?v0 ?v1 )):pattern ((fun_app$ (fun_app$a uua$ ?v0 )?v1 )))):named a0 ))
(assert (! (forall ((?v0 A$ )(?v1 A$ ))(! (= (fun_app$b (fun_app$c uu$ ?v0 )?v1 )(= ?v0 ?v1 )):pattern ((fun_app$b (fun_app$c uu$ ?v0 )?v1 )))):named a1 ))
(assert (! (not (= (fun_app$ (fun_app$a (llist_all2$ p$ )xs$ )xs$ )(forall ((?v0 A$ ))(=> (member$ ?v0 (lset$ xs$ ))(fun_app$b (fun_app$c p$ ?v0 )?v0 ))))):named a2 ))
(assert (! (= (llist_all2$ uu$ )uua$ ):named a3 ))
(assert (! (forall ((?v0 A_llist$ )(?v1 A_a_bool_fun_fun$ ))(=> (forall ((?v2 A$ ))(=> (member$ ?v2 (lset$ ?v0 ))(fun_app$b (fun_app$c ?v1 ?v2 )?v2 )))(fun_app$ (fun_app$a (llist_all2$ ?v1 )?v0 )?v0 ))):named a4 ))
(assert (! (forall ((?v0 A_a_bool_fun_fun$ )(?v1 A_llist$ )(?v2 A_llist$ )(?v3 A_a_bool_fun_fun$ ))(=> (and (fun_app$ (fun_app$a (llist_all2$ ?v0 )?v1 )?v2 )(forall ((?v4 A$ )(?v5 A$ ))(=> (and (member$ ?v4 (lset$ ?v1 ))(and (member$ ?v5 (lset$ ?v2 ))(fun_app$b (fun_app$c ?v0 ?v4 )?v5 )))(fun_app$b (fun_app$c ?v3 ?v4 )?v5 ))))(fun_app$ (fun_app$a (llist_all2$ ?v3 )?v1 )?v2 ))):named a5 ))
(assert (! (forall ((?v0 A_a_bool_fun_fun$ )(?v1 A_llist$ )(?v2 A_llist$ )(?v3 A_a_bool_fun_fun$ ))(=> (and (fun_app$ (fun_app$a (llist_all2$ ?v0 )?v1 )?v2 )(forall ((?v4 A$ )(?v5 A$ ))(=> (fun_app$b (fun_app$c ?v0 ?v4 )?v5 )(fun_app$b (fun_app$c ?v3 ?v4 )?v5 ))))(fun_app$ (fun_app$a (llist_all2$ ?v3 )?v1 )?v2 ))):named a6 ))
(assert (! (forall ((?v0 A_a_bool_fun_fun$ )(?v1 A_llist$ )(?v2 A_llist$ )(?v3 A$ ))(=> (and (fun_app$ (fun_app$a (llist_all2$ ?v0 )?v1 )?v2 )(member$ ?v3 (lset$ ?v2 )))(exists ((?v4 A$ ))(and (member$ ?v4 (lset$ ?v1 ))(fun_app$b (fun_app$c ?v0 ?v4 )?v3 ))))):named a7 ))
(assert (! (forall ((?v0 A_a_bool_fun_fun$ )(?v1 A_llist$ )(?v2 A_llist$ )(?v3 A$ ))(=> (and (fun_app$ (fun_app$a (llist_all2$ ?v0 )?v1 )?v2 )(member$ ?v3 (lset$ ?v1 )))(exists ((?v4 A$ ))(and (member$ ?v4 (lset$ ?v2 ))(fun_app$b (fun_app$c ?v0 ?v3 )?v4 ))))):named a8 ))
(assert (! (forall ((?v0 A$ )(?v1 A_llist$ ))(= (member$ ?v0 (lset$ ?v1 ))(lmember$ ?v0 ?v1 ))):named a9 ))
(assert (! (forall ((?v0 A$ )(?v1 A_llist$ ))(=> (member$ ?v0 (lset$ ?v1 ))(fun_app$b (lsetp$ ?v1 )?v0 ))):named a10 ))
(assert (! (forall ((?v0 A_llist$ )(?v1 A$ ))(=> (fun_app$b (lsetp$ ?v0 )?v1 )(member$ ?v1 (lset$ ?v0 )))):named a11 ))
(assert (! (forall ((?v0 A_a_bool_fun_fun$ )(?v1 A_llist$ ))(! (= (fun_app$ (fun_app$a (llist_all2$ ?v0 )?v1 )lNil$ )(= ?v1 lNil$ )):pattern ((fun_app$a (llist_all2$ ?v0 )?v1 )))):named a12 ))
(assert (! (forall ((?v0 A_a_bool_fun_fun$ )(?v1 A_llist$ ))(! (= (fun_app$ (fun_app$a (llist_all2$ ?v0 )lNil$ )?v1 )(= ?v1 lNil$ )):pattern ((fun_app$ (fun_app$a (llist_all2$ ?v0 )lNil$ )?v1 )))):named a13 ))
(assert (! (forall ((?v0 A_a_bool_fun_fun$ )(?v1 A$ )(?v2 A_llist$ )(?v3 A$ )(?v4 A_llist$ ))(! (= (fun_app$ (fun_app$a (llist_all2$ ?v0 )(lCons$ ?v1 ?v2 ))(lCons$ ?v3 ?v4 ))(and (fun_app$b (fun_app$c ?v0 ?v1 )?v3 )(fun_app$ (fun_app$a (llist_all2$ ?v0 )?v2 )?v4 ))):pattern ((fun_app$ (fun_app$a (llist_all2$ ?v0 )(lCons$ ?v1 ?v2 ))(lCons$ ?v3 ?v4 ))))):named a14 ))
(assert (! (forall ((?v0 A_a_bool_fun_fun$ )(?v1 A_llist$ )(?v2 A_llist$ )(?v3 A_bool_fun$ )(?v4 A_bool_fun$ ))(=> (and (fun_app$ (fun_app$a (llist_all2$ ?v0 )?v1 )?v2 )(forall ((?v5 A$ )(?v6 A$ ))(=> (fun_app$b (fun_app$c ?v0 ?v5 )?v6 )(= (fun_app$b ?v3 ?v5 )(fun_app$b ?v4 ?v6 )))))(fun_app$ (fun_app$a (llist_all2$ ?v0 )(ldropWhile$ ?v3 ?v1 ))(ldropWhile$ ?v4 ?v2 )))):named a15 ))
(assert (! (forall ((?v0 A_llist$ )(?v1 A_llist$ )(?v2 A_bool_fun$ )(?v3 A_bool_fun$ ))(=> (and (= ?v0 ?v1 )(forall ((?v4 A$ ))(=> (member$ ?v4 (lset$ ?v1 ))(= (fun_app$b ?v2 ?v4 )(fun_app$b ?v3 ?v4 )))))(= (ldropWhile$ ?v2 ?v0 )(ldropWhile$ ?v3 ?v1 )))):named a16 ))
(assert (! (forall ((?v0 A$ )(?v1 A_bool_fun$ )(?v2 A_llist$ ))(=> (member$ ?v0 (lset$ (ldropWhile$ ?v1 ?v2 )))(member$ ?v0 (lset$ ?v2 )))):named a17 ))
(assert (! (forall ((?v0 A_a_bool_fun_fun$ )(?v1 A_llist$ )(?v2 A_llist$ )(?v3 Nat$ ))(=> (fun_app$ (fun_app$a (llist_all2$ ?v0 )?v1 )?v2 )(fun_app$ (fun_app$a (llist_all2$ ?v0 )(ldropn$ ?v3 ?v1 ))(ldropn$ ?v3 ?v2 )))):named a18 ))
(assert (! (forall ((?v0 A$ )(?v1 Nat$ )(?v2 A_llist$ ))(=> (member$ ?v0 (lset$ (ldropn$ ?v1 ?v2 )))(member$ ?v0 (lset$ ?v2 )))):named a19 ))
(check-sat )
;(get-unsat-core )
