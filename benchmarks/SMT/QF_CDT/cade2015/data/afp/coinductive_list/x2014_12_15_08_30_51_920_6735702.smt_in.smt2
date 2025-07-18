;(set-option :produce-unsat-cores true )
(set-logic ALL_SUPPORTED )
(declare-sort A$ 0 )
(declare-sort A_set$ 0 )
(declare-sort A_bool_fun$ 0 )
(declare-sort Bool_bool_fun$ 0 )
(declare-sort A_llist_a_llist_fun$ 0 )
(declare-sort A_bool_fun_a_bool_fun_fun$ 0 )
(declare-sort A_llist$ 0)
(declare-fun lNil$ ()A_llist$)
(declare-fun lhd$ (A_llist$)A$)
(declare-fun ltl$ (A_llist$)A_llist$)
(declare-fun lCons$ (A$ A_llist$ )A_llist$)
(declare-fun p$ ()A_bool_fun$ )
(declare-fun x$ ()A$ )
(declare-fun id$ ()A_llist_a_llist_fun$ )
(declare-fun uu$ ()A_bool_fun$ )
(declare-fun xs$ ()A_llist$ )
(declare-fun ys$ ()A_llist$ )
(declare-fun uua$ ()Bool_bool_fun$ )
(declare-fun uub$ ()A_bool_fun$ )
(declare-fun uuc$ ()A_bool_fun$ )
(declare-fun comp$ (Bool_bool_fun$ )A_bool_fun_a_bool_fun_fun$ )
(declare-fun lset$ (A_llist$ )A_set$ )
(declare-fun lnull$ (A_llist$ )Bool )
(declare-fun member$ (A$ A_set$ )Bool )
(declare-fun fun_app$ (A_bool_fun$ A$ )Bool )
(declare-fun lfilter$ (A_bool_fun$ A_llist$ )A_llist$ )
(declare-fun fun_app$a (Bool_bool_fun$ Bool )Bool )
(declare-fun fun_app$b (A_llist_a_llist_fun$ A_llist$ )A_llist$ )
(declare-fun fun_app$c (A_bool_fun_a_bool_fun_fun$ A_bool_fun$ )A_bool_fun$ )
(declare-fun ldropWhile$ (A_bool_fun$ )A_llist_a_llist_fun$ )
(declare-fun ltakeWhile$ (A_bool_fun$ A_llist$ )A_llist$ )
(assert (! (forall ((?v0 A$ ))(! (= (fun_app$ uu$ ?v0 )(not (fun_app$ p$ ?v0 ))):pattern ((fun_app$ uu$ ?v0 )))):named a0 ))
(assert (! (forall ((?v0 Bool ))(! (= (fun_app$a uua$ ?v0 )(not ?v0 )):pattern ((fun_app$a uua$ ?v0 )))):named a1 ))
(assert (! (forall ((?v0 A$ ))(! (= (fun_app$ uuc$ ?v0 )false ):pattern ((fun_app$ uuc$ ?v0 )))):named a2 ))
(assert (! (forall ((?v0 A$ ))(! (= (fun_app$ uub$ ?v0 )true ):pattern ((fun_app$ uub$ ?v0 )))):named a3 ))
(assert (! (not (fun_app$ p$ (lhd$ (fun_app$b (ldropWhile$ uu$ )ys$ )))):named a4 ))
(assert (! (exists ((?v0 A$ ))(and (member$ ?v0 (lset$ ys$ ))(fun_app$ p$ ?v0 ))):named a5 ))
(assert (! (forall ((?v0 A_llist$ )(?v1 A_bool_fun$ ))(=> (exists ((?v2 A$ ))(and (member$ ?v2 (lset$ ?v0 ))(not (fun_app$ ?v1 ?v2 ))))(member$ (lhd$ (fun_app$b (ldropWhile$ ?v1 )?v0 ))(lset$ ?v0 )))):named a6 ))
(assert (! (forall ((?v0 A_llist$ )(?v1 A_bool_fun$ ))(=> (exists ((?v2 A$ ))(and (member$ ?v2 (lset$ ?v0 ))(not (fun_app$ ?v1 ?v2 ))))(not (fun_app$ ?v1 (lhd$ (fun_app$b (ldropWhile$ ?v1 )?v0 )))))):named a7 ))
(assert (! (= x$ (lhd$ (fun_app$b (ldropWhile$ (fun_app$c (comp$ uua$ )p$ ))ys$ ))):named a8 ))
(assert (! (forall ((?v0 A_llist$ )(?v1 A_llist$ )(?v2 A_bool_fun$ )(?v3 A_bool_fun$ ))(=> (and (= ?v0 ?v1 )(forall ((?v4 A$ ))(=> (member$ ?v4 (lset$ ?v1 ))(= (fun_app$ ?v2 ?v4 )(fun_app$ ?v3 ?v4 )))))(= (fun_app$b (ldropWhile$ ?v2 )?v0 )(fun_app$b (ldropWhile$ ?v3 )?v1 )))):named a9 ))
(assert (! (forall ((?v0 A$ )(?v1 A_bool_fun$ )(?v2 A_llist$ ))(=> (member$ ?v0 (lset$ (fun_app$b (ldropWhile$ ?v1 )?v2 )))(member$ ?v0 (lset$ ?v2 )))):named a10 ))
(assert (! (not (lnull$ (lfilter$ p$ ys$ ))):named a11 ))
(assert (! (forall ((?v0 A$ ))(=> (member$ ?v0 (lset$ (ltakeWhile$ (fun_app$c (comp$ uua$ )p$ )ys$ )))(not (fun_app$ p$ ?v0 )))):named a12 ))
(assert (! (= (lfilter$ p$ ys$ )(lCons$ x$ xs$ )):named a13 ))
(assert (! (forall ((?v0 A_llist$ ))(= (fun_app$b (ldropWhile$ uub$ )?v0 )lNil$ )):named a14 ))
(assert (! (= xs$ (ltl$ (lfilter$ p$ ys$ ))):named a15 ))
(assert (! (= (ldropWhile$ uuc$ )id$ ):named a16 ))
(assert (! (forall ((?v0 A$ )(?v1 A_llist$ )(?v2 A$ )(?v3 A_llist$ ))(= (= (lCons$ ?v0 ?v1 )(lCons$ ?v2 ?v3 ))(and (= ?v0 ?v2 )(= ?v1 ?v3 )))):named a17 ))
(assert (! (forall ((?v0 A_bool_fun$ )(?v1 A_llist$ ))(= (lfilter$ ?v0 (lfilter$ ?v0 ?v1 ))(lfilter$ ?v0 ?v1 ))):named a18 ))
(assert (! (forall ((?v0 A_llist$ ))(= (ltakeWhile$ uub$ ?v0 )?v0 )):named a19 ))
(assert (! (forall ((?v0 A_llist$ ))(= (lfilter$ uub$ ?v0 )?v0 )):named a20 ))
(check-sat )
;(get-unsat-core )
