;(set-option :produce-unsat-cores true )
(set-logic ALL_SUPPORTED )
(declare-sort A$ 0 )
(declare-sort A_set$ 0 )
(declare-sort A_a_fun$ 0 )
(declare-sort A_bool_fun$ 0 )
(declare-sort A_llist_a_fun$ 0 )
(declare-sort A_a_bool_fun_fun$ 0 )
(declare-sort A_llist_bool_fun$ 0 )
(declare-sort A_llist_a_llist_fun$ 0 )
(declare-sort A_llist_a_llist_bool_fun_fun$ 0 )
(declare-codatatypes ()((A_llist$ (lNil$ )(lCons$ (lhd$ A$ )(ltl$ A_llist$ )))))
(declare-fun p$ (A$ A_llist$ )Bool )
(declare-fun x$ ()A$ )
(declare-fun uu$ ()A_llist_a_fun$ )
(declare-fun xs$ ()A_llist$ )
(declare-fun bot$ ()A_set$ )
(declare-fun uua$ ()A_llist_a_llist_fun$ )
(declare-fun lmap$ (A_a_fun$ A_llist$ )A_llist$ )
(declare-fun lset$ (A_llist$ )A_set$ )
(declare-fun lnull$ ()A_llist_bool_fun$ )
(declare-fun member$ (A$ A_set$ )Bool )
(declare-fun fun_app$ (A_llist_a_llist_fun$ A_llist$ )A_llist$ )
(declare-fun fun_app$a (A_llist_a_fun$ A_llist$ )A$ )
(declare-fun fun_app$b (A_llist_bool_fun$ A_llist$ )Bool )
(declare-fun fun_app$c (A_llist_a_llist_bool_fun_fun$ A_llist$ )A_llist_bool_fun$ )
(declare-fun fun_app$d (A_bool_fun$ A$ )Bool )
(declare-fun fun_app$e (A_a_bool_fun_fun$ A$ )A_bool_fun$ )
(declare-fun fun_app$f (A_a_fun$ A$ )A$ )
(declare-fun llist_all2$ (A_a_bool_fun_fun$ A_llist$ )A_llist_bool_fun$ )
(declare-fun unfold_llist$ (A_llist_bool_fun$ A_llist_a_fun$ A_llist_a_llist_fun$ A_llist$ )A_llist$ )
(assert (! (forall ((?v0 A_llist$ ))(! (= (fun_app$ uua$ ?v0 )(ltl$ ?v0 )):pattern ((fun_app$ uua$ ?v0 )))):named a0 ))
(assert (! (forall ((?v0 A_llist$ ))(! (= (fun_app$a uu$ ?v0 )(lhd$ ?v0 )):pattern ((fun_app$a uu$ ?v0 )))):named a1 ))
(assert (! (not (p$ x$ xs$ )):named a2 ))
(assert (! (forall ((?v0 A_llist$ ))(=> (not (fun_app$b lnull$ ?v0 ))(p$ (lhd$ ?v0 )?v0 ))):named a3 ))
(assert (! (forall ((?v0 A_llist$ )(?v1 A$ ))(=> (and (not (fun_app$b lnull$ ?v0 ))(and (member$ ?v1 (lset$ (ltl$ ?v0 )))(p$ ?v1 (ltl$ ?v0 ))))(p$ ?v1 ?v0 ))):named a4 ))
(assert (! (member$ x$ (lset$ xs$ )):named a5 ))
(assert (! (forall ((?v0 A_llist$ ))(=> (and (=> (fun_app$b lnull$ ?v0 )false )(=> (not (fun_app$b lnull$ ?v0 ))false ))false )):named a6 ))
(assert (! (forall ((?v0 A$ )(?v1 A_llist$ ))(=> (member$ ?v0 (lset$ (ltl$ ?v1 )))(member$ ?v0 (lset$ ?v1 )))):named a7 ))
(assert (! (forall ((?v0 A_llist$ ))(=> (not (fun_app$b lnull$ ?v0 ))(member$ (lhd$ ?v0 )(lset$ ?v0 )))):named a8 ))
(assert (! (forall ((?v0 A_llist$ )(?v1 A_llist$ ))(=> (and (= (fun_app$b lnull$ ?v0 )(fun_app$b lnull$ ?v1 ))(=> (and (not (fun_app$b lnull$ ?v0 ))(not (fun_app$b lnull$ ?v1 )))(and (= (lhd$ ?v0 )(lhd$ ?v1 ))(= (ltl$ ?v0 )(ltl$ ?v1 )))))(= ?v0 ?v1 ))):named a9 ))
(assert (! (forall ((?v0 A_llist_a_llist_bool_fun_fun$ )(?v1 A_llist$ )(?v2 A_llist$ ))(=> (and (fun_app$b (fun_app$c ?v0 ?v1 )?v2 )(forall ((?v3 A_llist$ )(?v4 A_llist$ ))(=> (fun_app$b (fun_app$c ?v0 ?v3 )?v4 )(and (= (fun_app$b lnull$ ?v3 )(fun_app$b lnull$ ?v4 ))(=> (and (not (fun_app$b lnull$ ?v3 ))(not (fun_app$b lnull$ ?v4 )))(and (= (lhd$ ?v3 )(lhd$ ?v4 ))(or (fun_app$b (fun_app$c ?v0 (ltl$ ?v3 ))(ltl$ ?v4 ))(= (ltl$ ?v3 )(ltl$ ?v4 )))))))))(= ?v1 ?v2 ))):named a10 ))
(assert (! (forall ((?v0 A_llist_a_llist_bool_fun_fun$ )(?v1 A_llist$ )(?v2 A_llist$ ))(=> (and (fun_app$b (fun_app$c ?v0 ?v1 )?v2 )(forall ((?v3 A_llist$ )(?v4 A_llist$ ))(=> (fun_app$b (fun_app$c ?v0 ?v3 )?v4 )(and (= (fun_app$b lnull$ ?v3 )(fun_app$b lnull$ ?v4 ))(=> (and (not (fun_app$b lnull$ ?v3 ))(not (fun_app$b lnull$ ?v4 )))(and (= (lhd$ ?v3 )(lhd$ ?v4 ))(fun_app$b (fun_app$c ?v0 (ltl$ ?v3 ))(ltl$ ?v4 ))))))))(= ?v1 ?v2 ))):named a11 ))
(assert (! (forall ((?v0 A_llist$ )(?v1 A$ ))(=> (and (not (fun_app$b lnull$ ?v0 ))(member$ ?v1 (lset$ (ltl$ ?v0 ))))(member$ ?v1 (lset$ ?v0 )))):named a12 ))
(assert (! (forall ((?v0 A_llist$ ))(= (unfold_llist$ lnull$ uu$ uua$ ?v0 )?v0 )):named a13 ))
(assert (! (forall ((?v0 A_llist$ ))(=> (not (fun_app$b lnull$ ?v0 ))(= (lCons$ (lhd$ ?v0 )(ltl$ ?v0 ))?v0 ))):named a14 ))
(assert (! (forall ((?v0 A_a_bool_fun_fun$ )(?v1 A_llist$ )(?v2 A_llist$ ))(= (fun_app$b (llist_all2$ ?v0 ?v1 )?v2 )(and (= (fun_app$b lnull$ ?v1 )(fun_app$b lnull$ ?v2 ))(=> (and (not (fun_app$b lnull$ ?v1 ))(not (fun_app$b lnull$ ?v2 )))(and (fun_app$d (fun_app$e ?v0 (lhd$ ?v1 ))(lhd$ ?v2 ))(fun_app$b (llist_all2$ ?v0 (ltl$ ?v1 ))(ltl$ ?v2 ))))))):named a15 ))
(assert (! (forall ((?v0 A_llist_a_llist_bool_fun_fun$ )(?v1 A_llist$ )(?v2 A_llist$ )(?v3 A_a_bool_fun_fun$ ))(=> (and (fun_app$b (fun_app$c ?v0 ?v1 )?v2 )(forall ((?v4 A_llist$ )(?v5 A_llist$ ))(=> (fun_app$b (fun_app$c ?v0 ?v4 )?v5 )(and (= (fun_app$b lnull$ ?v4 )(fun_app$b lnull$ ?v5 ))(=> (and (not (fun_app$b lnull$ ?v4 ))(not (fun_app$b lnull$ ?v5 )))(and (fun_app$d (fun_app$e ?v3 (lhd$ ?v4 ))(lhd$ ?v5 ))(fun_app$b (fun_app$c ?v0 (ltl$ ?v4 ))(ltl$ ?v5 ))))))))(fun_app$b (llist_all2$ ?v3 ?v1 )?v2 ))):named a16 ))
(assert (! (forall ((?v0 A_llist$ )(?v1 A_a_fun$ ))(=> (not (fun_app$b lnull$ ?v0 ))(= (lhd$ (lmap$ ?v1 ?v0 ))(fun_app$f ?v1 (lhd$ ?v0 ))))):named a17 ))
(assert (! (forall ((?v0 A_llist$ ))(= (= (lset$ ?v0 )bot$ )(fun_app$b lnull$ ?v0 ))):named a18 ))
(check-sat )
;(get-unsat-core )
