;(set-option :produce-unsat-cores true )
(set-logic ALL_SUPPORTED )
(declare-sort A$ 0 )
(declare-sort A_llist_set$ 0 )
(declare-sort A_llist_bool_fun$ 0 )
(declare-sort A_llist_set_a_llist_fun$ 0 )
(declare-sort A_llist_a_llist_bool_fun_fun$ 0 )
(declare-codatatypes ()((A_llist$ (lNil$ )(lCons$ (lhd$ A$ )(ltl$ A_llist$ )))))
(declare-fun a$ ()A_llist_set$ )
(declare-fun bot$ ()A_llist_set$ )
(declare-fun lSup$ ()A_llist_set_a_llist_fun$ )
(declare-fun chain$ (A_llist_a_llist_bool_fun_fun$ A_llist_set$ )Bool )
(declare-fun lnull$ (A_llist$ )Bool )
(declare-fun finite$ (A_llist_set$ )Bool )
(declare-fun member$ (A_llist$ A_llist_set$ )Bool )
(declare-fun fun_app$ (A_llist_set_a_llist_fun$ A_llist_set$ )A_llist$ )
(declare-fun lfinite$ (A_llist$ )Bool )
(declare-fun lprefix$ ()A_llist_a_llist_bool_fun_fun$ )
(declare-fun fun_app$a (A_llist_bool_fun$ A_llist$ )Bool )
(declare-fun fun_app$b (A_llist_a_llist_bool_fun_fun$ A_llist$ )A_llist_bool_fun$ )
(declare-fun lub_singleton$ (A_llist_set_a_llist_fun$ )Bool )
(assert (! (not (member$ (fun_app$ lSup$ a$ )a$ )):named a0 ))
(assert (! (not (= a$ bot$ )):named a1 ))
(assert (! (finite$ a$ ):named a2 ))
(assert (! (chain$ lprefix$ a$ ):named a3 ))
(assert (! (and (finite$ a$ )(forall ((?v0 A_llist$ ))(=> (member$ ?v0 a$ )(lfinite$ ?v0 )))):named a4 ))
(assert (! (forall ((?v0 A_llist$ ))(=> (member$ ?v0 a$ )(lfinite$ ?v0 ))):named a5 ))
(assert (! (forall ((?v0 A_llist$ ))(fun_app$a (fun_app$b lprefix$ ?v0 )?v0 )):named a6 ))
(assert (! (forall ((?v0 A_llist$ ))(fun_app$a (fun_app$b lprefix$ ?v0 )?v0 )):named a7 ))
(assert (! (forall ((?v0 A_llist_set$ )(?v1 A_llist$ ))(=> (and (chain$ lprefix$ ?v0 )(forall ((?v2 A_llist$ ))(=> (member$ ?v2 ?v0 )(fun_app$a (fun_app$b lprefix$ ?v2 )?v1 ))))(fun_app$a (fun_app$b lprefix$ (fun_app$ lSup$ ?v0 ))?v1 ))):named a8 ))
(assert (! (forall ((?v0 A_llist_set$ )(?v1 A_llist$ ))(=> (and (chain$ lprefix$ ?v0 )(forall ((?v2 A_llist$ ))(=> (member$ ?v2 ?v0 )(fun_app$a (fun_app$b lprefix$ ?v2 )?v1 ))))(fun_app$a (fun_app$b lprefix$ (fun_app$ lSup$ ?v0 ))?v1 ))):named a9 ))
(assert (! (forall ((?v0 A_llist_set$ )(?v1 A_llist$ ))(=> (and (chain$ lprefix$ ?v0 )(member$ ?v1 ?v0 ))(fun_app$a (fun_app$b lprefix$ ?v1 )(fun_app$ lSup$ ?v0 )))):named a10 ))
(assert (! (forall ((?v0 A_llist_set$ )(?v1 A_llist$ ))(=> (and (chain$ lprefix$ ?v0 )(member$ ?v1 ?v0 ))(fun_app$a (fun_app$b lprefix$ ?v1 )(fun_app$ lSup$ ?v0 )))):named a11 ))
(assert (! (lub_singleton$ lSup$ ):named a12 ))
(assert (! (forall ((?v0 A_llist_set$ ))(= (lnull$ (fun_app$ lSup$ ?v0 ))(forall ((?v1 A_llist$ ))(=> (member$ ?v1 ?v0 )(lnull$ ?v1 ))))):named a13 ))
(assert (! (forall ((?v0 A_llist$ )(?v1 A_llist$ ))(=> (and (fun_app$a (fun_app$b lprefix$ ?v0 )?v1 )(fun_app$a (fun_app$b lprefix$ ?v1 )?v0 ))(= ?v0 ?v1 ))):named a14 ))
(assert (! (forall ((?v0 A_llist$ )(?v1 A_llist$ ))(=> (and (fun_app$a (fun_app$b lprefix$ ?v0 )?v1 )(fun_app$a (fun_app$b lprefix$ ?v1 )?v0 ))(= ?v0 ?v1 ))):named a15 ))
(assert (! (forall ((?v0 A_llist$ )(?v1 A_llist$ ))(=> (and (=> (or (lnull$ ?v0 )(lnull$ ?v1 ))false )(=> (and (not (lnull$ ?v0 ))(not (lnull$ ?v1 )))false ))false )):named a16 ))
(assert (! (forall ((?v0 A_llist_set$ ))(=> (and (=> (forall ((?v1 A_llist$ ))(=> (member$ ?v1 ?v0 )(lnull$ ?v1 )))false )(=> (not (forall ((?v1 A_llist$ ))(=> (member$ ?v1 ?v0 )(lnull$ ?v1 ))))false ))false )):named a17 ))
(check-sat )
;(get-unsat-core )
