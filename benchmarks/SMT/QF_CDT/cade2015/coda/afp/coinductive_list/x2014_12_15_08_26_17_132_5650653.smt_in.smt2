;(set-option :produce-unsat-cores true )
(set-logic ALL_SUPPORTED )
(declare-sort A$ 0 )
(declare-sort A_llist_set$ 0 )
(declare-sort A_llist_bool_fun$ 0 )
(declare-sort A_llist_a_llist_bool_fun_fun$ 0 )
(declare-codatatypes ()((A_llist$ (lNil$ )(lCons$ (lhd$ A$ )(ltl$ A_llist$ )))))
(declare-fun ya$ ()A_llist_set$ )
(declare-fun lSup$ (A_llist_set$ )A_llist$ )
(declare-fun chain$ (A_llist_a_llist_bool_fun_fun$ A_llist_set$ )Bool )
(declare-fun lnull$ (A_llist$ )Bool )
(declare-fun member$ (A_llist$ A_llist_set$ )Bool )
(declare-fun fun_app$ (A_llist_bool_fun$ A_llist$ )Bool )
(declare-fun lprefix$ ()A_llist_a_llist_bool_fun_fun$ )
(declare-fun fun_app$a (A_llist_a_llist_bool_fun_fun$ A_llist$ )A_llist_bool_fun$ )
(declare-fun ldistinct$ (A_llist$ )Bool )
(assert (! (not (chain$ lprefix$ ya$ )):named a0 ))
(assert (! (forall ((?v0 A_llist$ ))(=> (member$ ?v0 ya$ )(ldistinct$ ?v0 ))):named a1 ))
(assert (! (not (lnull$ (lSup$ ya$ ))):named a2 ))
(assert (! (chain$ lprefix$ ya$ ):named a3 ))
(assert (! (forall ((?v0 A_llist$ ))(fun_app$ (fun_app$a lprefix$ ?v0 )?v0 )):named a4 ))
(assert (! (forall ((?v0 A_llist$ ))(fun_app$ (fun_app$a lprefix$ ?v0 )?v0 )):named a5 ))
(assert (! (forall ((?v0 A_llist$ )(?v1 A_llist$ ))(=> (and (fun_app$ (fun_app$a lprefix$ ?v0 )?v1 )(fun_app$ (fun_app$a lprefix$ ?v1 )?v0 ))(= ?v0 ?v1 ))):named a6 ))
(assert (! (forall ((?v0 A_llist$ )(?v1 A_llist$ ))(=> (and (fun_app$ (fun_app$a lprefix$ ?v0 )?v1 )(fun_app$ (fun_app$a lprefix$ ?v1 )?v0 ))(= ?v0 ?v1 ))):named a7 ))
(assert (! (forall ((?v0 A_llist$ )(?v1 A_llist$ )(?v2 A_llist$ ))(=> (and (fun_app$ (fun_app$a lprefix$ ?v0 )?v1 )(fun_app$ (fun_app$a lprefix$ ?v2 )?v1 ))(or (fun_app$ (fun_app$a lprefix$ ?v0 )?v2 )(fun_app$ (fun_app$a lprefix$ ?v2 )?v0 )))):named a8 ))
(assert (! (forall ((?v0 A_llist$ )(?v1 A_llist$ )(?v2 A_llist$ ))(=> (and (fun_app$ (fun_app$a lprefix$ ?v0 )?v1 )(fun_app$ (fun_app$a lprefix$ ?v1 )?v2 ))(fun_app$ (fun_app$a lprefix$ ?v0 )?v2 ))):named a9 ))
(assert (! (forall ((?v0 A_llist$ )(?v1 A_llist$ )(?v2 A_llist$ ))(=> (and (fun_app$ (fun_app$a lprefix$ ?v0 )?v1 )(fun_app$ (fun_app$a lprefix$ ?v1 )?v2 ))(fun_app$ (fun_app$a lprefix$ ?v0 )?v2 ))):named a10 ))
(assert (! (forall ((?v0 A_llist_set$ )(?v1 A_llist$ ))(=> (and (chain$ lprefix$ ?v0 )(forall ((?v2 A_llist$ ))(=> (member$ ?v2 ?v0 )(fun_app$ (fun_app$a lprefix$ ?v2 )?v1 ))))(fun_app$ (fun_app$a lprefix$ (lSup$ ?v0 ))?v1 ))):named a11 ))
(assert (! (forall ((?v0 A_llist_set$ )(?v1 A_llist$ ))(=> (and (chain$ lprefix$ ?v0 )(forall ((?v2 A_llist$ ))(=> (member$ ?v2 ?v0 )(fun_app$ (fun_app$a lprefix$ ?v2 )?v1 ))))(fun_app$ (fun_app$a lprefix$ (lSup$ ?v0 ))?v1 ))):named a12 ))
(assert (! (forall ((?v0 A_llist_set$ )(?v1 A_llist$ ))(=> (and (chain$ lprefix$ ?v0 )(member$ ?v1 ?v0 ))(fun_app$ (fun_app$a lprefix$ ?v1 )(lSup$ ?v0 )))):named a13 ))
(assert (! (forall ((?v0 A_llist_set$ )(?v1 A_llist$ ))(=> (and (chain$ lprefix$ ?v0 )(member$ ?v1 ?v0 ))(fun_app$ (fun_app$a lprefix$ ?v1 )(lSup$ ?v0 )))):named a14 ))
(assert (! (forall ((?v0 A_llist$ )(?v1 A_llist$ ))(=> (and (fun_app$ (fun_app$a lprefix$ ?v0 )?v1 )(not (lnull$ ?v0 )))(not (lnull$ ?v1 )))):named a15 ))
(assert (! (forall ((?v0 A_llist$ )(?v1 A_llist$ ))(=> (and (fun_app$ (fun_app$a lprefix$ ?v0 )?v1 )(lnull$ ?v1 ))(lnull$ ?v0 ))):named a16 ))
(assert (! (forall ((?v0 A_llist$ )(?v1 A_llist$ ))(! (=> (lnull$ ?v0 )(= (fun_app$ (fun_app$a lprefix$ ?v1 )?v0 )(lnull$ ?v1 ))):pattern ((fun_app$ (fun_app$a lprefix$ ?v1 )?v0 )))):named a17 ))
(check-sat )
;(get-unsat-core )
