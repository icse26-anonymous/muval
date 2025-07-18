;(set-option :produce-unsat-cores true )
(set-logic ALL_SUPPORTED )
(declare-sort A$ 0 )
(declare-sort A_set$ 0 )
(declare-sort A_bool_fun$ 0 )
(declare-sort A_llist_set$ 0 )
(declare-sort A_llist_bool_fun$ 0 )
(declare-sort A_llist_llist_set$ 0 )
(declare-codatatypes ()((A_llist$ (lNil$ )(lCons$ (lhd$ A$ )(ltl$ A_llist$ )))(A_llist_llist$ (lNil$a )(lCons$a (lhd$a A_llist$ )(ltl$a A_llist_llist$ )))))
(declare-fun p$ ()A_bool_fun$ )
(declare-fun uu$ ()A_llist_bool_fun$ )
(declare-fun ys$ ()A_llist$ )
(declare-fun uua$ ()A_bool_fun$ )
(declare-fun xsa$ ()A_llist$ )
(declare-fun lset$ (A_llist$ )A_set$ )
(declare-fun lnull$ (A_llist$ )Bool )
(declare-fun lset$a (A_llist_llist$ )A_llist_set$ )
(declare-fun lnull$a (A_llist_llist$ )Bool )
(declare-fun member$ (A$ A_set$ )Bool )
(declare-fun fun_app$ (A_llist_bool_fun$ A_llist$ )Bool )
(declare-fun lappend$ (A_llist$ A_llist$ )A_llist$ )
(declare-fun member$a (A_llist_llist$ A_llist_llist_set$ )Bool )
(declare-fun member$b (A_llist$ A_llist_set$ )Bool )
(declare-fun fun_app$a (A_bool_fun$ A$ )Bool )
(declare-fun lappend$a (A_llist_llist$ A_llist_llist$ )A_llist_llist$ )
(declare-fun ldropWhile$ (A_llist_bool_fun$ A_llist_llist$ )A_llist_llist$ )
(declare-fun ltakeWhile$ (A_bool_fun$ A_llist$ )A_llist$ )
(declare-fun ldropWhile$a (A_bool_fun$ A_llist$ )A_llist$ )
(declare-fun ltakeWhile$a (A_llist_bool_fun$ A_llist_llist$ )A_llist_llist$ )
(assert (! (forall ((?v0 A_llist$ ))(! (= (fun_app$ uu$ ?v0 )true ):pattern ((fun_app$ uu$ ?v0 )))):named a0 ))
(assert (! (forall ((?v0 A$ ))(! (= (fun_app$a uua$ ?v0 )true ):pattern ((fun_app$a uua$ ?v0 )))):named a1 ))
(assert (! (not (= (lnull$ (ltakeWhile$ p$ (lappend$ xsa$ ys$ )))(lnull$ (ite (exists ((?v0 A$ ))(and (member$ ?v0 (lset$ xsa$ ))(not (fun_app$a p$ ?v0 ))))(ltakeWhile$ p$ xsa$ )(lappend$ xsa$ (ltakeWhile$ p$ ys$ )))))):named a2 ))
(assert (! (forall ((?v0 A_llist_llist$ ))(= (ltakeWhile$a uu$ ?v0 )?v0 )):named a3 ))
(assert (! (forall ((?v0 A_llist$ ))(= (ltakeWhile$ uua$ ?v0 )?v0 )):named a4 ))
(assert (! (forall ((?v0 A_llist_llist$ )(?v1 A_llist_llist$ ))(= (not (lnull$a (lappend$a ?v0 ?v1 )))(or (not (lnull$a ?v0 ))(not (lnull$a ?v1 ))))):named a5 ))
(assert (! (forall ((?v0 A_llist$ )(?v1 A_llist$ ))(= (not (lnull$ (lappend$ ?v0 ?v1 )))(or (not (lnull$ ?v0 ))(not (lnull$ ?v1 ))))):named a6 ))
(assert (! (forall ((?v0 A_llist_llist$ )(?v1 A_llist_llist$ ))(= (lnull$a (lappend$a ?v0 ?v1 ))(and (lnull$a ?v0 )(lnull$a ?v1 )))):named a7 ))
(assert (! (forall ((?v0 A_llist$ )(?v1 A_llist$ ))(= (lnull$ (lappend$ ?v0 ?v1 ))(and (lnull$ ?v0 )(lnull$ ?v1 )))):named a8 ))
(assert (! (forall ((?v0 A_llist$ )(?v1 A_llist$ )(?v2 A_llist$ ))(= (lappend$ (lappend$ ?v0 ?v1 )?v2 )(lappend$ ?v0 (lappend$ ?v1 ?v2 )))):named a9 ))
(assert (! (forall ((?v0 A_llist$ )(?v1 A_llist_llist$ ))(=> (and (=> (or (lnull$ ?v0 )(lnull$a ?v1 ))false )(=> (and (not (lnull$ ?v0 ))(not (lnull$a ?v1 )))false ))false )):named a10 ))
(assert (! (forall ((?v0 A_llist_llist$ )(?v1 A_llist$ ))(=> (and (=> (or (lnull$a ?v0 )(lnull$ ?v1 ))false )(=> (and (not (lnull$a ?v0 ))(not (lnull$ ?v1 )))false ))false )):named a11 ))
(assert (! (forall ((?v0 A_llist_llist$ )(?v1 A_llist_llist$ ))(=> (and (=> (or (lnull$a ?v0 )(lnull$a ?v1 ))false )(=> (and (not (lnull$a ?v0 ))(not (lnull$a ?v1 )))false ))false )):named a12 ))
(assert (! (forall ((?v0 A_llist$ )(?v1 A_llist$ ))(=> (and (=> (or (lnull$ ?v0 )(lnull$ ?v1 ))false )(=> (and (not (lnull$ ?v0 ))(not (lnull$ ?v1 )))false ))false )):named a13 ))
(assert (! (forall ((?v0 A_llist_llist_set$ ))(=> (and (=> (forall ((?v1 A_llist_llist$ ))(=> (member$a ?v1 ?v0 )(lnull$a ?v1 )))false )(=> (not (forall ((?v1 A_llist_llist$ ))(=> (member$a ?v1 ?v0 )(lnull$a ?v1 ))))false ))false )):named a14 ))
(assert (! (forall ((?v0 A_llist_set$ ))(=> (and (=> (forall ((?v1 A_llist$ ))(=> (member$b ?v1 ?v0 )(lnull$ ?v1 )))false )(=> (not (forall ((?v1 A_llist$ ))(=> (member$b ?v1 ?v0 )(lnull$ ?v1 ))))false ))false )):named a15 ))
(assert (! (forall ((?v0 A_llist_llist$ )(?v1 A_llist_llist$ ))(=> (and (=> (and (lnull$a ?v0 )(lnull$a ?v1 ))false )(=> (or (not (lnull$a ?v0 ))(not (lnull$a ?v1 )))false ))false )):named a16 ))
(assert (! (forall ((?v0 A_llist$ )(?v1 A_llist$ ))(=> (and (=> (and (lnull$ ?v0 )(lnull$ ?v1 ))false )(=> (or (not (lnull$ ?v0 ))(not (lnull$ ?v1 )))false ))false )):named a17 ))
(assert (! (forall ((?v0 A_llist_llist$ ))(=> (and (=> (lnull$a ?v0 )false )(=> (not (lnull$a ?v0 ))false ))false )):named a18 ))
(assert (! (forall ((?v0 A_llist$ ))(=> (and (=> (lnull$ ?v0 )false )(=> (not (lnull$ ?v0 ))false ))false )):named a19 ))
(assert (! (forall ((?v0 A_llist_llist$ )(?v1 A_llist_llist$ ))(=> (or (not (lnull$a ?v0 ))(not (lnull$a ?v1 )))(not (lnull$a (lappend$a ?v0 ?v1 ))))):named a20 ))
(assert (! (forall ((?v0 A_llist$ )(?v1 A_llist$ ))(=> (or (not (lnull$ ?v0 ))(not (lnull$ ?v1 )))(not (lnull$ (lappend$ ?v0 ?v1 ))))):named a21 ))
(assert (! (forall ((?v0 A_llist_llist$ )(?v1 A_llist_bool_fun$ ))(! (=> (forall ((?v2 A_llist$ ))(=> (member$b ?v2 (lset$a ?v0 ))(fun_app$ ?v1 ?v2 )))(= (ltakeWhile$a ?v1 ?v0 )?v0 )):pattern ((ltakeWhile$a ?v1 ?v0 )))):named a22 ))
(assert (! (forall ((?v0 A_llist$ )(?v1 A_bool_fun$ ))(! (=> (forall ((?v2 A$ ))(=> (member$ ?v2 (lset$ ?v0 ))(fun_app$a ?v1 ?v2 )))(= (ltakeWhile$ ?v1 ?v0 )?v0 )):pattern ((ltakeWhile$ ?v1 ?v0 )))):named a23 ))
(assert (! (forall ((?v0 A_llist$ )(?v1 A_llist_bool_fun$ )(?v2 A_llist_llist$ ))(=> (member$b ?v0 (lset$a (ltakeWhile$a ?v1 ?v2 )))(and (member$b ?v0 (lset$a ?v2 ))(fun_app$ ?v1 ?v0 )))):named a24 ))
(assert (! (forall ((?v0 A$ )(?v1 A_bool_fun$ )(?v2 A_llist$ ))(=> (member$ ?v0 (lset$ (ltakeWhile$ ?v1 ?v2 )))(and (member$ ?v0 (lset$ ?v2 ))(fun_app$a ?v1 ?v0 )))):named a25 ))
(assert (! (forall ((?v0 A_llist_llist$ )(?v1 A_llist_llist$ ))(=> (and (lnull$a ?v0 )(lnull$a ?v1 ))(lnull$a (lappend$a ?v0 ?v1 )))):named a26 ))
(assert (! (forall ((?v0 A_llist$ )(?v1 A_llist$ ))(=> (and (lnull$ ?v0 )(lnull$ ?v1 ))(lnull$ (lappend$ ?v0 ?v1 )))):named a27 ))
(assert (! (forall ((?v0 A_llist_llist$ )(?v1 A_llist_llist$ ))(! (=> (lnull$a ?v0 )(= (lappend$a ?v1 ?v0 )?v1 )):pattern ((lappend$a ?v1 ?v0 )))):named a28 ))
(assert (! (forall ((?v0 A_llist$ )(?v1 A_llist$ ))(! (=> (lnull$ ?v0 )(= (lappend$ ?v1 ?v0 )?v1 )):pattern ((lappend$ ?v1 ?v0 )))):named a29 ))
(assert (! (forall ((?v0 A_llist_llist$ )(?v1 A_llist_llist$ ))(! (=> (lnull$a ?v0 )(= (lappend$a ?v0 ?v1 )?v1 )):pattern ((lappend$a ?v0 ?v1 )))):named a30 ))
(assert (! (forall ((?v0 A_llist$ )(?v1 A_llist$ ))(! (=> (lnull$ ?v0 )(= (lappend$ ?v0 ?v1 )?v1 )):pattern ((lappend$ ?v0 ?v1 )))):named a31 ))
(assert (! (forall ((?v0 A_llist_bool_fun$ )(?v1 A_llist_llist$ ))(= (lappend$a (ltakeWhile$a ?v0 ?v1 )(ldropWhile$ ?v0 ?v1 ))?v1 )):named a32 ))
(assert (! (forall ((?v0 A_bool_fun$ )(?v1 A_llist$ ))(= (lappend$ (ltakeWhile$ ?v0 ?v1 )(ldropWhile$a ?v0 ?v1 ))?v1 )):named a33 ))
(assert (! (forall ((?v0 A_llist_bool_fun$ )(?v1 A_llist_llist$ ))(= (lnull$a (ldropWhile$ ?v0 ?v1 ))(forall ((?v2 A_llist$ ))(=> (member$b ?v2 (lset$a ?v1 ))(fun_app$ ?v0 ?v2 ))))):named a34 ))
(assert (! (forall ((?v0 A_bool_fun$ )(?v1 A_llist$ ))(= (lnull$ (ldropWhile$a ?v0 ?v1 ))(forall ((?v2 A$ ))(=> (member$ ?v2 (lset$ ?v1 ))(fun_app$a ?v0 ?v2 ))))):named a35 ))
(assert (! (forall ((?v0 A_llist_set$ )(?v1 A_llist_bool_fun$ ))(= (exists ((?v2 A_llist$ ))(and (member$b ?v2 ?v0 )(fun_app$ ?v1 ?v2 )))(exists ((?v2 A_llist$ ))(and (member$b ?v2 ?v0 )(fun_app$ ?v1 ?v2 ))))):named a36 ))
(assert (! (forall ((?v0 A_set$ )(?v1 A_bool_fun$ ))(= (exists ((?v2 A$ ))(and (member$ ?v2 ?v0 )(fun_app$a ?v1 ?v2 )))(exists ((?v2 A$ ))(and (member$ ?v2 ?v0 )(fun_app$a ?v1 ?v2 ))))):named a37 ))
(check-sat )
;(get-unsat-core )
