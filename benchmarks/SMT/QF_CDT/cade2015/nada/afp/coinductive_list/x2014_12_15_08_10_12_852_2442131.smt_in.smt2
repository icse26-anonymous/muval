;(set-option :produce-unsat-cores true )
(set-logic ALL_SUPPORTED )
(declare-sort A$ 0 )
(declare-sort A_llist_set$ 0 )
(declare-sort A_llist_bool_fun$ 0 )
(declare-sort A_llist$ 0)
(declare-fun lNil$ ()A_llist$)
(declare-fun lhd$ (A_llist$)A$)
(declare-fun ltl$ (A_llist$)A_llist$)
(declare-fun lCons$ (A$ A_llist$ )A_llist$)
(declare-fun z$ ()A$ )
(declare-fun uu$ ()A_llist_bool_fun$ )
(declare-fun xs$ ()A_llist$ )
(declare-fun zs$ ()A_llist$ )
(declare-fun uua$ (A_llist$ )A_llist_bool_fun$ )
(declare-fun xs$a ()A_llist$ )
(declare-fun xsa$ ()A_llist$ )
(declare-fun zsa$ ()A_llist$ )
(declare-fun lSup$ (A_llist_set$ )A_llist$ )
(declare-fun lnull$ (A_llist$ )Bool )
(declare-fun member$ (A_llist$ A_llist_set$ )Bool )
(declare-fun collect$ (A_llist_bool_fun$ )A_llist_set$ )
(declare-fun fun_app$ (A_llist_bool_fun$ A_llist$ )Bool )
(declare-fun lfinite$ (A_llist$ )Bool )
(declare-fun lprefix$ (A_llist$ A_llist$ )Bool )
(assert (! (forall ((?v0 A_llist$ ))(! (= (fun_app$ uu$ ?v0 )(and (lprefix$ ?v0 xsa$ )(and (lprefix$ (lCons$ z$ zsa$ )?v0 )(lfinite$ ?v0 )))):pattern ((fun_app$ uu$ ?v0 )))):named a0 ))
(assert (! (forall ((?v0 A_llist$ )(?v1 A_llist$ ))(! (= (fun_app$ (uua$ ?v0 )?v1 )(and (lprefix$ ?v1 ?v0 )(and (lprefix$ zsa$ ?v1 )(lfinite$ ?v1 )))):pattern ((fun_app$ (uua$ ?v0 )?v1 )))):named a1 ))
(assert (! (not (= (lnull$ (lSup$ (collect$ uu$ )))(lnull$ xsa$ ))):named a2 ))
(assert (! (lfinite$ zsa$ ):named a3 ))
(assert (! (lfinite$ zs$ ):named a4 ))
(assert (! (lprefix$ zs$ xs$ ):named a5 ))
(assert (! (lprefix$ zsa$ xs$a ):named a6 ))
(assert (! (= xsa$ (lCons$ z$ xs$a )):named a7 ))
(assert (! (forall ((?v0 A_llist$ ))(=> (lprefix$ zsa$ ?v0 )(= (lSup$ (collect$ (uua$ ?v0 )))?v0 ))):named a8 ))
(assert (! (lprefix$ (lCons$ z$ zsa$ )xsa$ ):named a9 ))
(assert (! (forall ((?v0 A$ )(?v1 A_llist$ )(?v2 A$ )(?v3 A_llist$ ))(= (= (lCons$ ?v0 ?v1 )(lCons$ ?v2 ?v3 ))(and (= ?v0 ?v2 )(= ?v1 ?v3 )))):named a10 ))
(assert (! (forall ((?v0 A_llist$ ))(lprefix$ ?v0 ?v0 )):named a11 ))
(assert (! (forall ((?v0 A$ )(?v1 A_llist$ )(?v2 A$ )(?v3 A_llist$ ))(! (= (lprefix$ (lCons$ ?v0 ?v1 )(lCons$ ?v2 ?v3 ))(and (= ?v0 ?v2 )(lprefix$ ?v1 ?v3 ))):pattern ((lprefix$ (lCons$ ?v0 ?v1 )(lCons$ ?v2 ?v3 ))))):named a12 ))
(assert (! (forall ((?v0 A$ )(?v1 A_llist$ ))(! (= (lfinite$ (lCons$ ?v0 ?v1 ))(lfinite$ ?v1 )):pattern ((lCons$ ?v0 ?v1 )))):named a13 ))
(assert (! (forall ((?v0 A$ )(?v1 A_llist$ ))(! (= (lfinite$ (lCons$ ?v0 ?v1 ))(lfinite$ ?v1 )):pattern ((lCons$ ?v0 ?v1 )))):named a14 ))
(assert (! (forall ((?v0 A_llist_set$ ))(= (lnull$ (lSup$ ?v0 ))(forall ((?v1 A_llist$ ))(=> (member$ ?v1 ?v0 )(lnull$ ?v1 ))))):named a15 ))
(assert (! (=> (forall ((?v0 A_llist$ ))(=> (and (= xsa$ (lCons$ z$ ?v0 ))(lprefix$ zsa$ ?v0 ))false ))false ):named a16 ))
(assert (! (forall ((?v0 A$ )(?v1 A_llist$ )(?v2 A_llist$ ))(= (lprefix$ (lCons$ ?v0 ?v1 )?v2 )(exists ((?v3 A_llist$ ))(and (= ?v2 (lCons$ ?v0 ?v3 ))(lprefix$ ?v1 ?v3 ))))):named a17 ))
(assert (! (forall ((?v0 A_llist$ ))(= (not (lnull$ ?v0 ))(exists ((?v1 A$ )(?v2 A_llist$ ))(= ?v0 (lCons$ ?v1 ?v2 ))))):named a18 ))
(assert (! (forall ((?v0 A_llist_set$ ))(= (not (lnull$ (lSup$ ?v0 )))(not (forall ((?v1 A_llist$ ))(=> (member$ ?v1 ?v0 )(lnull$ ?v1 )))))):named a19 ))
(check-sat )
;(get-unsat-core )
