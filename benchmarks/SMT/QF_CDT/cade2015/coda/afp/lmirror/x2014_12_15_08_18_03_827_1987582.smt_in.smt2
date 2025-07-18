;(set-option :produce-unsat-cores true )
(set-logic ALL_SUPPORTED )
(declare-sort A$ 0 )
(declare-sort A_set$ 0 )
(declare-sort A_bool_fun$ 0 )
(declare-sort A_llist_a_llist_fun$ 0 )
(declare-codatatypes ()((A_llist$ (lNil$ )(lCons$ (lhd$ A$ )(ltl$ A_llist$ )))))
(declare-fun xs$ ()A_llist$ )
(declare-fun acc$ ()A_llist$ )
(declare-fun lset$ (A_llist$ )A_set$ )
(declare-fun lnull$ (A_llist$ )Bool )
(declare-fun member$ (A$ A_set$ )Bool )
(declare-fun fun_app$ (A_llist_a_llist_fun$ A_llist$ )A_llist$ )
(declare-fun lappend$ (A_llist$ A_llist$ )A_llist$ )
(declare-fun less_eq$ (A_set$ A_set$ )Bool )
(declare-fun lfinite$ (A_llist$ )Bool )
(declare-fun lmember$ (A$ A_llist$ )Bool )
(declare-fun fun_app$a (A_bool_fun$ A$ )Bool )
(declare-fun ltakeWhile$ (A_bool_fun$ A_llist$ )A_llist$ )
(declare-fun lmirror_aux$ (A_llist$ )A_llist_a_llist_fun$ )
(assert (! (not (= (lset$ (fun_app$ (lmirror_aux$ acc$ )xs$ ))(lset$ (lappend$ xs$ acc$ )))):named a0 ))
(assert (! (forall ((?v0 A_llist$ )(?v1 A_llist$ )(?v2 A_llist$ ))(= (fun_app$ (lmirror_aux$ (lappend$ ?v0 ?v1 ))?v2 )(lappend$ (fun_app$ (lmirror_aux$ ?v0 )?v2 )?v1 ))):named a1 ))
(assert (! (forall ((?v0 A_llist$ )(?v1 A_llist$ )(?v2 A_llist$ ))(= (lappend$ (lappend$ ?v0 ?v1 )?v2 )(lappend$ ?v0 (lappend$ ?v1 ?v2 )))):named a2 ))
(assert (! (forall ((?v0 A_llist$ ))(! (= (fun_app$ (lmirror_aux$ ?v0 )lNil$ )?v0 ):pattern ((lmirror_aux$ ?v0 )))):named a3 ))
(assert (! (forall ((?v0 A_llist$ )(?v1 A$ )(?v2 A_llist$ ))(! (= (fun_app$ (lmirror_aux$ ?v0 )(lCons$ ?v1 ?v2 ))(lCons$ ?v1 (fun_app$ (lmirror_aux$ (lCons$ ?v1 ?v0 ))?v2 ))):pattern ((fun_app$ (lmirror_aux$ ?v0 )(lCons$ ?v1 ?v2 ))))):named a4 ))
(assert (! (forall ((?v0 A_llist$ )(?v1 A_llist$ ))(= (not (lnull$ (fun_app$ (lmirror_aux$ ?v0 )?v1 )))(or (not (lnull$ ?v1 ))(not (lnull$ ?v0 ))))):named a5 ))
(assert (! (forall ((?v0 A_llist$ )(?v1 A_llist$ ))(= (lnull$ (fun_app$ (lmirror_aux$ ?v0 )?v1 ))(and (lnull$ ?v1 )(lnull$ ?v0 )))):named a6 ))
(assert (! (forall ((?v0 A_llist$ )(?v1 A_llist$ ))(= (lfinite$ (fun_app$ (lmirror_aux$ ?v0 )?v1 ))(and (lfinite$ ?v1 )(lfinite$ ?v0 )))):named a7 ))
(assert (! (forall ((?v0 A_llist$ )(?v1 A_llist$ ))(less_eq$ (lset$ ?v0 )(lset$ (lappend$ ?v0 ?v1 )))):named a8 ))
(assert (! (forall ((?v0 A$ )(?v1 A_llist$ ))(= (member$ ?v0 (lset$ ?v1 ))(lmember$ ?v0 ?v1 ))):named a9 ))
(assert (! (forall ((?v0 A$ )(?v1 A_llist$ )(?v2 A_bool_fun$ )(?v3 A_llist$ ))(=> (and (member$ ?v0 (lset$ ?v1 ))(not (fun_app$a ?v2 ?v0 )))(= (ltakeWhile$ ?v2 (lappend$ ?v1 ?v3 ))(ltakeWhile$ ?v2 ?v1 )))):named a10 ))
(assert (! (forall ((?v0 A$ )(?v1 A_llist$ )(?v2 A_llist$ ))(= (member$ ?v0 (lset$ (lappend$ ?v1 ?v2 )))(or (member$ ?v0 (lset$ ?v1 ))(and (lfinite$ ?v1 )(member$ ?v0 (lset$ ?v2 )))))):named a11 ))
(assert (! (forall ((?v0 A_llist$ )(?v1 A_llist$ ))(=> (or (not (lnull$ ?v0 ))(not (lnull$ ?v1 )))(not (lnull$ (fun_app$ (lmirror_aux$ ?v1 )?v0 ))))):named a12 ))
(assert (! (forall ((?v0 A_llist$ )(?v1 A_llist$ ))(=> (and (lnull$ ?v0 )(lnull$ ?v1 ))(lnull$ (fun_app$ (lmirror_aux$ ?v1 )?v0 )))):named a13 ))
(assert (! (forall ((?v0 A$ )(?v1 A_llist$ )(?v2 A$ )(?v3 A_llist$ ))(= (= (lCons$ ?v0 ?v1 )(lCons$ ?v2 ?v3 ))(and (= ?v0 ?v2 )(= ?v1 ?v3 )))):named a14 ))
(assert (! (forall ((?v0 A$ )(?v1 A_llist$ )(?v2 A_llist$ ))(! (= (lappend$ (lCons$ ?v0 ?v1 )?v2 )(lCons$ ?v0 (lappend$ ?v1 ?v2 ))):pattern ((lappend$ (lCons$ ?v0 ?v1 )?v2 )))):named a15 ))
(assert (! (forall ((?v0 A$ )(?v1 A_llist$ ))(! (= (lfinite$ (lCons$ ?v0 ?v1 ))(lfinite$ ?v1 )):pattern ((lCons$ ?v0 ?v1 )))):named a16 ))
(assert (! (forall ((?v0 A$ )(?v1 A_llist$ ))(! (= (lfinite$ (lCons$ ?v0 ?v1 ))(lfinite$ ?v1 )):pattern ((lCons$ ?v0 ?v1 )))):named a17 ))
(check-sat )
;(get-unsat-core )
