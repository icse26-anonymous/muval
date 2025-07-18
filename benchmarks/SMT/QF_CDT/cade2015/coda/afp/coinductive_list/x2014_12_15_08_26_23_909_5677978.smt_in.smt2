;(set-option :produce-unsat-cores true )
(set-logic ALL_SUPPORTED )
(declare-sort A$ 0 )
(declare-sort A_set$ 0 )
(declare-sort A_llist_bool_fun$ 0 )
(declare-sort A_llist_a_llist_fun$ 0 )
(declare-codatatypes ()((A_llist$ (lNil$ )(lCons$ (lhd$ A$ )(ltl$ A_llist$ )))))
(declare-sort A_list$ 0)
(declare-fun nil$ ()A_list$)
(declare-fun hd$ (A_list$)A$)
(declare-fun tl$ (A_list$)A_list$)
(declare-fun cons$ (A$ A_list$ )A_list$)
(declare-fun xs$ ()A_llist$ )
(declare-fun ys$ ()A_llist$ )
(declare-fun lset$ (A_llist$ )A_set$ )
(declare-fun member$ (A$ A_set$ )Bool )
(declare-fun fun_app$ (A_llist_a_llist_fun$ A_llist$ )A_llist$ )
(declare-fun lappend$ (A_llist$ )A_llist_a_llist_fun$ )
(declare-fun distinct$ (A_list$ )Bool )
(declare-fun fun_app$a (A_llist_bool_fun$ A_llist$ )Bool )
(declare-fun llist_of$ (A_list$ )A_llist$ )
(declare-fun ldistinct$ (A_llist$ )Bool )
(declare-fun lstrict_prefix$ (A_llist$ )A_llist_bool_fun$ )
(assert (! (not (ldistinct$ xs$ )):named a0 ))
(assert (! (ldistinct$ (fun_app$ (lappend$ xs$ )ys$ )):named a1 ))
(assert (! (= (ldistinct$ lNil$ )true ):named a2 ))
(assert (! (ldistinct$ lNil$ ):named a3 ))
(assert (! (forall ((?v0 A_llist$ ))(=> (ldistinct$ ?v0 )(ldistinct$ (ltl$ ?v0 )))):named a4 ))
(assert (! (forall ((?v0 A_llist$ )(?v1 A_llist$ )(?v2 A_llist$ ))(= (fun_app$ (lappend$ (fun_app$ (lappend$ ?v0 )?v1 ))?v2 )(fun_app$ (lappend$ ?v0 )(fun_app$ (lappend$ ?v1 )?v2 )))):named a5 ))
(assert (! (forall ((?v0 A_list$ ))(= (ldistinct$ (llist_of$ ?v0 ))(distinct$ ?v0 ))):named a6 ))
(assert (! (forall ((?v0 A$ )(?v1 A_llist$ ))(! (= (ldistinct$ (lCons$ ?v0 ?v1 ))(and (not (member$ ?v0 (lset$ ?v1 )))(ldistinct$ ?v1 ))):pattern ((lCons$ ?v0 ?v1 )))):named a7 ))
(assert (! (forall ((?v0 A$ )(?v1 A_llist$ ))(=> (and (not (member$ ?v0 (lset$ ?v1 )))(ldistinct$ ?v1 ))(ldistinct$ (lCons$ ?v0 ?v1 )))):named a8 ))
(assert (! (forall ((?v0 A_llist_bool_fun$ )(?v1 A_llist$ ))(=> (forall ((?v2 A_llist$ ))(=> (forall ((?v3 A_llist$ ))(=> (fun_app$a (lstrict_prefix$ ?v3 )?v2 )(fun_app$a ?v0 ?v3 )))(fun_app$a ?v0 ?v2 )))(fun_app$a ?v0 ?v1 ))):named a9 ))
(assert (! (forall ((?v0 A$ )(?v1 A_llist$ )(?v2 A$ )(?v3 A_llist$ ))(= (= (lCons$ ?v0 ?v1 )(lCons$ ?v2 ?v3 ))(and (= ?v0 ?v2 )(= ?v1 ?v3 )))):named a10 ))
(assert (! (forall ((?v0 A_list$ )(?v1 A_list$ ))(= (= (llist_of$ ?v0 )(llist_of$ ?v1 ))(= ?v0 ?v1 ))):named a11 ))
(assert (! (forall ((?v0 A$ )(?v1 A_llist$ )(?v2 A_llist$ ))(! (= (fun_app$ (lappend$ (lCons$ ?v0 ?v1 ))?v2 )(lCons$ ?v0 (fun_app$ (lappend$ ?v1 )?v2 ))):pattern ((fun_app$ (lappend$ (lCons$ ?v0 ?v1 ))?v2 )))):named a12 ))
(assert (! (forall ((?v0 A_llist$ ))(! (= (fun_app$ (lappend$ ?v0 )lNil$ )?v0 ):pattern ((lappend$ ?v0 )))):named a13 ))
(assert (! (forall ((?v0 A_llist$ ))(! (= (fun_app$ (lappend$ lNil$ )?v0 )?v0 ):pattern ((fun_app$ (lappend$ lNil$ )?v0 )))):named a14 ))
(assert (! (forall ((?v0 A$ )(?v1 A_llist$ )(?v2 A$ )(?v3 A_llist$ ))(! (= (fun_app$a (lstrict_prefix$ (lCons$ ?v0 ?v1 ))(lCons$ ?v2 ?v3 ))(and (= ?v0 ?v2 )(fun_app$a (lstrict_prefix$ ?v1 )?v3 ))):pattern ((fun_app$a (lstrict_prefix$ (lCons$ ?v0 ?v1 ))(lCons$ ?v2 ?v3 ))))):named a15 ))
(assert (! (= (fun_app$a (lstrict_prefix$ lNil$ )lNil$ )false ):named a16 ))
(assert (! (forall ((?v0 A$ )(?v1 A_llist$ ))(! (= (fun_app$a (lstrict_prefix$ lNil$ )(lCons$ ?v0 ?v1 ))true ):pattern ((lCons$ ?v0 ?v1 )))):named a17 ))
(check-sat )
;(get-unsat-core )
