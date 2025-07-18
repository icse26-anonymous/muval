;(set-option :produce-unsat-cores true )
(set-logic ALL_SUPPORTED )
(declare-sort A$ 0 )
(declare-sort A_llist_bool_fun$ 0 )
(declare-sort A_llist_a_llist_bool_fun_fun$ 0 )
(declare-codatatypes ()((A_llist$ (lNil$ )(lCons$ (lhd$ A$ )(ltl$ A_llist$ )))))
(declare-fun xs$ ()A_llist$ )
(declare-fun ys$ ()A_llist$ )
(declare-fun less$ (A_llist$ )A_llist_bool_fun$ )
(declare-fun fun_app$ (A_llist_bool_fun$ A_llist$ )Bool )
(declare-fun less_eq$ (A_llist$ )A_llist_bool_fun$ )
(declare-fun lprefix$ ()A_llist_a_llist_bool_fun_fun$ )
(declare-fun fun_app$a (A_llist_a_llist_bool_fun_fun$ A_llist$ )A_llist_bool_fun$ )
(declare-fun finite_lprefix$ ()A_llist_a_llist_bool_fun_fun$ )
(declare-fun lstrict_prefix$ (A_llist$ )A_llist_bool_fun$ )
(assert (! (not (fun_app$ (fun_app$a lprefix$ xs$ )xs$ )):named a0 ))
(assert (! (forall ((?v0 A_llist$ ))(fun_app$ (fun_app$a lprefix$ ?v0 )?v0 )):named a1 ))
(assert (! (forall ((?v0 A_llist$ ))(fun_app$ (fun_app$a lprefix$ ?v0 )?v0 )):named a2 ))
(assert (! (forall ((?v0 A_llist$ )(?v1 A_llist$ ))(! (= (fun_app$ (less_eq$ ?v0 )?v1 )(fun_app$ (fun_app$a lprefix$ ?v0 )?v1 )):pattern ((fun_app$ (less_eq$ ?v0 )?v1 )))):named a3 ))
(assert (! (forall ((?v0 A_llist$ )(?v1 A_llist$ ))(=> (and (fun_app$ (fun_app$a lprefix$ ?v0 )?v1 )(fun_app$ (fun_app$a lprefix$ ?v1 )?v0 ))(= ?v0 ?v1 ))):named a4 ))
(assert (! (forall ((?v0 A_llist$ )(?v1 A_llist$ ))(=> (and (fun_app$ (fun_app$a lprefix$ ?v0 )?v1 )(fun_app$ (fun_app$a lprefix$ ?v1 )?v0 ))(= ?v0 ?v1 ))):named a5 ))
(assert (! (forall ((?v0 A_llist$ )(?v1 A_llist$ )(?v2 A_llist$ ))(=> (and (fun_app$ (fun_app$a lprefix$ ?v0 )?v1 )(fun_app$ (fun_app$a lprefix$ ?v2 )?v1 ))(or (fun_app$ (fun_app$a lprefix$ ?v0 )?v2 )(fun_app$ (fun_app$a lprefix$ ?v2 )?v0 )))):named a6 ))
(assert (! (forall ((?v0 A_llist$ )(?v1 A_llist$ )(?v2 A_llist$ ))(=> (and (fun_app$ (fun_app$a lprefix$ ?v0 )?v1 )(fun_app$ (fun_app$a lprefix$ ?v1 )?v2 ))(fun_app$ (fun_app$a lprefix$ ?v0 )?v2 ))):named a7 ))
(assert (! (forall ((?v0 A_llist$ )(?v1 A_llist$ )(?v2 A_llist$ ))(=> (and (fun_app$ (fun_app$a lprefix$ ?v0 )?v1 )(fun_app$ (fun_app$a lprefix$ ?v1 )?v2 ))(fun_app$ (fun_app$a lprefix$ ?v0 )?v2 ))):named a8 ))
(assert (! (= (fun_app$ (less$ xs$ )ys$ )(and (fun_app$ (less_eq$ xs$ )ys$ )(not (fun_app$ (less_eq$ ys$ )xs$ )))):named a9 ))
(assert (! (forall ((?v0 A_llist$ )(?v1 A_llist$ ))(! (= (fun_app$ (less_eq$ ?v0 )?v1 )(fun_app$ (fun_app$a lprefix$ ?v0 )?v1 )):pattern ((fun_app$ (less_eq$ ?v0 )?v1 )))):named a10 ))
(assert (! (= finite_lprefix$ lprefix$ ):named a11 ))
(assert (! (forall ((?v0 A_llist$ )(?v1 A_llist$ ))(! (= (fun_app$ (lstrict_prefix$ ?v0 )?v1 )(and (fun_app$ (fun_app$a lprefix$ ?v0 )?v1 )(not (= ?v0 ?v1 )))):pattern ((fun_app$ (lstrict_prefix$ ?v0 )?v1 )))):named a12 ))
(assert (! (forall ((?v0 A_llist$ )(?v1 A_llist$ ))(! (= (fun_app$ (less$ ?v0 )?v1 )(fun_app$ (lstrict_prefix$ ?v0 )?v1 )):pattern ((fun_app$ (less$ ?v0 )?v1 )))):named a13 ))
(assert (! (forall ((?v0 A_llist$ )(?v1 A_llist$ ))(! (= (fun_app$ (less$ ?v0 )?v1 )(fun_app$ (lstrict_prefix$ ?v0 )?v1 )):pattern ((fun_app$ (less$ ?v0 )?v1 )))):named a14 ))
(assert (! (forall ((?v0 A_llist_bool_fun$ )(?v1 A_llist$ ))(=> (forall ((?v2 A_llist$ ))(=> (forall ((?v3 A_llist$ ))(=> (fun_app$ (lstrict_prefix$ ?v3 )?v2 )(fun_app$ ?v0 ?v3 )))(fun_app$ ?v0 ?v2 )))(fun_app$ ?v0 ?v1 ))):named a15 ))
(check-sat )
;(get-unsat-core )
