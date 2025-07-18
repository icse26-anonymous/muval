;(set-option :produce-unsat-cores true )
(set-logic ALL_SUPPORTED )
(declare-sort A$ 0 )
(declare-sort A_llist_bool_fun$ 0 )
(declare-sort A_llist_a_llist_bool_fun_fun$ 0 )
(declare-codatatypes ()((A_llist$ (lNil$ )(lCons$ (lhd$ A$ )(ltl$ A_llist$ )))))
(declare-fun xs$ ()A_llist$ )
(declare-fun ys$ ()A_llist$ )
(declare-fun zs$ ()A_llist$ )
(declare-fun less$ (A_llist$ A_llist$ )Bool )
(declare-fun fun_app$ (A_llist_bool_fun$ A_llist$ )Bool )
(declare-fun less_eq$ (A_llist$ A_llist$ )Bool )
(declare-fun lprefix$ ()A_llist_a_llist_bool_fun_fun$ )
(declare-fun fun_app$a (A_llist_a_llist_bool_fun_fun$ A_llist$ )A_llist_bool_fun$ )
(declare-fun finite_lprefix$ ()A_llist_a_llist_bool_fun_fun$ )
(declare-fun lstrict_prefix$ (A_llist$ A_llist$ )Bool )
(assert (! (not (fun_app$ (fun_app$a lprefix$ xs$ )zs$ )):named a0 ))
(assert (! (fun_app$ (fun_app$a lprefix$ xs$ )ys$ ):named a1 ))
(assert (! (fun_app$ (fun_app$a lprefix$ ys$ )zs$ ):named a2 ))
(assert (! (forall ((?v0 A_llist$ ))(fun_app$ (fun_app$a lprefix$ ?v0 )?v0 )):named a3 ))
(assert (! (forall ((?v0 A_llist$ ))(fun_app$ (fun_app$a lprefix$ ?v0 )?v0 )):named a4 ))
(assert (! (forall ((?v0 A_llist$ )(?v1 A_llist$ ))(! (= (less_eq$ ?v0 ?v1 )(fun_app$ (fun_app$a lprefix$ ?v0 )?v1 )):pattern ((less_eq$ ?v0 ?v1 )))):named a5 ))
(assert (! (less_eq$ xs$ xs$ ):named a6 ))
(assert (! (= (less$ xs$ ys$ )(and (less_eq$ xs$ ys$ )(not (less_eq$ ys$ xs$ )))):named a7 ))
(assert (! (forall ((?v0 A_llist$ )(?v1 A_llist$ ))(=> (and (fun_app$ (fun_app$a lprefix$ ?v0 )?v1 )(fun_app$ (fun_app$a lprefix$ ?v1 )?v0 ))(= ?v0 ?v1 ))):named a8 ))
(assert (! (forall ((?v0 A_llist$ )(?v1 A_llist$ ))(=> (and (fun_app$ (fun_app$a lprefix$ ?v0 )?v1 )(fun_app$ (fun_app$a lprefix$ ?v1 )?v0 ))(= ?v0 ?v1 ))):named a9 ))
(assert (! (forall ((?v0 A_llist$ )(?v1 A_llist$ )(?v2 A_llist$ ))(=> (and (fun_app$ (fun_app$a lprefix$ ?v0 )?v1 )(fun_app$ (fun_app$a lprefix$ ?v2 )?v1 ))(or (fun_app$ (fun_app$a lprefix$ ?v0 )?v2 )(fun_app$ (fun_app$a lprefix$ ?v2 )?v0 )))):named a10 ))
(assert (! (forall ((?v0 A_llist$ )(?v1 A_llist$ )(?v2 A_llist$ ))(=> (and (fun_app$ (fun_app$a lprefix$ ?v0 )?v1 )(fun_app$ (fun_app$a lprefix$ ?v1 )?v2 ))(fun_app$ (fun_app$a lprefix$ ?v0 )?v2 ))):named a11 ))
(assert (! (forall ((?v0 A_llist$ )(?v1 A_llist$ )(?v2 A_llist$ ))(=> (and (fun_app$ (fun_app$a lprefix$ ?v0 )?v1 )(fun_app$ (fun_app$a lprefix$ ?v1 )?v2 ))(fun_app$ (fun_app$a lprefix$ ?v0 )?v2 ))):named a12 ))
(assert (! (forall ((?v0 A_llist$ )(?v1 A_llist$ ))(! (= (less_eq$ ?v0 ?v1 )(fun_app$ (fun_app$a lprefix$ ?v0 )?v1 )):pattern ((less_eq$ ?v0 ?v1 )))):named a13 ))
(assert (! (= finite_lprefix$ lprefix$ ):named a14 ))
(assert (! (forall ((?v0 A_llist$ )(?v1 A_llist$ ))(! (= (less$ ?v0 ?v1 )(lstrict_prefix$ ?v0 ?v1 )):pattern ((less$ ?v0 ?v1 )))):named a15 ))
(check-sat )
;(get-unsat-core )
