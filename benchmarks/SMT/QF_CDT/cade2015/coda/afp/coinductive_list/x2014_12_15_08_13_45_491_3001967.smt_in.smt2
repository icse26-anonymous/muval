;(set-option :produce-unsat-cores true )
(set-logic ALL_SUPPORTED )
(declare-sort A$ 0 )
(declare-sort A_llist_a_llist_fun$ 0 )
(declare-sort A_list$ 0)
(declare-fun nil$ ()A_list$)
(declare-fun hd$ (A_list$)A$)
(declare-fun tl$ (A_list$)A_list$)
(declare-fun cons$ (A$ A_list$ )A_list$)
(declare-codatatypes ()((A_llist$ (lNil$ )(lCons$ (lhd$ A$ )(ltl$ A_llist$ )))))
(declare-fun xs$ ()A_llist$ )
(declare-fun ys$ ()A_llist$ )
(declare-fun append$ (A_list$ A_list$ )A_list$ )
(declare-fun fun_app$ (A_llist_a_llist_fun$ A_llist$ )A_llist$ )
(declare-fun lappend$ (A_llist$ )A_llist_a_llist_fun$ )
(declare-fun lfinite$ (A_llist$ )Bool )
(declare-fun list_of$ (A_llist$ )A_list$ )
(declare-fun llist_of$ (A_list$ )A_llist$ )
(assert (! (not (= (list_of$ (fun_app$ (lappend$ xs$ )ys$ ))(append$ (list_of$ xs$ )(list_of$ ys$ )))):named a0 ))
(assert (! (lfinite$ xs$ ):named a1 ))
(assert (! (lfinite$ ys$ ):named a2 ))
(assert (! (forall ((?v0 A_llist$ )(?v1 A_llist$ )(?v2 A_llist$ ))(= (fun_app$ (lappend$ (fun_app$ (lappend$ ?v0 )?v1 ))?v2 )(fun_app$ (lappend$ ?v0 )(fun_app$ (lappend$ ?v1 )?v2 )))):named a3 ))
(assert (! (forall ((?v0 A_llist$ )(?v1 A_llist$ ))(= (lfinite$ (fun_app$ (lappend$ ?v0 )?v1 ))(and (lfinite$ ?v0 )(lfinite$ ?v1 )))):named a4 ))
(assert (! (forall ((?v0 A_list$ )(?v1 A_list$ )(?v2 A_list$ ))(= (= (append$ ?v0 ?v1 )(append$ ?v0 ?v2 ))(= ?v1 ?v2 ))):named a5 ))
(assert (! (forall ((?v0 A_list$ )(?v1 A_list$ )(?v2 A_list$ ))(= (= (append$ ?v0 ?v1 )(append$ ?v2 ?v1 ))(= ?v0 ?v2 ))):named a6 ))
(assert (! (forall ((?v0 A_list$ )(?v1 A_list$ )(?v2 A_list$ ))(= (append$ (append$ ?v0 ?v1 )?v2 )(append$ ?v0 (append$ ?v1 ?v2 )))):named a7 ))
(assert (! (forall ((?v0 A_llist$ )(?v1 A_llist$ ))(! (=> (not (lfinite$ ?v0 ))(= (fun_app$ (lappend$ ?v0 )?v1 )?v0 )):pattern ((fun_app$ (lappend$ ?v0 )?v1 )))):named a8 ))
(assert (! (forall ((?v0 A_list$ )(?v1 A_list$ )(?v2 A_list$ )(?v3 A_list$ ))(= (= (append$ ?v0 ?v1 )(append$ ?v2 ?v3 ))(exists ((?v4 A_list$ ))(or (and (= ?v0 (append$ ?v2 ?v4 ))(= (append$ ?v4 ?v1 )?v3 ))(and (= (append$ ?v0 ?v4 )?v2 )(= ?v1 (append$ ?v4 ?v3 ))))))):named a9 ))
(assert (! (forall ((?v0 A_list$ )(?v1 A_list$ )(?v2 A_list$ )(?v3 A_list$ )(?v4 A_list$ ))(=> (and (= (append$ ?v0 ?v1 )?v2 )(= ?v3 (append$ ?v1 ?v4 )))(= (append$ ?v0 ?v3 )(append$ ?v2 ?v4 )))):named a10 ))
(assert (! (forall ((?v0 A_list$ )(?v1 A_list$ ))(= (fun_app$ (lappend$ (llist_of$ ?v0 ))(llist_of$ ?v1 ))(llist_of$ (append$ ?v0 ?v1 )))):named a11 ))
(assert (! (forall ((?v0 A_list$ ))(= (list_of$ (llist_of$ ?v0 ))?v0 )):named a12 ))
(assert (! (forall ((?v0 A_llist$ ))(=> (lfinite$ ?v0 )(= (llist_of$ (list_of$ ?v0 ))?v0 ))):named a13 ))
(assert (! (forall ((?v0 A_llist$ ))(! (= (fun_app$ (lappend$ ?v0 )lNil$ )?v0 ):pattern ((lappend$ ?v0 )))):named a14 ))
(assert (! (forall ((?v0 A_llist$ ))(! (= (fun_app$ (lappend$ lNil$ )?v0 )?v0 ):pattern ((fun_app$ (lappend$ lNil$ )?v0 )))):named a15 ))
(assert (! (forall ((?v0 A_list$ )(?v1 A_list$ ))(= (= (llist_of$ ?v0 )(llist_of$ ?v1 ))(= ?v0 ?v1 ))):named a16 ))
(assert (! (= (lfinite$ lNil$ )true ):named a17 ))
(check-sat )
;(get-unsat-core )
