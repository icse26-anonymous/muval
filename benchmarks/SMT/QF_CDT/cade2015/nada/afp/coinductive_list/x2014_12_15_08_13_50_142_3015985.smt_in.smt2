;(set-option :produce-unsat-cores true )
(set-logic ALL_SUPPORTED )
(declare-sort A$ 0 )
(declare-sort A_a_fun$ 0 )
(declare-sort A_llist_a_llist_fun$ 0 )
(declare-sort A_list$ 0)
(declare-fun nil$ ()A_list$)
(declare-fun hd$ (A_list$)A$)
(declare-fun tl$ (A_list$)A_list$)
(declare-fun cons$ (A$ A_list$ )A_list$)
(declare-sort A_llist$ 0)
(declare-fun lNil$ ()A_llist$)
(declare-fun lhd$ (A_llist$)A$)
(declare-fun ltl$ (A_llist$)A_llist$)
(declare-fun lCons$ (A$ A_llist$ )A_llist$)
(declare-fun xs$ ()A_llist$ )
(declare-fun lmap$ (A_a_fun$ A_llist$ )A_llist$ )
(declare-fun fun_app$ (A_llist_a_llist_fun$ A_llist$ )A_llist$ )
(declare-fun lappend$ (A_llist$ )A_llist_a_llist_fun$ )
(declare-fun lfinite$ (A_llist$ )Bool )
(declare-fun list_of$ (A_llist$ )A_list$ )
(declare-fun iterates$ (A_a_fun$ A$ )A_llist$ )
(declare-fun llist_of$ (A_list$ )A_llist$ )
(assert (! (not (= (hd$ (list_of$ xs$ ))(lhd$ xs$ ))):named a0 ))
(assert (! (lfinite$ xs$ ):named a1 ))
(assert (! (forall ((?v0 A_llist$ ))(=> (lfinite$ ?v0 )(= (llist_of$ (list_of$ ?v0 ))?v0 ))):named a2 ))
(assert (! (forall ((?v0 A_list$ ))(= (lhd$ (llist_of$ ?v0 ))(hd$ ?v0 ))):named a3 ))
(assert (! (forall ((?v0 A_a_fun$ )(?v1 A$ ))(= (lhd$ (iterates$ ?v0 ?v1 ))?v1 )):named a4 ))
(assert (! (forall ((?v0 A_list$ ))(= (list_of$ (llist_of$ ?v0 ))?v0 )):named a5 ))
(assert (! (forall ((?v0 A_list$ ))(lfinite$ (llist_of$ ?v0 ))):named a6 ))
(assert (! (forall ((?v0 A_llist$ )(?v1 A_llist$ ))(= (lfinite$ (fun_app$ (lappend$ ?v0 )?v1 ))(and (lfinite$ ?v0 )(lfinite$ ?v1 )))):named a7 ))
(assert (! (forall ((?v0 A_a_fun$ )(?v1 A_llist$ ))(= (lfinite$ (lmap$ ?v0 ?v1 ))(lfinite$ ?v1 ))):named a8 ))
(assert (! (= (lfinite$ lNil$ )true ):named a9 ))
(assert (! (forall ((?v0 A_llist$ ))(= (lfinite$ (ltl$ ?v0 ))(lfinite$ ?v0 ))):named a10 ))
(assert (! (forall ((?v0 A$ )(?v1 A_llist$ ))(! (= (lfinite$ (lCons$ ?v0 ?v1 ))(lfinite$ ?v1 )):pattern ((lCons$ ?v0 ?v1 )))):named a11 ))
(assert (! (forall ((?v0 A$ )(?v1 A_llist$ )(?v2 A$ )(?v3 A_llist$ ))(= (= (lCons$ ?v0 ?v1 )(lCons$ ?v2 ?v3 ))(and (= ?v0 ?v2 )(= ?v1 ?v3 )))):named a12 ))
(assert (! (forall ((?v0 A_list$ )(?v1 A_list$ ))(= (= (llist_of$ ?v0 )(llist_of$ ?v1 ))(= ?v0 ?v1 ))):named a13 ))
(assert (! (forall ((?v0 A$ )(?v1 A_llist$ )(?v2 A_llist$ ))(! (= (fun_app$ (lappend$ (lCons$ ?v0 ?v1 ))?v2 )(lCons$ ?v0 (fun_app$ (lappend$ ?v1 )?v2 ))):pattern ((fun_app$ (lappend$ (lCons$ ?v0 ?v1 ))?v2 )))):named a14 ))
(assert (! (forall ((?v0 A$ )(?v1 A_llist$ ))(! (= (lfinite$ (lCons$ ?v0 ?v1 ))(lfinite$ ?v1 )):pattern ((lCons$ ?v0 ?v1 )))):named a15 ))
(assert (! (forall ((?v0 A_llist$ ))(! (= (fun_app$ (lappend$ ?v0 )lNil$ )?v0 ):pattern ((lappend$ ?v0 )))):named a16 ))
(check-sat )
;(get-unsat-core )
