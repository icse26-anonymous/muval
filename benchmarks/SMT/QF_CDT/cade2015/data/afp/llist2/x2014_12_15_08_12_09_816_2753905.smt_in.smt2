;(set-option :produce-unsat-cores true )
(set-logic ALL_SUPPORTED )
(declare-sort A$ 0 )
(declare-sort A_llist_a_llist_fun$ 0 )
(declare-sort A_llist$ 0)
(declare-fun lNil$ ()A_llist$)
(declare-fun lhd$ (A_llist$)A$)
(declare-fun ltl$ (A_llist$)A_llist$)
(declare-fun lCons$ (A$ A_llist$ )A_llist$)
(declare-fun s$ ()A_llist$ )
(declare-fun less$ (A_llist$ A_llist$ )Bool )
(declare-fun fun_app$ (A_llist_a_llist_fun$ A_llist$ )A_llist$ )
(declare-fun lappend$ (A_llist$ )A_llist_a_llist_fun$ )
(declare-fun less_eq$ (A_llist$ A_llist$ )Bool )
(declare-fun lbutlast$ (A_llist$ )A_llist$ )
(assert (! (not (less_eq$ lNil$ s$ )):named a0 ))
(assert (! (forall ((?v0 A$ )(?v1 A_llist$ ))(not (less_eq$ (lCons$ ?v0 ?v1 )lNil$ ))):named a1 ))
(assert (! (forall ((?v0 A_llist$ )(?v1 A_llist$ ))(! (= (less$ ?v0 ?v1 )(and (less_eq$ ?v0 ?v1 )(not (= ?v0 ?v1 )))):pattern ((less$ ?v0 ?v1 )))):named a2 ))
(assert (! (forall ((?v0 A_llist$ )(?v1 A_llist$ ))(= (less_eq$ ?v0 ?v1 )(exists ((?v2 A_llist$ ))(= ?v1 (fun_app$ (lappend$ ?v0 )?v2 ))))):named a3 ))
(assert (! (= (lbutlast$ lNil$ )lNil$ ):named a4 ))
(assert (! (forall ((?v0 A$ )(?v1 A_llist$ )(?v2 A$ )(?v3 A_llist$ ))(= (= (lCons$ ?v0 ?v1 )(lCons$ ?v2 ?v3 ))(and (= ?v0 ?v2 )(= ?v1 ?v3 )))):named a5 ))
(assert (! (forall ((?v0 A$ )(?v1 A_llist$ )(?v2 A_llist$ ))(! (= (fun_app$ (lappend$ (lCons$ ?v0 ?v1 ))?v2 )(lCons$ ?v0 (fun_app$ (lappend$ ?v1 )?v2 ))):pattern ((fun_app$ (lappend$ (lCons$ ?v0 ?v1 ))?v2 )))):named a6 ))
(assert (! (forall ((?v0 A_llist$ ))(! (= (fun_app$ (lappend$ lNil$ )?v0 )?v0 ):pattern ((fun_app$ (lappend$ lNil$ )?v0 )))):named a7 ))
(assert (! (forall ((?v0 A_llist$ ))(! (= (fun_app$ (lappend$ ?v0 )lNil$ )?v0 ):pattern ((lappend$ ?v0 )))):named a8 ))
(assert (! (forall ((?v0 A_llist$ )(?v1 A_llist$ ))(= (= (fun_app$ (lappend$ ?v0 )?v1 )lNil$ )(and (= ?v0 lNil$ )(= ?v1 lNil$ )))):named a9 ))
(check-sat )
;(get-unsat-core )
