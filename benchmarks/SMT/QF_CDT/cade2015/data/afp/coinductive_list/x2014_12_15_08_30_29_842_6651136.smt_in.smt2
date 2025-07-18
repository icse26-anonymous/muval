;(set-option :produce-unsat-cores true )
(set-logic ALL_SUPPORTED )
(declare-sort A$ 0 )
(declare-sort Nat$ 0 )
(declare-sort A_a_fun$ 0 )
(declare-sort A_bool_fun$ 0 )
(declare-sort A_llist_enat_fun$ 0 )
(declare-datatypes ()((Nat_option$ (none$ )(some$ (the$ Nat$ )))(Enat$ (abs_enat$ (rep_enat$ Nat_option$ )))))
(declare-sort A_llist$ 0)
(declare-fun lNil$ ()A_llist$)
(declare-fun lhd$ (A_llist$)A$)
(declare-fun ltl$ (A_llist$)A_llist$)
(declare-fun lCons$ (A$ A_llist$ )A_llist$)
(declare-fun p$ ()A_bool_fun$ )
(declare-fun xs$ ()A_llist$ )
(declare-fun llcp$ (A_llist$ )A_llist_enat_fun$ )
(declare-fun lmap$ (A_a_fun$ A_llist$ )A_llist$ )
(declare-fun ldrop$ (Enat$ A_llist$ )A_llist$ )
(declare-fun fun_app$ (A_llist_enat_fun$ A_llist$ )Enat$ )
(declare-fun lfilter$ (A_bool_fun$ A_llist$ )A_llist$ )
(declare-fun lfinite$ (A_llist$ )Bool )
(declare-fun llength$ (A_llist$ )Enat$ )
(declare-fun lprefix$ (A_llist$ A_llist$ )Bool )
(declare-fun infinity$ ()Enat$ )
(declare-fun iterates$ (A_a_fun$ A$ )A_llist$ )
(declare-fun ltakeWhile$ (A_bool_fun$ A_llist$ )A_llist$ )
(assert (! (not (= (llength$ xs$ )infinity$ )):named a0 ))
(assert (! (not (lfinite$ xs$ )):named a1 ))
(assert (! (forall ((?v0 A_llist$ ))(= (= (llength$ ?v0 )infinity$ )(not (lfinite$ ?v0 )))):named a2 ))
(assert (! (forall ((?v0 A_llist$ ))(! (=> (not (lfinite$ ?v0 ))(= (llength$ ?v0 )infinity$ )):pattern ((llength$ ?v0 )))):named a3 ))
(assert (! (forall ((?v0 A_a_fun$ )(?v1 A$ ))(= (llength$ (iterates$ ?v0 ?v1 ))infinity$ )):named a4 ))
(assert (! (=> (lfinite$ xs$ )(lfinite$ (lfilter$ p$ xs$ ))):named a5 ))
(assert (! (forall ((?v0 A_llist$ ))(! (= (fun_app$ (llcp$ ?v0 )?v0 )(llength$ ?v0 )):pattern ((llcp$ ?v0 )))):named a6 ))
(assert (! (forall ((?v0 A_bool_fun$ )(?v1 A_llist$ ))(= (= (llength$ (ltakeWhile$ ?v0 ?v1 ))infinity$ )(and (not (lfinite$ ?v1 ))(= (ltakeWhile$ ?v0 ?v1 )?v1 )))):named a7 ))
(assert (! (forall ((?v0 A_a_fun$ )(?v1 A_llist$ ))(= (llength$ (lmap$ ?v0 ?v1 ))(llength$ ?v1 ))):named a8 ))
(assert (! (forall ((?v0 A_llist$ )(?v1 A_llist$ ))(=> (and (lprefix$ ?v0 ?v1 )(= (llength$ ?v0 )(llength$ ?v1 )))(= ?v0 ?v1 ))):named a9 ))
(assert (! (forall ((?v0 A_bool_fun$ )(?v1 A_llist$ ))(= (= (llength$ (ltakeWhile$ ?v0 ?v1 ))(llength$ ?v1 ))(= (ltakeWhile$ ?v0 ?v1 )?v1 ))):named a10 ))
(assert (! (forall ((?v0 Enat$ )(?v1 A_llist$ ))(= (lfinite$ (ldrop$ ?v0 ?v1 ))(or (lfinite$ ?v1 )(= ?v0 infinity$ )))):named a11 ))
(assert (! (forall ((?v0 A_llist$ ))(lprefix$ ?v0 ?v0 )):named a12 ))
(assert (! (forall ((?v0 A_llist$ ))(lprefix$ ?v0 ?v0 )):named a13 ))
(assert (! (forall ((?v0 A_bool_fun$ )(?v1 A_llist$ ))(= (lfilter$ ?v0 (lfilter$ ?v0 ?v1 ))(lfilter$ ?v0 ?v1 ))):named a14 ))
(assert (! (forall ((?v0 A_a_fun$ )(?v1 A_llist$ ))(= (lfinite$ (lmap$ ?v0 ?v1 ))(lfinite$ ?v1 ))):named a15 ))
(check-sat )
;(get-unsat-core )
