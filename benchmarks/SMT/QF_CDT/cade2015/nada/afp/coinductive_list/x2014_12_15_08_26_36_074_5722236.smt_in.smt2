;(set-option :produce-unsat-cores true )
(set-logic ALL_SUPPORTED )
(declare-sort A$ 0 )
(declare-sort Nat$ 0 )
(declare-sort A_set$ 0 )
(declare-sort A_llist$ 0)
(declare-fun lNil$ ()A_llist$)
(declare-fun lhd$ (A_llist$)A$)
(declare-fun ltl$ (A_llist$)A_llist$)
(declare-fun lCons$ (A$ A_llist$ )A_llist$)
(declare-sort Nat_option$ 0)
(declare-sort Enat$ 0)
(declare-sort A_list$ 0)
(declare-fun none$ ()Nat_option$)
(declare-fun the$ (Nat_option$)Nat$)
(declare-fun some$ (Nat$ )Nat_option$)
(declare-fun rep_enat$ (Enat$)Nat_option$)
(declare-fun abs_enat$ (Nat_option$ )Enat$)
(declare-fun nil$ ()A_list$)
(declare-fun hd$ (A_list$)A$)
(declare-fun tl$ (A_list$)A_list$)
(declare-fun cons$ (A$ A_list$ )A_list$)
(declare-fun xs$ ()A_llist$ )
(declare-fun enat$ (Nat$ )Enat$ )
(declare-fun less$ (Enat$ Enat$ )Bool )
(declare-fun lnth$ (A_llist$ Nat$ )A$ )
(declare-fun lset$ (A_llist$ )A_set$ )
(declare-fun ldrop$ (Enat$ A_llist$ )A_llist$ )
(declare-fun ltake$ (Enat$ A_llist$ )A_llist$ )
(declare-fun ldropn$ (Nat$ A_llist$ )A_llist$ )
(declare-fun member$ (A$ A_set$ )Bool )
(declare-fun llength$ (A_llist$ )Enat$ )
(declare-fun lprefix$ (A_llist$ A_llist$ )Bool )
(declare-fun distinct$ (A_list$ )Bool )
(declare-fun llist_of$ (A_list$ )A_llist$ )
(declare-fun ldistinct$ (A_llist$ )Bool )
(assert (! (not (ldistinct$ xs$ )):named a0 ))
(assert (! (forall ((?v0 Nat$ )(?v1 Nat$ ))(=> (and (less$ (enat$ ?v0 )(llength$ xs$ ))(and (less$ (enat$ ?v1 )(llength$ xs$ ))(not (= ?v0 ?v1 ))))(not (= (lnth$ xs$ ?v0 )(lnth$ xs$ ?v1 ))))):named a1 ))
(assert (! (= (ldistinct$ lNil$ )true ):named a2 ))
(assert (! (forall ((?v0 A_llist$ )(?v1 Nat$ ))(=> (ldistinct$ ?v0 )(ldistinct$ (ldropn$ ?v1 ?v0 )))):named a3 ))
(assert (! (forall ((?v0 A_llist$ )(?v1 Enat$ ))(=> (ldistinct$ ?v0 )(ldistinct$ (ldrop$ ?v1 ?v0 )))):named a4 ))
(assert (! (ldistinct$ lNil$ ):named a5 ))
(assert (! (forall ((?v0 A_llist$ )(?v1 A_llist$ ))(=> (and (ldistinct$ ?v0 )(lprefix$ ?v1 ?v0 ))(ldistinct$ ?v1 ))):named a6 ))
(assert (! (forall ((?v0 A_llist$ ))(=> (ldistinct$ ?v0 )(ldistinct$ (ltl$ ?v0 )))):named a7 ))
(assert (! (forall ((?v0 A_llist$ )(?v1 Enat$ ))(=> (ldistinct$ ?v0 )(ldistinct$ (ltake$ ?v1 ?v0 )))):named a8 ))
(assert (! (forall ((?v0 A_list$ ))(= (ldistinct$ (llist_of$ ?v0 ))(distinct$ ?v0 ))):named a9 ))
(assert (! (forall ((?v0 A$ )(?v1 A_llist$ ))(! (= (ldistinct$ (lCons$ ?v0 ?v1 ))(and (not (member$ ?v0 (lset$ ?v1 )))(ldistinct$ ?v1 ))):pattern ((lCons$ ?v0 ?v1 )))):named a10 ))
(assert (! (forall ((?v0 A$ )(?v1 A_llist$ ))(=> (and (not (member$ ?v0 (lset$ ?v1 )))(ldistinct$ ?v1 ))(ldistinct$ (lCons$ ?v0 ?v1 )))):named a11 ))
(assert (! (forall ((?v0 A_llist$ ))(lprefix$ ?v0 ?v0 )):named a12 ))
(assert (! (forall ((?v0 A_llist$ ))(lprefix$ ?v0 ?v0 )):named a13 ))
(assert (! (forall ((?v0 A$ )(?v1 A_llist$ )(?v2 A$ )(?v3 A_llist$ ))(= (= (lCons$ ?v0 ?v1 )(lCons$ ?v2 ?v3 ))(and (= ?v0 ?v2 )(= ?v1 ?v3 )))):named a14 ))
(assert (! (forall ((?v0 A_list$ )(?v1 A_list$ ))(= (= (llist_of$ ?v0 )(llist_of$ ?v1 ))(= ?v0 ?v1 ))):named a15 ))
(assert (! (forall ((?v0 A$ )(?v1 A_llist$ )(?v2 A$ )(?v3 A_llist$ ))(! (= (lprefix$ (lCons$ ?v0 ?v1 )(lCons$ ?v2 ?v3 ))(and (= ?v0 ?v2 )(lprefix$ ?v1 ?v3 ))):pattern ((lprefix$ (lCons$ ?v0 ?v1 )(lCons$ ?v2 ?v3 ))))):named a16 ))
(check-sat )
;(get-unsat-core )
