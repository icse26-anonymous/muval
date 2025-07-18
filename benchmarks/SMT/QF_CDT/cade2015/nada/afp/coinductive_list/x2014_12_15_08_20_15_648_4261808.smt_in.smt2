;(set-option :produce-unsat-cores true )
(set-logic ALL_SUPPORTED )
(declare-sort A$ 0 )
(declare-sort Nat$ 0 )
(declare-sort A_a_fun$ 0 )
(declare-sort A_llist$ 0)
(declare-fun lNil$ ()A_llist$)
(declare-fun lhd$ (A_llist$)A$)
(declare-fun ltl$ (A_llist$)A_llist$)
(declare-fun lCons$ (A$ A_llist$ )A_llist$)
(declare-sort Nat_option$ 0)
(declare-sort Enat$ 0)
(declare-fun none$ ()Nat_option$)
(declare-fun the$ (Nat_option$)Nat$)
(declare-fun some$ (Nat$ )Nat_option$)
(declare-fun rep_enat$ (Enat$)Nat_option$)
(declare-fun abs_enat$ (Nat_option$ )Enat$)
(declare-fun xs$ ()A_llist$ )
(declare-fun ys$ ()A_llist$ )
(declare-fun less$ (Enat$ Enat$ )Bool )
(declare-fun plus$ (Enat$ Enat$ )Enat$ )
(declare-fun zero$ ()Enat$ )
(declare-fun ldrop$ (Enat$ A_llist$ )A_llist$ )
(declare-fun ltake$ (Enat$ A_llist$ )A_llist$ )
(declare-fun minus$ (Enat$ Enat$ )Enat$ )
(declare-fun lappend$ (A_llist$ A_llist$ )A_llist$ )
(declare-fun lfinite$ (A_llist$ )Bool )
(declare-fun llength$ (A_llist$ )Enat$ )
(declare-fun lprefix$ (A_llist$ A_llist$ )Bool )
(declare-fun iterates$ (A_a_fun$ A$ )A_llist$ )
(assert (! (not (= ys$ (lappend$ xs$ (ldrop$ (llength$ xs$ )ys$ )))):named a0 ))
(assert (! (lprefix$ xs$ ys$ ):named a1 ))
(assert (! (forall ((?v0 A_llist$ )(?v1 A_llist$ )(?v2 A_llist$ ))(= (lappend$ (lappend$ ?v0 ?v1 )?v2 )(lappend$ ?v0 (lappend$ ?v1 ?v2 )))):named a2 ))
(assert (! (forall ((?v0 A_llist$ )(?v1 A_llist$ ))(=> (and (lprefix$ ?v0 ?v1 )(= (llength$ ?v0 )(llength$ ?v1 )))(= ?v0 ?v1 ))):named a3 ))
(assert (! (forall ((?v0 A_llist$ )(?v1 A_llist$ )(?v2 A_llist$ ))(=> (lprefix$ ?v0 ?v1 )(lprefix$ (lappend$ ?v2 ?v0 )(lappend$ ?v2 ?v1 )))):named a4 ))
(assert (! (forall ((?v0 A_llist$ )(?v1 A_llist$ ))(lprefix$ ?v0 (lappend$ ?v0 ?v1 ))):named a5 ))
(assert (! (forall ((?v0 A_llist$ ))(lprefix$ ?v0 ?v0 )):named a6 ))
(assert (! (forall ((?v0 A_llist$ ))(lprefix$ ?v0 ?v0 )):named a7 ))
(assert (! (forall ((?v0 A_llist$ )(?v1 A_llist$ ))(= (llength$ (lappend$ ?v0 ?v1 ))(plus$ (llength$ ?v0 )(llength$ ?v1 )))):named a8 ))
(assert (! (forall ((?v0 Enat$ )(?v1 A_llist$ ))(= (lappend$ (ltake$ ?v0 ?v1 )(ldrop$ ?v0 ?v1 ))?v1 )):named a9 ))
(assert (! (forall ((?v0 A_llist$ )(?v1 A_llist$ )(?v2 A_llist$ )(?v3 A_llist$ ))(=> (= (llength$ ?v0 )(llength$ ?v1 ))(= (= (lappend$ ?v0 ?v2 )(lappend$ ?v1 ?v3 ))(and (= ?v0 ?v1 )(=> (lfinite$ ?v0 )(= ?v2 ?v3 )))))):named a10 ))
(assert (! (forall ((?v0 A_llist$ ))(= (ldrop$ zero$ ?v0 )?v0 )):named a11 ))
(assert (! (forall ((?v0 A_a_fun$ )(?v1 A$ )(?v2 A_llist$ ))(= (lappend$ (iterates$ ?v0 ?v1 )?v2 )(iterates$ ?v0 ?v1 ))):named a12 ))
(assert (! (forall ((?v0 Enat$ )(?v1 A_llist$ )(?v2 A_llist$ ))(= (ldrop$ ?v0 (lappend$ ?v1 ?v2 ))(ite (less$ ?v0 (llength$ ?v1 ))(lappend$ (ldrop$ ?v0 ?v1 )?v2 )(ldrop$ (minus$ ?v0 (llength$ ?v1 ))?v2 )))):named a13 ))
(assert (! (forall ((?v0 Enat$ )(?v1 Enat$ )(?v2 A_llist$ ))(= (ldrop$ ?v0 (ldrop$ ?v1 ?v2 ))(ldrop$ (plus$ ?v0 ?v1 )?v2 ))):named a14 ))
(assert (! (forall ((?v0 Enat$ )(?v1 A_llist$ ))(lprefix$ (ltake$ ?v0 ?v1 )?v1 )):named a15 ))
(assert (! (forall ((?v0 A_llist$ )(?v1 A_llist$ ))(= (lfinite$ (lappend$ ?v0 ?v1 ))(and (lfinite$ ?v0 )(lfinite$ ?v1 )))):named a16 ))
(assert (! (forall ((?v0 A_llist$ )(?v1 A_llist$ )(?v2 A_llist$ ))(= (lprefix$ (lappend$ ?v0 ?v1 )(lappend$ ?v0 ?v2 ))(=> (lfinite$ ?v0 )(lprefix$ ?v1 ?v2 )))):named a17 ))
(check-sat )
;(get-unsat-core )
