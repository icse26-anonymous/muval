;(set-option :produce-unsat-cores true )
(set-logic ALL_SUPPORTED )
(declare-sort A$ 0 )
(declare-codatatypes ()((A_llist$ (lNil$ )(lCons$ (lhd$ A$ )(ltl$ A_llist$ )))))
(declare-fun s$ ()A_llist$ )
(declare-fun t$ ()A_llist$ )
(declare-fun less$ (A_llist$ A_llist$ )Bool )
(declare-fun less_eq$ (A_llist$ A_llist$ )Bool )
(assert (! (not (= (less$ s$ t$ )(and (less_eq$ s$ t$ )(not (less_eq$ t$ s$ ))))):named a0 ))
(assert (! (forall ((?v0 A_llist$ )(?v1 A_llist$ ))(=> (and (less_eq$ ?v0 ?v1 )(less_eq$ ?v1 ?v0 ))(= ?v0 ?v1 ))):named a1 ))
(assert (! (forall ((?v0 A_llist$ )(?v1 A_llist$ )(?v2 A_llist$ ))(=> (and (less_eq$ ?v0 ?v1 )(less_eq$ ?v1 ?v2 ))(less_eq$ ?v0 ?v2 ))):named a2 ))
(assert (! (forall ((?v0 A_llist$ )(?v1 A_llist$ ))(! (= (less$ ?v0 ?v1 )(and (less_eq$ ?v0 ?v1 )(not (= ?v0 ?v1 )))):pattern ((less$ ?v0 ?v1 )))):named a3 ))
(assert (! (forall ((?v0 A_llist$ ))(less_eq$ ?v0 ?v0 )):named a4 ))
(assert (! (forall ((?v0 A_llist$ )(?v1 A_llist$ ))(! (= (less$ ?v0 ?v1 )(and (less_eq$ ?v0 ?v1 )(not (= ?v0 ?v1 )))):pattern ((less$ ?v0 ?v1 )))):named a5 ))
(assert (! (forall ((?v0 A_llist$ )(?v1 A_llist$ ))(=> (and (less_eq$ ?v0 ?v1 )(less_eq$ ?v1 ?v0 ))(= ?v0 ?v1 ))):named a6 ))
(assert (! (forall ((?v0 A_llist$ )(?v1 A_llist$ )(?v2 A_llist$ ))(=> (and (less_eq$ ?v0 ?v1 )(less_eq$ ?v1 ?v2 ))(less_eq$ ?v0 ?v2 ))):named a7 ))
(assert (! (forall ((?v0 A_llist$ ))(less_eq$ ?v0 ?v0 )):named a8 ))
(check-sat )
;(get-unsat-core )
