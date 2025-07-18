;(set-option :produce-unsat-cores true )
(set-logic ALL_SUPPORTED )
(declare-sort A$ 0 )
(declare-sort A_set$ 0 )
(declare-sort A_llist_set$ 0 )
(declare-codatatypes ()((A_llist$ (lNil$ )(lCons$ (lhd$ A$ )(ltl$ A_llist$ )))))
(declare-fun xs$ ()A_llist$ )
(declare-fun ys$ ()A_llist$ )
(declare-fun top$ ()A_set$ )
(declare-fun lrev$ (A_llist$ )A_llist$ )
(declare-fun member$ (A_llist$ A_llist_set$ )Bool )
(declare-fun finlsts$ (A_set$ )A_llist_set$ )
(declare-fun lappend$ (A_llist$ A_llist$ )A_llist$ )
(assert (! (not (= (= (lrev$ xs$ )(lrev$ ys$ ))(= xs$ ys$ ))):named a0 ))
(assert (! (member$ xs$ (finlsts$ top$ )):named a1 ))
(assert (! (member$ ys$ (finlsts$ top$ )):named a2 ))
(assert (! (= (lrev$ lNil$ )lNil$ ):named a3 ))
(assert (! (forall ((?v0 A_llist$ )(?v1 A_set$ ))(=> (member$ ?v0 (finlsts$ ?v1 ))(member$ (lrev$ ?v0 )(finlsts$ ?v1 )))):named a4 ))
(assert (! (forall ((?v0 A_llist$ ))(=> (member$ ?v0 (finlsts$ top$ ))(= (lrev$ (lrev$ ?v0 ))?v0 ))):named a5 ))
(assert (! (forall ((?v0 A_llist$ ))(=> (member$ ?v0 (finlsts$ top$ ))(= (= (lrev$ ?v0 )lNil$ )(= ?v0 lNil$ )))):named a6 ))
(assert (! (forall ((?v0 A_llist$ ))(=> (member$ ?v0 (finlsts$ top$ ))(= (= lNil$ (lrev$ ?v0 ))(= ?v0 lNil$ )))):named a7 ))
(assert (! (forall ((?v0 A_llist$ )(?v1 A_llist$ ))(=> (and (member$ ?v0 (finlsts$ top$ ))(member$ ?v1 (finlsts$ top$ )))(= (lrev$ (lappend$ ?v0 ?v1 ))(lappend$ (lrev$ ?v1 )(lrev$ ?v0 ))))):named a8 ))
(assert (! (forall ((?v0 A_llist$ )(?v1 A_llist$ ))(= (= lNil$ (lappend$ ?v0 ?v1 ))(and (= ?v0 lNil$ )(= ?v1 lNil$ )))):named a9 ))
(assert (! (forall ((?v0 A_llist$ )(?v1 A_llist$ ))(= (= (lappend$ ?v0 ?v1 )lNil$ )(and (= ?v0 lNil$ )(= ?v1 lNil$ )))):named a10 ))
(assert (! (forall ((?v0 A_llist$ )(?v1 A_llist$ )(?v2 A_set$ ))(= (member$ (lappend$ ?v0 ?v1 )(finlsts$ ?v2 ))(and (member$ ?v0 (finlsts$ ?v2 ))(member$ ?v1 (finlsts$ ?v2 ))))):named a11 ))
(assert (! (forall ((?v0 A_llist$ )(?v1 A_set$ )(?v2 A_llist$ )(?v3 A_llist$ ))(=> (member$ ?v0 (finlsts$ ?v1 ))(= (= (lappend$ ?v0 ?v2 )(lappend$ ?v0 ?v3 ))(= ?v2 ?v3 )))):named a12 ))
(assert (! (forall ((?v0 A_llist$ )(?v1 A_llist$ )(?v2 A_set$ ))(=> (member$ (lappend$ ?v0 ?v1 )(finlsts$ ?v2 ))(member$ ?v0 (finlsts$ ?v2 )))):named a13 ))
(assert (! (forall ((?v0 A_llist$ )(?v1 A_set$ )(?v2 A_llist$ ))(=> (and (member$ ?v0 (finlsts$ ?v1 ))(member$ ?v2 (finlsts$ ?v1 )))(member$ (lappend$ ?v0 ?v2 )(finlsts$ ?v1 )))):named a14 ))
(assert (! (forall ((?v0 A_llist$ )(?v1 A_set$ ))(=> (and (member$ ?v0 (finlsts$ ?v1 ))(not (member$ ?v0 (finlsts$ top$ ))))false )):named a15 ))
(assert (! (forall ((?v0 A_llist$ )(?v1 A_set$ ))(=> (member$ ?v0 (finlsts$ ?v1 ))(member$ ?v0 (finlsts$ top$ )))):named a16 ))
(assert (! (forall ((?v0 A_set$ ))(member$ lNil$ (finlsts$ ?v0 ))):named a17 ))
(check-sat )
;(get-unsat-core )
