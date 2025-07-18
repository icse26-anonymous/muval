; --full-saturate-quant --inst-when=full-last-call --inst-no-entail --term-db-mode=relevant --random-seed=1 --lang=smt2 --tlimit 599
;(set-option :produce-unsat-cores true)
(set-logic ALL_SUPPORTED)
(declare-sort A$ 0)
(declare-sort A_bool_fun$ 0)
(declare-sort A_llist_set$ 0)
(declare-sort A_llist_bool_fun$ 0)
(declare-codatatypes () ((A_llist$ (lNil$) (lCons$ (lhd$ A$) (ltl$ A_llist$)))
  (A_llist_llist$ (lNil$a) (lCons$a (lhd$a A_llist$) (ltl$a A_llist_llist$)))
  (A_llist_llist_llist$ (lNil$b) (lCons$b (lhd$b A_llist_llist$) (ltl$b A_llist_llist_llist$)))))
(declare-fun xss$ () A_llist_llist$)
(declare-fun lset$ (A_llist_llist$) A_llist_set$)
(declare-fun xss$a () A_llist_llist$)
(declare-fun xssa$ () A_llist_llist$)
(declare-fun lnull$ (A_llist_llist$) Bool)
(declare-fun lnull$a (A_llist$) Bool)
(declare-fun member$ (A_llist$ A_llist_set$) Bool)
(declare-fun lappend$ (A_llist_llist$ A_llist_llist$) A_llist_llist$)
(declare-fun lconcat$ (A_llist_llist$) A_llist$)
(declare-fun lfilter$ (A_llist_bool_fun$ A_llist_llist$) A_llist_llist$)
(declare-fun lfinite$ (A_llist$) Bool)
(declare-fun lappend$a (A_llist$ A_llist$) A_llist$)
(declare-fun lconcat$a (A_llist_llist_llist$) A_llist_llist$)
(declare-fun lfilter$a (A_bool_fun$ A_llist$) A_llist$)
(declare-fun lfinite$a (A_llist_llist$) Bool)
(assert (! (not (lfinite$ (lconcat$ xssa$))) :named a0))
(assert (! (lfinite$ (lconcat$ xss$)) :named a1))
(assert (! (forall ((?v0 A_llist$)) (=> (member$ ?v0 (lset$ xssa$)) (lfinite$ ?v0))) :named a2))
(assert (! (forall ((?v0 A_llist$)) (=> (member$ ?v0 (lset$ xss$a)) (lfinite$ ?v0))) :named a3))
(assert (! (forall ((?v0 A_llist$)) (=> (member$ ?v0 (lset$ xss$)) (lfinite$ ?v0))) :named a4))
(assert (! (forall ((?v0 A_llist$)) (=> (member$ ?v0 (lset$ xssa$)) (lfinite$ ?v0))) :named a5))
(assert (! (forall ((?v0 A_llist$) (?v1 A_llist_llist$)) (! (= (lfinite$a (lCons$a ?v0 ?v1)) (lfinite$a ?v1)) :pattern ((lCons$a ?v0 ?v1)))) :named a6))
(assert (! (forall ((?v0 A$) (?v1 A_llist$)) (! (= (lfinite$ (lCons$ ?v0 ?v1)) (lfinite$ ?v1)) :pattern ((lCons$ ?v0 ?v1)))) :named a7))
(assert (! (forall ((?v0 A_llist$) (?v1 A_llist_llist$)) (! (= (lfinite$a (lCons$a ?v0 ?v1)) (lfinite$a ?v1)) :pattern ((lCons$a ?v0 ?v1)))) :named a8))
(assert (! (forall ((?v0 A$) (?v1 A_llist$)) (! (= (lfinite$ (lCons$ ?v0 ?v1)) (lfinite$ ?v1)) :pattern ((lCons$ ?v0 ?v1)))) :named a9))
(assert (! (forall ((?v0 A_llist_llist$) (?v1 A_llist_llist$)) (= (lfinite$a (lappend$ ?v0 ?v1)) (and (lfinite$a ?v0) (lfinite$a ?v1)))) :named a10))
(assert (! (forall ((?v0 A_llist$) (?v1 A_llist$)) (= (lfinite$ (lappend$a ?v0 ?v1)) (and (lfinite$ ?v0) (lfinite$ ?v1)))) :named a11))
(assert (! (forall ((?v0 A_llist_llist$) (?v1 A_llist$)) (=> (lfinite$a ?v0) (lfinite$a (lCons$a ?v1 ?v0)))) :named a12))
(assert (! (forall ((?v0 A_llist$) (?v1 A$)) (=> (lfinite$ ?v0) (lfinite$ (lCons$ ?v1 ?v0)))) :named a13))
(assert (! (forall ((?v0 A_llist_llist$) (?v1 A_llist_bool_fun$)) (=> (lfinite$a ?v0) (lfinite$a (lfilter$ ?v1 ?v0)))) :named a14))
(assert (! (forall ((?v0 A_llist$) (?v1 A_bool_fun$)) (=> (lfinite$ ?v0) (lfinite$ (lfilter$a ?v1 ?v0)))) :named a15))
(assert (! (forall ((?v0 A_llist_llist$)) (=> (lnull$ ?v0) (lfinite$a ?v0))) :named a16))
(assert (! (forall ((?v0 A_llist$)) (=> (lnull$a ?v0) (lfinite$ ?v0))) :named a17))
(assert (! (forall ((?v0 A_llist_llist$) (?v1 A_llist_llist$)) (! (=> (not (lfinite$a ?v0)) (= (lappend$ ?v0 ?v1) ?v0)) :pattern ((lappend$ ?v0 ?v1)))) :named a18))
(assert (! (forall ((?v0 A_llist$) (?v1 A_llist$)) (! (=> (not (lfinite$ ?v0)) (= (lappend$a ?v0 ?v1) ?v0)) :pattern ((lappend$a ?v0 ?v1)))) :named a19))
(assert (! (forall ((?v0 A_llist_llist$) (?v1 A_llist_llist_llist$)) (! (= (lconcat$a (lCons$b ?v0 ?v1)) (lappend$ ?v0 (lconcat$a ?v1))) :pattern ((lCons$b ?v0 ?v1)))) :named a20))
(assert (! (forall ((?v0 A_llist$) (?v1 A_llist_llist$)) (! (= (lconcat$ (lCons$a ?v0 ?v1)) (lappend$a ?v0 (lconcat$ ?v1))) :pattern ((lCons$a ?v0 ?v1)))) :named a21))
(assert (! (forall ((?v0 A$) (?v1 A_llist$) (?v2 A$) (?v3 A_llist$)) (= (= (lCons$ ?v0 ?v1) (lCons$ ?v2 ?v3)) (and (= ?v0 ?v2) (= ?v1 ?v3)))) :named a22))
(assert (! (forall ((?v0 A_llist$) (?v1 A_llist_llist$) (?v2 A_llist$) (?v3 A_llist_llist$)) (= (= (lCons$a ?v0 ?v1) (lCons$a ?v2 ?v3)) (and (= ?v0 ?v2) (= ?v1 ?v3)))) :named a23))
(assert (! (forall ((?v0 A_bool_fun$) (?v1 A_llist$)) (= (lfilter$a ?v0 (lfilter$a ?v0 ?v1)) (lfilter$a ?v0 ?v1))) :named a24))
(assert (! (forall ((?v0 A_llist_llist$) (?v1 A_llist_bool_fun$) (?v2 A_llist_llist$)) (=> (lfinite$a ?v0) (= (lfilter$ ?v1 (lappend$ ?v0 ?v2)) (lappend$ (lfilter$ ?v1 ?v0) (lfilter$ ?v1 ?v2))))) :named a25))
(assert (! (forall ((?v0 A_llist$) (?v1 A_bool_fun$) (?v2 A_llist$)) (=> (lfinite$ ?v0) (= (lfilter$a ?v1 (lappend$a ?v0 ?v2)) (lappend$a (lfilter$a ?v1 ?v0) (lfilter$a ?v1 ?v2))))) :named a26))
(assert (! (forall ((?v0 A$) (?v1 A_llist$) (?v2 A_llist$)) (! (= (lappend$a (lCons$ ?v0 ?v1) ?v2) (lCons$ ?v0 (lappend$a ?v1 ?v2))) :pattern ((lappend$a (lCons$ ?v0 ?v1) ?v2)))) :named a27))
(assert (! (forall ((?v0 A_llist$) (?v1 A_llist_llist$) (?v2 A_llist_llist$)) (! (= (lappend$ (lCons$a ?v0 ?v1) ?v2) (lCons$a ?v0 (lappend$ ?v1 ?v2))) :pattern ((lappend$ (lCons$a ?v0 ?v1) ?v2)))) :named a28))
(check-sat)
;(get-unsat-core)
