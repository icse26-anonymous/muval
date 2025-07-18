; --full-saturate-quant --inst-when=full-last-call --inst-no-entail --term-db-mode=relevant --random-seed=1 --lang=smt2 --tlimit 500
;(set-option :produce-unsat-cores true)
(set-logic ALL_SUPPORTED)
(declare-sort A$ 0)
(declare-sort Nat$ 0)
(declare-datatypes () ((A_option$ (none$) (some$ (the$ A$)))))
(declare-codatatypes () ((A_llist$ (lNil$) (lCons$ (lhd$ A$) (ltl$ A_llist$)))))
(declare-fun i$ () Nat$)
(declare-fun j$ () Nat$)
(declare-fun t$ () A_llist$)
(declare-fun ll2f$ (A_llist$ Nat$) A_option$)
(declare-fun plus$ (Nat$ Nat$) Nat$)
(declare-fun ldrop$ (A_llist$ Nat$) A_llist$)
(declare-fun ltake$ (A_llist$ Nat$) A_llist$)
(assert (! (not (= (ll2f$ (ldrop$ t$ i$) j$) (ll2f$ t$ (plus$ i$ j$)))) :named a0))
(assert (! (forall ((?v0 A_llist$) (?v1 Nat$) (?v2 Nat$)) (= (ldrop$ ?v0 (plus$ ?v1 ?v2)) (ldrop$ (ldrop$ ?v0 ?v1) ?v2))) :named a1))
(assert (! (forall ((?v0 Nat$) (?v1 Nat$) (?v2 Nat$)) (= (= (plus$ ?v0 ?v1) (plus$ ?v2 ?v1)) (= ?v0 ?v2))) :named a2))
(assert (! (forall ((?v0 Nat$) (?v1 Nat$) (?v2 Nat$)) (= (= (plus$ ?v0 ?v1) (plus$ ?v0 ?v2)) (= ?v1 ?v2))) :named a3))
(assert (! (forall ((?v0 A_llist$) (?v1 Nat$) (?v2 Nat$)) (= (ltake$ (ldrop$ ?v0 ?v1) ?v2) (ldrop$ (ltake$ ?v0 (plus$ ?v2 ?v1)) ?v1))) :named a4))
(assert (! (forall ((?v0 Nat$) (?v1 Nat$) (?v2 Nat$)) (= (= (plus$ ?v0 ?v1) (plus$ ?v2 ?v1)) (= ?v0 ?v2))) :named a5))
(assert (! (forall ((?v0 Nat$) (?v1 Nat$) (?v2 Nat$)) (= (= (plus$ ?v0 ?v1) (plus$ ?v0 ?v2)) (= ?v1 ?v2))) :named a6))
(assert (! (forall ((?v0 Nat$) (?v1 Nat$) (?v2 Nat$) (?v3 Nat$)) (= (plus$ (plus$ ?v0 ?v1) (plus$ ?v2 ?v3)) (plus$ (plus$ ?v0 ?v2) (plus$ ?v1 ?v3)))) :named a7))
(assert (! (forall ((?v0 Nat$) (?v1 Nat$) (?v2 Nat$)) (= (plus$ (plus$ ?v0 ?v1) ?v2) (plus$ (plus$ ?v0 ?v2) ?v1))) :named a8))
(assert (! (forall ((?v0 Nat$) (?v1 Nat$) (?v2 Nat$)) (= (plus$ (plus$ ?v0 ?v1) ?v2) (plus$ ?v0 (plus$ ?v1 ?v2)))) :named a9))
(assert (! (forall ((?v0 Nat$) (?v1 Nat$) (?v2 Nat$)) (= (plus$ (plus$ ?v0 ?v1) ?v2) (plus$ ?v0 (plus$ ?v1 ?v2)))) :named a10))
(assert (! (forall ((?v0 Nat$) (?v1 Nat$) (?v2 Nat$)) (= (plus$ ?v0 (plus$ ?v1 ?v2)) (plus$ (plus$ ?v0 ?v1) ?v2))) :named a11))
(assert (! (forall ((?v0 Nat$) (?v1 Nat$) (?v2 Nat$) (?v3 Nat$)) (=> (and (= ?v0 ?v1) (= ?v2 ?v3)) (= (plus$ ?v0 ?v2) (plus$ ?v1 ?v3)))) :named a12))
(assert (! (forall ((?v0 Nat$) (?v1 Nat$) (?v2 Nat$)) (=> (= (plus$ ?v0 ?v1) (plus$ ?v0 ?v2)) (= ?v1 ?v2))) :named a13))
(assert (! (forall ((?v0 Nat$) (?v1 Nat$) (?v2 Nat$)) (=> (= (plus$ ?v0 ?v1) (plus$ ?v0 ?v2)) (= ?v1 ?v2))) :named a14))
(assert (! (forall ((?v0 Nat$) (?v1 Nat$) (?v2 Nat$)) (=> (= (plus$ ?v0 ?v1) (plus$ ?v2 ?v1)) (= ?v0 ?v2))) :named a15))
(check-sat)
;(get-unsat-core)
