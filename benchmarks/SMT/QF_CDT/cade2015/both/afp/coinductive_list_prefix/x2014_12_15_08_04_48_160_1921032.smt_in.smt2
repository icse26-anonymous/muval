; --full-saturate-quant --inst-when=full-last-call --inst-no-entail --term-db-mode=relevant --random-seed=1 --lang=smt2 --tlimit 425
;(set-option :produce-unsat-cores true)
(set-logic ALL_SUPPORTED)
(declare-sort A$ 0)
(declare-codatatypes () ((A_llist$ (lNil$) (lCons$ (lhd$ A$) (ltl$ A_llist$)))))
(declare-fun xs$ () A_llist$)
(declare-fun ys$ () A_llist$)
(declare-fun inf$ (A_llist$ A_llist$) A_llist$)
(declare-fun lprefix$ (A_llist$ A_llist$) Bool)
(assert (! (not (lprefix$ (inf$ xs$ ys$) xs$)) :named a0))
(assert (! (forall ((?v0 A_llist$)) (lprefix$ ?v0 ?v0)) :named a1))
(assert (! (forall ((?v0 A_llist$)) (lprefix$ ?v0 ?v0)) :named a2))
(assert (! (forall ((?v0 A_llist$) (?v1 A_llist$)) (=> (and (lprefix$ ?v0 ?v1) (lprefix$ ?v1 ?v0)) (= ?v0 ?v1))) :named a3))
(assert (! (forall ((?v0 A_llist$) (?v1 A_llist$)) (=> (and (lprefix$ ?v0 ?v1) (lprefix$ ?v1 ?v0)) (= ?v0 ?v1))) :named a4))
(assert (! (forall ((?v0 A_llist$) (?v1 A_llist$) (?v2 A_llist$)) (=> (and (lprefix$ ?v0 ?v1) (lprefix$ ?v2 ?v1)) (or (lprefix$ ?v0 ?v2) (lprefix$ ?v2 ?v0)))) :named a5))
(check-sat)
;(get-unsat-core)
