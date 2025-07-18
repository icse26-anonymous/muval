; --full-saturate-quant --inst-when=full-last-call --inst-no-entail --term-db-mode=relevant --random-seed=1 --lang=smt2 --tlimit 487
;(set-option :produce-unsat-cores true)
(set-logic ALL_SUPPORTED)
(declare-sort Ref$ 0)
(declare-datatypes () ((Dag$ (tip$) (node$ (select$ Dag$) (selecta$ Ref$) (selectb$ Dag$)))))
(declare-fun x$ () Dag$)
(declare-fun y$ () Dag$)
(declare-fun z$ () Dag$)
(declare-fun less$ (Dag$ Dag$) Bool)
(declare-fun subdag$ (Dag$ Dag$) Bool)
(declare-fun less_eq$ (Dag$ Dag$) Bool)
(assert (! (not (less$ x$ y$)) :named a0))
(assert (! (not (= x$ y$)) :named a1))
(assert (! (less_eq$ x$ y$) :named a2))
(assert (! (less_eq$ y$ z$) :named a3))
(assert (! (forall ((?v0 Dag$) (?v1 Dag$)) (! (= (less_eq$ ?v0 ?v1) (or (= ?v0 ?v1) (less$ ?v0 ?v1))) :pattern ((less_eq$ ?v0 ?v1)))) :named a4))
(assert (! (forall ((?v0 Dag$) (?v1 Dag$)) (! (= (less$ ?v0 ?v1) (subdag$ ?v1 ?v0)) :pattern ((less$ ?v0 ?v1)))) :named a5))
(check-sat)
;(get-unsat-core)
