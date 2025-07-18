; --full-saturate-quant --inst-when=full-last-call --inst-no-entail --term-db-mode=relevant --random-seed=1 --lang=smt2 --tlimit 452
;(set-option :produce-unsat-cores true)
(set-logic ALL_SUPPORTED)
(declare-sort A$ 0)
(declare-sort Nat$ 0)
(declare-codatatypes () ((A_stream$ (sCons$ (shd$ A$) (stl$ A_stream$)))))
(declare-datatypes () ((A_list$ (nil$) (cons$ (hd$ A$) (tl$ A_list$)))))
(declare-fun p$ () Nat$)
(declare-fun s$ () A_stream$)
(declare-fun xs$ () A_list$)
(declare-fun size$ (A_list$) Nat$)
(declare-fun snth$ (A_stream$ Nat$) A$)
(declare-fun minus$ (Nat$ Nat$) Nat$)
(declare-fun shift$ (A_list$ A_stream$) A_stream$)
(declare-fun less_eq$ (Nat$ Nat$) Bool)
(assert (! (not (= (snth$ (shift$ xs$ s$) p$) (snth$ s$ (minus$ p$ (size$ xs$))))) :named a0))
(assert (! (less_eq$ (size$ xs$) p$) :named a1))
(assert (! (forall ((?v0 A_list$) (?v1 A_stream$) (?v2 A_stream$)) (= (= (shift$ ?v0 ?v1) (shift$ ?v0 ?v2)) (= ?v1 ?v2))) :named a2))
(assert (! (forall ((?v0 Nat$) (?v1 Nat$)) (=> (less_eq$ ?v0 ?v1) (= (minus$ ?v1 (minus$ ?v1 ?v0)) ?v0))) :named a3))
(assert (! (forall ((?v0 Nat$)) (less_eq$ ?v0 ?v0)) :named a4))
(assert (! (forall ((?v0 Nat$) (?v1 Nat$) (?v2 Nat$)) (=> (and (less_eq$ ?v0 ?v1) (less_eq$ ?v0 ?v2)) (= (= (minus$ ?v1 ?v0) (minus$ ?v2 ?v0)) (= ?v1 ?v2)))) :named a5))
(assert (! (forall ((?v0 Nat$) (?v1 Nat$) (?v2 Nat$)) (=> (and (less_eq$ ?v0 ?v1) (less_eq$ ?v0 ?v2)) (= (minus$ (minus$ ?v1 ?v0) (minus$ ?v2 ?v0)) (minus$ ?v1 ?v2)))) :named a6))
(assert (! (forall ((?v0 Nat$) (?v1 Nat$) (?v2 Nat$)) (=> (and (less_eq$ ?v0 ?v1) (less_eq$ ?v0 ?v2)) (= (less_eq$ (minus$ ?v1 ?v0) (minus$ ?v2 ?v0)) (less_eq$ ?v1 ?v2)))) :named a7))
(assert (! (forall ((?v0 Nat$) (?v1 Nat$) (?v2 Nat$)) (=> (less_eq$ ?v0 ?v1) (less_eq$ (minus$ ?v2 ?v1) (minus$ ?v2 ?v0)))) :named a8))
(assert (! (forall ((?v0 Nat$) (?v1 Nat$) (?v2 Nat$)) (=> (less_eq$ ?v0 ?v1) (less_eq$ (minus$ ?v0 ?v2) (minus$ ?v1 ?v2)))) :named a9))
(assert (! (forall ((?v0 Nat$) (?v1 Nat$)) (less_eq$ (minus$ ?v0 ?v1) ?v0)) :named a10))
(assert (! (forall ((?v0 Nat$)) (less_eq$ ?v0 ?v0)) :named a11))
(assert (! (forall ((?v0 Nat$) (?v1 Nat$)) (or (less_eq$ ?v0 ?v1) (less_eq$ ?v1 ?v0))) :named a12))
(assert (! (forall ((?v0 Nat$) (?v1 Nat$)) (! (=> (less_eq$ ?v0 ?v1) (= (less_eq$ ?v1 ?v0) (= ?v1 ?v0))) :pattern ((less_eq$ ?v1 ?v0)))) :named a13))
(check-sat)
;(get-unsat-core)
