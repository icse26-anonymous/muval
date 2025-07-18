; --full-saturate-quant --inst-when=full-last-call --inst-no-entail --term-db-mode=relevant --random-seed=1 --lang=smt2 --tlimit 198
;(set-option :produce-unsat-cores true)
(set-logic ALL_SUPPORTED)
(declare-sort N$ 0)
(declare-sort T$ 0)
(declare-sort Dtree$ 0)
(declare-sort N_set$ 0)
(declare-sort T_dtree_sum_set$ 0)
(declare-datatypes () ((T_dtree_sum$ (inl$ (projl$ T$)) (inr$ (projr$ Dtree$)))))
(declare-fun t$ () T$)
(declare-fun ns$ () N_set$)
(declare-fun tr$ () Dtree$)
(declare-fun tr1$ () Dtree$)
(declare-fun cont$ (Dtree$) T_dtree_sum_set$)
(declare-fun inFr$ (N_set$ Dtree$ T$) Bool)
(declare-fun root$ (Dtree$) N$)
(declare-fun inFr2$ (N_set$ Dtree$ T$) Bool)
(declare-fun insert$ (N$ N_set$) N_set$)
(declare-fun member$ (T_dtree_sum$ T_dtree_sum_set$) Bool)
(declare-fun insert$a (T_dtree_sum$ T_dtree_sum_set$) T_dtree_sum_set$)
(declare-fun less_eq$ (N_set$ N_set$) Bool)
(declare-fun member$a (N$ N_set$) Bool)
(declare-fun less_eq$a (T_dtree_sum_set$ T_dtree_sum_set$) Bool)
(assert (! (not (inFr2$ ns$ tr$ t$)) :named a0))
(assert (! (member$ (inr$ tr1$) (cont$ tr$)) :named a1))
(assert (! (member$a (root$ tr$) ns$) :named a2))
(assert (! (inFr2$ ns$ tr1$ t$) :named a3))
(assert (! (forall ((?v0 N_set$) (?v1 Dtree$) (?v2 T$)) (=> (inFr2$ ?v0 ?v1 ?v2) (member$a (root$ ?v1) ?v0))) :named a4))
(assert (! (forall ((?v0 N_set$) (?v1 Dtree$) (?v2 T$) (?v3 N_set$)) (=> (and (inFr2$ ?v0 ?v1 ?v2) (less_eq$ ?v0 ?v3)) (inFr2$ ?v3 ?v1 ?v2))) :named a5))
(assert (! (forall ((?v0 Dtree$) (?v1 N_set$) (?v2 T$)) (=> (and (member$a (root$ ?v0) ?v1) (member$ (inl$ ?v2) (cont$ ?v0))) (inFr2$ ?v1 ?v0 ?v2))) :named a6))
(assert (! (forall ((?v0 Dtree$) (?v1 Dtree$) (?v2 N_set$) (?v3 T$)) (=> (and (member$ (inr$ ?v0) (cont$ ?v1)) (inFr2$ ?v2 ?v0 ?v3)) (inFr2$ (insert$ (root$ ?v1) ?v2) ?v1 ?v3))) :named a7))
(assert (! (forall ((?v0 N_set$) (?v1 Dtree$) (?v2 T$)) (= (inFr2$ ?v0 ?v1 ?v2) (or (exists ((?v3 Dtree$) (?v4 N_set$) (?v5 T$)) (and (= ?v0 ?v4) (and (= ?v1 ?v3) (and (= ?v2 ?v5) (and (member$a (root$ ?v3) ?v4) (member$ (inl$ ?v5) (cont$ ?v3))))))) (exists ((?v3 Dtree$) (?v4 Dtree$) (?v5 N_set$) (?v6 T$)) (and (= ?v0 (insert$ (root$ ?v4) ?v5)) (and (= ?v1 ?v4) (and (= ?v2 ?v6) (and (member$ (inr$ ?v3) (cont$ ?v4)) (inFr2$ ?v5 ?v3 ?v6))))))))) :named a8))
(assert (! (forall ((?v0 N_set$) (?v1 Dtree$) (?v2 T$)) (=> (and (inFr2$ ?v0 ?v1 ?v2) (and (forall ((?v3 Dtree$) (?v4 N_set$) (?v5 T$)) (=> (and (= ?v0 ?v4) (and (= ?v1 ?v3) (and (= ?v2 ?v5) (and (member$a (root$ ?v3) ?v4) (member$ (inl$ ?v5) (cont$ ?v3)))))) false)) (forall ((?v3 Dtree$) (?v4 Dtree$) (?v5 N_set$) (?v6 T$)) (=> (and (= ?v0 (insert$ (root$ ?v4) ?v5)) (and (= ?v1 ?v4) (and (= ?v2 ?v6) (and (member$ (inr$ ?v3) (cont$ ?v4)) (inFr2$ ?v5 ?v3 ?v6))))) false)))) false)) :named a9))
(assert (! (forall ((?v0 T$) (?v1 Dtree$)) (= (= (inl$ ?v0) (inr$ ?v1)) false)) :named a10))
(assert (! (forall ((?v0 Dtree$) (?v1 T$)) (= (= (inr$ ?v0) (inl$ ?v1)) false)) :named a11))
(assert (! (forall ((?v0 T_dtree_sum$) (?v1 T_dtree_sum_set$) (?v2 T_dtree_sum_set$)) (= (less_eq$a (insert$a ?v0 ?v1) ?v2) (and (member$ ?v0 ?v2) (less_eq$a ?v1 ?v2)))) :named a12))
(assert (! (forall ((?v0 N$) (?v1 N_set$) (?v2 N_set$)) (= (less_eq$ (insert$ ?v0 ?v1) ?v2) (and (member$a ?v0 ?v2) (less_eq$ ?v1 ?v2)))) :named a13))
(assert (! (forall ((?v0 T$) (?v1 T$)) (= (= (inl$ ?v0) (inl$ ?v1)) (= ?v0 ?v1))) :named a14))
(assert (! (forall ((?v0 T$) (?v1 T$)) (= (= (inl$ ?v0) (inl$ ?v1)) (= ?v0 ?v1))) :named a15))
(assert (! (forall ((?v0 Dtree$) (?v1 Dtree$)) (= (= (inr$ ?v0) (inr$ ?v1)) (= ?v0 ?v1))) :named a16))
(assert (! (forall ((?v0 Dtree$) (?v1 Dtree$)) (= (= (inr$ ?v0) (inr$ ?v1)) (= ?v0 ?v1))) :named a17))
(assert (! (forall ((?v0 N_set$) (?v1 Dtree$) (?v2 T$) (?v3 Dtree$)) (=> (and (inFr$ ?v0 ?v1 ?v2) (member$ (inr$ ?v1) (cont$ ?v3))) (inFr$ (insert$ (root$ ?v3) ?v0) ?v3 ?v2))) :named a18))
(check-sat)
;(get-unsat-core)
