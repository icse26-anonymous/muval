; --full-saturate-quant --inst-when=full-last-call --inst-no-entail --term-db-mode=relevant --random-seed=1 --lang=smt2 --tlimit 312
;(set-option :produce-unsat-cores true)
(set-logic ALL_SUPPORTED)
(declare-sort N$ 0)
(declare-sort T$ 0)
(declare-sort Dtree$ 0)
(declare-sort N_set$ 0)
(declare-sort T_set$ 0)
(declare-sort T_dtree_sum_set$ 0)
(declare-sort T_T_dtree_sum_fun$ 0)
(declare-datatypes () ((T_dtree_sum$ (inl$ (projl$ T$)) (inr$ (projr$ Dtree$)))))
(declare-fun ta$ () T$)
(declare-fun tr$ () Dtree$)
(declare-fun uu$ () T_T_dtree_sum_fun$)
(declare-fun bot$ () N_set$)
(declare-fun nsa$ () N_set$)
(declare-fun tr0$ () Dtree$)
(declare-fun tr1$ () Dtree$)
(declare-fun tra$ () Dtree$)
(declare-fun cont$ (Dtree$) T_dtree_sum_set$)
(declare-fun inFr$ (N_set$ Dtree$ T$) Bool)
(declare-fun root$ (Dtree$) N$)
(declare-fun tr1a$ () Dtree$)
(declare-fun inFrr$ (N_set$ Dtree$ T$) Bool)
(declare-fun minus$ (N_set$ N_set$) N_set$)
(declare-fun insert$ (N$ N_set$) N_set$)
(declare-fun member$ (T$ T_set$) Bool)
(declare-fun vimage$ (T_T_dtree_sum_fun$ T_dtree_sum_set$) T_set$)
(declare-fun fun_app$ (T_T_dtree_sum_fun$ T$) T_dtree_sum$)
(declare-fun member$a (T_dtree_sum$ T_dtree_sum_set$) Bool)
(declare-fun member$b (N$ N_set$) Bool)
(declare-fun hsubst_c$ (Dtree$ Dtree$) T_dtree_sum_set$)
(assert (! (forall ((?v0 T$)) (! (= (fun_app$ uu$ ?v0) (inl$ ?v0)) :pattern ((fun_app$ uu$ ?v0)))) :named a0))
(assert (! (not (or (member$ ta$ (vimage$ uu$ (cont$ tr0$))) (or (exists ((?v0 Dtree$)) (and (member$a (inr$ ?v0) (cont$ tr0$)) (inFr$ (minus$ nsa$ (insert$ (root$ tr0$) bot$)) ?v0 ta$))) (inFr$ (minus$ nsa$ (insert$ (root$ tr0$) bot$)) tra$ ta$)))) :named a1))
(assert (! (member$a (inr$ tr$) (cont$ tr0$)) :named a2))
(assert (! (= (root$ tr1a$) (root$ tr0$)) :named a3))
(assert (! (member$b (root$ tr1a$) nsa$) :named a4))
(assert (! (inFr$ (minus$ nsa$ (insert$ (root$ tr0$) bot$)) tr$ ta$) :named a5))
(assert (! (inFr$ nsa$ tr1$ ta$) :named a6))
(assert (! (forall ((?v0 Dtree$)) (! (= (hsubst_c$ tr0$ ?v0) (ite (= (root$ ?v0) (root$ tr0$)) (cont$ tr0$) (cont$ ?v0))) :pattern ((hsubst_c$ tr0$ ?v0)))) :named a7))
(assert (! (or (member$ ta$ (vimage$ uu$ (cont$ tr0$))) (or (inFrr$ (minus$ nsa$ (insert$ (root$ tr0$) bot$)) tr0$ ta$) (inFr$ (minus$ nsa$ (insert$ (root$ tr0$) bot$)) tr$ ta$))) :named a8))
(assert (! (forall ((?v0 N_set$) (?v1 Dtree$) (?v2 T$)) (= (inFr$ ?v0 ?v1 ?v2) (or (exists ((?v3 Dtree$) (?v4 N_set$) (?v5 T$)) (and (= ?v0 ?v4) (and (= ?v1 ?v3) (and (= ?v2 ?v5) (and (member$b (root$ ?v3) ?v4) (member$a (inl$ ?v5) (cont$ ?v3))))))) (exists ((?v3 Dtree$) (?v4 N_set$) (?v5 Dtree$) (?v6 T$)) (and (= ?v0 ?v4) (and (= ?v1 ?v3) (and (= ?v2 ?v6) (and (member$b (root$ ?v3) ?v4) (and (member$a (inr$ ?v5) (cont$ ?v3)) (inFr$ ?v4 ?v5 ?v6)))))))))) :named a9))
(assert (! (forall ((?v0 N_set$) (?v1 Dtree$) (?v2 T$)) (=> (and (inFr$ ?v0 ?v1 ?v2) (and (forall ((?v3 Dtree$) (?v4 N_set$) (?v5 T$)) (=> (and (= ?v0 ?v4) (and (= ?v1 ?v3) (and (= ?v2 ?v5) (and (member$b (root$ ?v3) ?v4) (member$a (inl$ ?v5) (cont$ ?v3)))))) false)) (forall ((?v3 Dtree$) (?v4 N_set$) (?v5 Dtree$) (?v6 T$)) (=> (and (= ?v0 ?v4) (and (= ?v1 ?v3) (and (= ?v2 ?v6) (and (member$b (root$ ?v3) ?v4) (and (member$a (inr$ ?v5) (cont$ ?v3)) (inFr$ ?v4 ?v5 ?v6)))))) false)))) false)) :named a10))
(assert (! (forall ((?v0 N_set$) (?v1 Dtree$) (?v2 T$) (?v3 Dtree$)) (=> (and (inFr$ ?v0 ?v1 ?v2) (member$a (inr$ ?v1) (cont$ ?v3))) (inFr$ (insert$ (root$ ?v3) ?v0) ?v3 ?v2))) :named a11))
(assert (! (forall ((?v0 N_set$) (?v1 Dtree$) (?v2 T$)) (=> (inFr$ ?v0 ?v1 ?v2) (member$b (root$ ?v1) ?v0))) :named a12))
(assert (! (forall ((?v0 Dtree$) (?v1 N_set$) (?v2 T$)) (=> (and (member$b (root$ ?v0) ?v1) (member$a (inl$ ?v2) (cont$ ?v0))) (inFr$ ?v1 ?v0 ?v2))) :named a13))
(assert (! (forall ((?v0 Dtree$) (?v1 N_set$) (?v2 Dtree$) (?v3 T$)) (=> (and (member$b (root$ ?v0) ?v1) (and (member$a (inr$ ?v2) (cont$ ?v0)) (inFr$ ?v1 ?v2 ?v3))) (inFr$ ?v1 ?v0 ?v3))) :named a14))
(assert (! (forall ((?v0 Dtree$) (?v1 N_set$) (?v2 T$)) (=> (not (member$b (root$ ?v0) ?v1)) (not (inFr$ ?v1 ?v0 ?v2)))) :named a15))
(assert (! (= (root$ tr1a$) (root$ tra$)) :named a16))
(assert (! (member$a (inr$ tr1$) (cont$ tr1a$)) :named a17))
(assert (! (forall ((?v0 N$) (?v1 N_set$)) (= (insert$ ?v0 (minus$ ?v1 (insert$ ?v0 bot$))) (insert$ ?v0 ?v1))) :named a18))
(check-sat)
;(get-unsat-core)
