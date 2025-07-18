; --full-saturate-quant --inst-when=full-last-call --inst-no-entail --term-db-mode=relevant --random-seed=1 --lang=smt2 --tlimit 164
;(set-option :produce-unsat-cores true)
(set-logic ALL_SUPPORTED)
(declare-sort N$ 0)
(declare-sort T$ 0)
(declare-sort Dtree$ 0)
(declare-sort N_set$ 0)
(declare-sort N_set_N_set_fun$ 0)
(declare-sort T_dtree_sum_set$ 0)
(declare-sort T_dtree_sum_set_T_dtree_sum_set_fun$ 0)
(declare-datatypes () ((T_dtree_sum$ (inl$ (projl$ T$)) (inr$ (projr$ Dtree$)))))
(declare-fun ns$ () N_set$)
(declare-fun sup$ (N_set$) N_set_N_set_fun$)
(declare-fun tr1$ () Dtree$)
(declare-fun tr2$ () Dtree$)
(declare-fun tr3$ () Dtree$)
(declare-fun cont$ (Dtree$) T_dtree_sum_set$)
(declare-fun ns12$ () N_set$)
(declare-fun ns23$ () N_set$)
(declare-fun root$ (Dtree$) N$)
(declare-fun sup$a (T_dtree_sum_set$) T_dtree_sum_set_T_dtree_sum_set_fun$)
(declare-fun tr1a$ () Dtree$)
(declare-fun tr2a$ () Dtree$)
(declare-fun tr3a$ () Dtree$)
(declare-fun ns12a$ () N_set$)
(declare-fun subtr$ (N_set$ Dtree$ Dtree$) Bool)
(declare-fun tr1aa$ () Dtree$)
(declare-fun member$ (N$ N_set$) Bool)
(declare-fun fun_app$ (N_set_N_set_fun$ N_set$) N_set$)
(declare-fun member$a (T_dtree_sum$ T_dtree_sum_set$) Bool)
(declare-fun fun_app$a (T_dtree_sum_set_T_dtree_sum_set_fun$ T_dtree_sum_set$) T_dtree_sum_set$)
(assert (! (not (subtr$ (fun_app$ (sup$ ns12a$) ns$) tr1aa$ tr3a$)) :named a0))
(assert (! (member$ (root$ tr3a$) ns$) :named a1))
(assert (! (subtr$ ns$ tr1a$ tr2a$) :named a2))
(assert (! (forall ((?v0 N_set$) (?v1 Dtree$)) (=> (subtr$ ?v0 ?v1 tr1a$) (subtr$ (fun_app$ (sup$ ?v0) ns$) ?v1 tr2a$))) :named a3))
(assert (! (member$a (inr$ tr2a$) (cont$ tr3a$)) :named a4))
(assert (! (subtr$ ns12a$ tr1aa$ tr1a$) :named a5))
(assert (! (subtr$ ns12$ tr1$ tr2$) :named a6))
(assert (! (subtr$ ns23$ tr2$ tr3$) :named a7))
(assert (! (forall ((?v0 N_set$) (?v1 Dtree$) (?v2 Dtree$)) (= (subtr$ ?v0 ?v1 ?v2) (or (exists ((?v3 Dtree$) (?v4 N_set$)) (and (= ?v0 ?v4) (and (= ?v1 ?v3) (and (= ?v2 ?v3) (member$ (root$ ?v3) ?v4))))) (exists ((?v3 Dtree$) (?v4 N_set$) (?v5 Dtree$) (?v6 Dtree$)) (and (= ?v0 ?v4) (and (= ?v1 ?v5) (and (= ?v2 ?v3) (and (member$ (root$ ?v3) ?v4) (and (subtr$ ?v4 ?v5 ?v6) (member$a (inr$ ?v6) (cont$ ?v3))))))))))) :named a8))
(assert (! (forall ((?v0 N_set$) (?v1 Dtree$) (?v2 Dtree$)) (=> (and (subtr$ ?v0 ?v1 ?v2) (and (forall ((?v3 Dtree$) (?v4 N_set$)) (=> (and (= ?v0 ?v4) (and (= ?v1 ?v3) (and (= ?v2 ?v3) (member$ (root$ ?v3) ?v4)))) false)) (forall ((?v3 Dtree$) (?v4 N_set$) (?v5 Dtree$) (?v6 Dtree$)) (=> (and (= ?v0 ?v4) (and (= ?v1 ?v5) (and (= ?v2 ?v3) (and (member$ (root$ ?v3) ?v4) (and (subtr$ ?v4 ?v5 ?v6) (member$a (inr$ ?v6) (cont$ ?v3))))))) false)))) false)) :named a9))
(assert (! (forall ((?v0 N_set$) (?v1 Dtree$) (?v2 Dtree$)) (=> (subtr$ ?v0 ?v1 ?v2) (member$ (root$ ?v2) ?v0))) :named a10))
(assert (! (forall ((?v0 N_set$) (?v1 Dtree$) (?v2 Dtree$)) (=> (subtr$ ?v0 ?v1 ?v2) (member$ (root$ ?v1) ?v0))) :named a11))
(assert (! (forall ((?v0 Dtree$) (?v1 N_set$) (?v2 Dtree$) (?v3 Dtree$)) (=> (and (member$ (root$ ?v0) ?v1) (and (subtr$ ?v1 ?v2 ?v3) (member$a (inr$ ?v3) (cont$ ?v0)))) (subtr$ ?v1 ?v2 ?v0))) :named a12))
(assert (! (forall ((?v0 Dtree$) (?v1 N_set$)) (=> (member$ (root$ ?v0) ?v1) (subtr$ ?v1 ?v0 ?v0))) :named a13))
(assert (! (forall ((?v0 Dtree$) (?v1 Dtree$)) (= (= (inr$ ?v0) (inr$ ?v1)) (= ?v0 ?v1))) :named a14))
(assert (! (forall ((?v0 Dtree$) (?v1 Dtree$)) (= (= (inr$ ?v0) (inr$ ?v1)) (= ?v0 ?v1))) :named a15))
(assert (! (forall ((?v0 T_dtree_sum$) (?v1 T_dtree_sum_set$) (?v2 T_dtree_sum_set$)) (= (member$a ?v0 (fun_app$a (sup$a ?v1) ?v2)) (or (member$a ?v0 ?v1) (member$a ?v0 ?v2)))) :named a16))
(assert (! (forall ((?v0 N$) (?v1 N_set$) (?v2 N_set$)) (= (member$ ?v0 (fun_app$ (sup$ ?v1) ?v2)) (or (member$ ?v0 ?v1) (member$ ?v0 ?v2)))) :named a17))
(assert (! (forall ((?v0 T_dtree_sum$) (?v1 T_dtree_sum_set$) (?v2 T_dtree_sum_set$)) (=> (=> (not (member$a ?v0 ?v1)) (member$a ?v0 ?v2)) (member$a ?v0 (fun_app$a (sup$a ?v2) ?v1)))) :named a18))
(assert (! (forall ((?v0 N$) (?v1 N_set$) (?v2 N_set$)) (=> (=> (not (member$ ?v0 ?v1)) (member$ ?v0 ?v2)) (member$ ?v0 (fun_app$ (sup$ ?v2) ?v1)))) :named a19))
(assert (! (forall ((?v0 T_dtree_sum_set$) (?v1 T_dtree_sum_set$)) (= (fun_app$a (sup$a (fun_app$a (sup$a ?v0) ?v1)) ?v1) (fun_app$a (sup$a ?v0) ?v1))) :named a20))
(assert (! (forall ((?v0 N_set$) (?v1 N_set$)) (= (fun_app$ (sup$ (fun_app$ (sup$ ?v0) ?v1)) ?v1) (fun_app$ (sup$ ?v0) ?v1))) :named a21))
(assert (! (forall ((?v0 T_dtree_sum_set$) (?v1 T_dtree_sum_set$)) (= (fun_app$a (sup$a ?v0) (fun_app$a (sup$a ?v0) ?v1)) (fun_app$a (sup$a ?v0) ?v1))) :named a22))
(assert (! (forall ((?v0 N_set$) (?v1 N_set$)) (= (fun_app$ (sup$ ?v0) (fun_app$ (sup$ ?v0) ?v1)) (fun_app$ (sup$ ?v0) ?v1))) :named a23))
(assert (! (forall ((?v0 T_dtree_sum_set$) (?v1 T_dtree_sum_set$)) (= (fun_app$a (sup$a ?v0) (fun_app$a (sup$a ?v0) ?v1)) (fun_app$a (sup$a ?v0) ?v1))) :named a24))
(assert (! (forall ((?v0 N_set$) (?v1 N_set$)) (= (fun_app$ (sup$ ?v0) (fun_app$ (sup$ ?v0) ?v1)) (fun_app$ (sup$ ?v0) ?v1))) :named a25))
(assert (! (forall ((?v0 T_dtree_sum_set$)) (! (= (fun_app$a (sup$a ?v0) ?v0) ?v0) :pattern ((sup$a ?v0)))) :named a26))
(assert (! (forall ((?v0 N_set$)) (! (= (fun_app$ (sup$ ?v0) ?v0) ?v0) :pattern ((sup$ ?v0)))) :named a27))
(check-sat)
;(get-unsat-core)
