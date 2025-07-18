; --full-saturate-quant --inst-when=full-last-call --inst-no-entail --term-db-mode=relevant --random-seed=1 --lang=smt2 --tlimit 241
;(set-option :produce-unsat-cores true)
(set-logic ALL_SUPPORTED)
(declare-sort N$ 0)
(declare-sort T$ 0)
(declare-sort Dtree$ 0)
(declare-sort N_set$ 0)
(declare-sort N_dtree_fun$ 0)
(declare-sort T_dtree_sum_set$ 0)
(declare-datatypes () ((N_list$ (nil$) (cons$ (hd$ N$) (tl$ N_list$)))
  (T_dtree_sum$ (inl$ (projl$ T$)) (inr$ (projr$ Dtree$)))
  (T_dtree_sum_list$ (nil$a) (cons$a (hd$a T_dtree_sum$) (tl$a T_dtree_sum_list$)))))
(declare-fun f$ () N_dtree_fun$)
(declare-fun n$ () N$)
(declare-fun n1$ () N$)
(declare-fun nl$ () N_list$)
(declare-fun nla$ () N_list$)
(declare-fun set$ (N_list$) N_set$)
(declare-fun cont$ (Dtree$) T_dtree_sum_set$)
(declare-fun last$ (N_list$) N$)
(declare-fun path$ (N_dtree_fun$ N_list$) Bool)
(declare-fun root$ (Dtree$) N$)
(declare-fun set$a (T_dtree_sum_list$) T_dtree_sum_set$)
(declare-fun subtr$ (N_set$ Dtree$ Dtree$) Bool)
(declare-fun append$ (N_list$ N_list$) N_list$)
(declare-fun member$ (T_dtree_sum$ T_dtree_sum_set$) Bool)
(declare-fun fun_app$ (N_dtree_fun$ N$) Dtree$)
(declare-fun member$a (N$ N_set$) Bool)
(assert (! (not (path$ f$ (cons$ n1$ nla$))) :named a0))
(assert (! (path$ f$ nl$) :named a1))
(assert (! (member$ (inr$ (fun_app$ f$ n1$)) (cont$ (fun_app$ f$ n$))) :named a2))
(assert (! (path$ f$ (cons$ n1$ nla$)) :named a3))
(assert (! (subtr$ (set$ (cons$ n1$ nla$)) (fun_app$ f$ (last$ (cons$ n1$ nla$))) (fun_app$ f$ (hd$ (cons$ n1$ nla$)))) :named a4))
(assert (! (forall ((?v0 T_dtree_sum$) (?v1 T_dtree_sum_list$) (?v2 T_dtree_sum$) (?v3 T_dtree_sum_list$)) (= (= (cons$a ?v0 ?v1) (cons$a ?v2 ?v3)) (and (= ?v0 ?v2) (= ?v1 ?v3)))) :named a5))
(assert (! (forall ((?v0 N$) (?v1 N_list$) (?v2 N$) (?v3 N_list$)) (= (= (cons$ ?v0 ?v1) (cons$ ?v2 ?v3)) (and (= ?v0 ?v2) (= ?v1 ?v3)))) :named a6))
(assert (! (forall ((?v0 N$)) (= (root$ (fun_app$ f$ ?v0)) ?v0)) :named a7))
(assert (! (forall ((?v0 N_dtree_fun$) (?v1 N$) (?v2 N_list$) (?v3 N$)) (=> (and (path$ ?v0 (cons$ ?v1 ?v2)) (member$ (inr$ (fun_app$ ?v0 ?v1)) (cont$ (fun_app$ ?v0 ?v3)))) (path$ ?v0 (cons$ ?v3 (cons$ ?v1 ?v2))))) :named a8))
(assert (! (forall ((?v0 T_dtree_sum$) (?v1 T_dtree_sum_list$)) (not (= (cons$a ?v0 ?v1) ?v1))) :named a9))
(assert (! (forall ((?v0 N$) (?v1 N_list$)) (not (= (cons$ ?v0 ?v1) ?v1))) :named a10))
(assert (! (forall ((?v0 N_dtree_fun$) (?v1 N$) (?v2 N_list$)) (=> (and (path$ ?v0 (cons$ ?v1 ?v2)) (not (= ?v2 nil$))) (path$ ?v0 ?v2))) :named a11))
(assert (! (forall ((?v0 N_dtree_fun$) (?v1 N$)) (path$ ?v0 (cons$ ?v1 nil$))) :named a12))
(assert (! (forall ((?v0 N_dtree_fun$) (?v1 N_list$) (?v2 N_list$)) (=> (and (path$ ?v0 ?v1) (path$ ?v0 (cons$ (last$ ?v1) ?v2))) (path$ ?v0 (append$ ?v1 ?v2)))) :named a13))
(assert (! (forall ((?v0 T_dtree_sum$) (?v1 T_dtree_sum_list$)) (! (= (hd$a (cons$a ?v0 ?v1)) ?v0) :pattern ((cons$a ?v0 ?v1)))) :named a14))
(assert (! (forall ((?v0 N$) (?v1 N_list$)) (! (= (hd$ (cons$ ?v0 ?v1)) ?v0) :pattern ((cons$ ?v0 ?v1)))) :named a15))
(assert (! (forall ((?v0 N_dtree_fun$) (?v1 N_list$)) (= (path$ ?v0 ?v1) (or (exists ((?v2 N$)) (= ?v1 (cons$ ?v2 nil$))) (exists ((?v2 N$) (?v3 N_list$) (?v4 N$)) (and (= ?v1 (cons$ ?v4 (cons$ ?v2 ?v3))) (and (path$ ?v0 (cons$ ?v2 ?v3)) (member$ (inr$ (fun_app$ ?v0 ?v2)) (cont$ (fun_app$ ?v0 ?v4))))))))) :named a16))
(assert (! (forall ((?v0 N_dtree_fun$) (?v1 N_list$)) (=> (and (path$ ?v0 ?v1) (and (forall ((?v2 N$)) (=> (= ?v1 (cons$ ?v2 nil$)) false)) (forall ((?v2 N$) (?v3 N_list$) (?v4 N$)) (=> (and (= ?v1 (cons$ ?v4 (cons$ ?v2 ?v3))) (and (path$ ?v0 (cons$ ?v2 ?v3)) (member$ (inr$ (fun_app$ ?v0 ?v2)) (cont$ (fun_app$ ?v0 ?v4))))) false)))) false)) :named a17))
(assert (! (forall ((?v0 T_dtree_sum$) (?v1 T_dtree_sum$) (?v2 T_dtree_sum_list$)) (=> (member$ ?v0 (set$a (cons$a ?v1 ?v2))) (or (= ?v0 ?v1) (member$ ?v0 (set$a ?v2))))) :named a18))
(assert (! (forall ((?v0 N$) (?v1 N$) (?v2 N_list$)) (=> (member$a ?v0 (set$ (cons$ ?v1 ?v2))) (or (= ?v0 ?v1) (member$a ?v0 (set$ ?v2))))) :named a19))
(assert (! (forall ((?v0 N_list$) (?v1 N_list$) (?v2 N_list$)) (= (= (append$ ?v0 ?v1) (append$ ?v0 ?v2)) (= ?v1 ?v2))) :named a20))
(check-sat)
;(get-unsat-core)
