; --full-saturate-quant --inst-when=full-last-call --inst-no-entail --term-db-mode=relevant --random-seed=1 --lang=smt2 --tlimit 363
;(set-option :produce-unsat-cores true)
(set-logic ALL_SUPPORTED)
(declare-sort N$ 0)
(declare-sort N_dtree_fun$ 0)
(declare-sort N_list_N_list_fun$ 0)
(declare-datatypes () ((N_list$ (nil$) (cons$ (hd$ N$) (tl$ N_list$)))))
(declare-fun f$ () N_dtree_fun$)
(declare-fun n$ () N$)
(declare-fun nl1$ () N_list$)
(declare-fun nl2$ () N_list$)
(declare-fun last$ (N_list$) N$)
(declare-fun path$ (N_dtree_fun$ N_list$) Bool)
(declare-fun append$ (N_list$) N_list_N_list_fun$)
(declare-fun fun_app$ (N_list_N_list_fun$ N_list$) N_list$)
(assert (! (not (path$ f$ (fun_app$ (append$ (cons$ n$ nil$)) nl2$))) :named a0))
(assert (! (path$ f$ (cons$ (last$ (cons$ n$ nil$)) nl2$)) :named a1))
(assert (! (path$ f$ nl1$) :named a2))
(assert (! (path$ f$ (cons$ (last$ nl1$) nl2$)) :named a3))
(assert (! (forall ((?v0 N_dtree_fun$) (?v1 N_list$) (?v2 N_list$)) (=> (and (path$ ?v0 (fun_app$ (append$ ?v1) ?v2)) (not (= ?v2 nil$))) (path$ ?v0 ?v2))) :named a4))
(assert (! (forall ((?v0 N_dtree_fun$) (?v1 N$) (?v2 N_list$)) (=> (and (path$ ?v0 (cons$ ?v1 ?v2)) (not (= ?v2 nil$))) (path$ ?v0 ?v2))) :named a5))
(assert (! (forall ((?v0 N_dtree_fun$) (?v1 N_list$)) (=> (path$ ?v0 ?v1) (not (= ?v1 nil$)))) :named a6))
(assert (! (forall ((?v0 N_dtree_fun$) (?v1 N$)) (path$ ?v0 (cons$ ?v1 nil$))) :named a7))
(assert (! (forall ((?v0 N_list$) (?v1 N$)) (= (last$ (fun_app$ (append$ ?v0) (cons$ ?v1 nil$))) ?v1)) :named a8))
(assert (! (forall ((?v0 N_list$) (?v1 N_list$)) (=> (= ?v0 nil$) (= (last$ (fun_app$ (append$ ?v1) ?v0)) (last$ ?v1)))) :named a9))
(assert (! (forall ((?v0 N_list$) (?v1 N_list$)) (=> (not (= ?v0 nil$)) (= (last$ (fun_app$ (append$ ?v1) ?v0)) (last$ ?v0)))) :named a10))
(assert (! (forall ((?v0 N_list$) (?v1 N$) (?v2 N_list$) (?v3 N$)) (= (= (fun_app$ (append$ ?v0) (cons$ ?v1 nil$)) (fun_app$ (append$ ?v2) (cons$ ?v3 nil$))) (and (= ?v0 ?v2) (= ?v1 ?v3)))) :named a11))
(assert (! (forall ((?v0 N_list$) (?v1 N_list$)) (= (= (fun_app$ (append$ ?v0) ?v1) ?v1) (= ?v0 nil$))) :named a12))
(assert (! (forall ((?v0 N_list$) (?v1 N_list$)) (= (= (fun_app$ (append$ ?v0) ?v1) ?v0) (= ?v1 nil$))) :named a13))
(assert (! (forall ((?v0 N_list$) (?v1 N_list$)) (= (= ?v0 (fun_app$ (append$ ?v1) ?v0)) (= ?v1 nil$))) :named a14))
(assert (! (forall ((?v0 N_list$) (?v1 N_list$)) (= (= ?v0 (fun_app$ (append$ ?v0) ?v1)) (= ?v1 nil$))) :named a15))
(assert (! (forall ((?v0 N_list$) (?v1 N_list$)) (= (= nil$ (fun_app$ (append$ ?v0) ?v1)) (and (= ?v0 nil$) (= ?v1 nil$)))) :named a16))
(assert (! (forall ((?v0 N_list$) (?v1 N_list$)) (= (= (fun_app$ (append$ ?v0) ?v1) nil$) (and (= ?v0 nil$) (= ?v1 nil$)))) :named a17))
(assert (! (forall ((?v0 N_list$)) (! (= (fun_app$ (append$ ?v0) nil$) ?v0) :pattern ((append$ ?v0)))) :named a18))
(check-sat)
;(get-unsat-core)
