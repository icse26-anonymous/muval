; --full-saturate-quant --inst-when=full-last-call --inst-no-entail --term-db-mode=relevant --random-seed=1 --lang=smt2 --tlimit 509
;(set-option :produce-unsat-cores true)
(set-logic ALL_SUPPORTED)
(declare-sort A$ 0)
(declare-sort A_set$ 0)
(declare-datatypes () ((A_list$ (nil$) (cons$ (hd$ A$) (tl$ A_list$)))))
(declare-fun x$ () A$)
(declare-fun xs$ () A_list$)
(declare-fun set$ (A_list$) A_set$)
(declare-fun union$ (A_list$ A_list$) A_list$)
(declare-fun insert$ (A$ A_list$) A_list$)
(declare-fun member$ (A$ A_set$) Bool)
(declare-fun sorted$ (A_list$) Bool)
(declare-fun member$a (A_list$ A$) Bool)
(declare-fun distinct$ (A_list$) Bool)
(declare-fun memb_sorted$ (A_list$ A$) Bool)
(declare-fun insertion_sort$ (A$ A_list$) A_list$)
(declare-fun mergesort_remdups$ (A_list$) A_list$)
(assert (! (not (and (distinct$ (insertion_sort$ x$ xs$)) (and (sorted$ (insertion_sort$ x$ xs$)) (= (set$ (insertion_sort$ x$ xs$)) (set$ (cons$ x$ xs$)))))) :named a0))
(assert (! (sorted$ xs$) :named a1))
(assert (! (distinct$ xs$) :named a2))
(assert (! (forall ((?v0 A_list$) (?v1 A_list$)) (=> (and (and (distinct$ ?v0) (sorted$ ?v0)) (and (distinct$ ?v1) (sorted$ ?v1))) (= (= ?v0 ?v1) (= (set$ ?v0) (set$ ?v1))))) :named a3))
(assert (! (forall ((?v0 A_list$) (?v1 A_list$)) (=> (and (sorted$ ?v0) (and (distinct$ ?v0) (and (sorted$ ?v1) (and (distinct$ ?v1) (= (set$ ?v0) (set$ ?v1)))))) (= ?v0 ?v1))) :named a4))
(assert (! (forall ((?v0 A$) (?v1 A_list$)) (! (= (distinct$ (cons$ ?v0 ?v1)) (and (not (member$ ?v0 (set$ ?v1))) (distinct$ ?v1))) :pattern ((cons$ ?v0 ?v1)))) :named a5))
(assert (! (forall ((?v0 A$) (?v1 A_list$) (?v2 A$) (?v3 A_list$)) (= (= (cons$ ?v0 ?v1) (cons$ ?v2 ?v3)) (and (= ?v0 ?v2) (= ?v1 ?v3)))) :named a6))
(assert (! (forall ((?v0 A$) (?v1 A$) (?v2 A_list$)) (! (= (distinct$ (cons$ ?v0 (cons$ ?v1 ?v2))) (and (not (= ?v0 ?v1)) (and (distinct$ (cons$ ?v0 ?v2)) (distinct$ (cons$ ?v1 ?v2))))) :pattern ((cons$ ?v0 (cons$ ?v1 ?v2))))) :named a7))
(assert (! (forall ((?v0 A$) (?v1 A$) (?v2 A_list$)) (=> (member$ ?v0 (set$ (cons$ ?v1 ?v2))) (or (= ?v0 ?v1) (member$ ?v0 (set$ ?v2))))) :named a8))
(assert (! (forall ((?v0 A$) (?v1 A_list$)) (=> (and (member$ ?v0 (set$ ?v1)) (and (forall ((?v2 A_list$)) (=> (= ?v1 (cons$ ?v0 ?v2)) false)) (forall ((?v2 A$) (?v3 A_list$)) (=> (and (= ?v1 (cons$ ?v2 ?v3)) (member$ ?v0 (set$ ?v3))) false)))) false)) :named a9))
(assert (! (forall ((?v0 A$) (?v1 A_list$) (?v2 A$)) (=> (member$ ?v0 (set$ ?v1)) (member$ ?v0 (set$ (cons$ ?v2 ?v1))))) :named a10))
(assert (! (forall ((?v0 A$) (?v1 A_list$)) (member$ ?v0 (set$ (cons$ ?v0 ?v1)))) :named a11))
(assert (! (forall ((?v0 A_list$)) (and (distinct$ (mergesort_remdups$ ?v0)) (and (sorted$ (mergesort_remdups$ ?v0)) (= (set$ (mergesort_remdups$ ?v0)) (set$ ?v0))))) :named a12))
(assert (! (forall ((?v0 A_list$) (?v1 A$)) (! (=> (sorted$ ?v0) (= (memb_sorted$ ?v0 ?v1) (member$ ?v1 (set$ ?v0)))) :pattern ((memb_sorted$ ?v0 ?v1)))) :named a13))
(assert (! (forall ((?v0 A$) (?v1 A_list$) (?v2 A$) (?v3 A_list$)) (=> (= (cons$ ?v0 ?v1) (cons$ ?v2 ?v3)) (and (= ?v0 ?v2) (= ?v1 ?v3)))) :named a14))
(assert (! (forall ((?v0 A$) (?v1 A_list$)) (not (= (cons$ ?v0 ?v1) ?v1))) :named a15))
(assert (! (forall ((?v0 A_list$) (?v1 A_list$)) (= (distinct$ (union$ ?v0 ?v1)) (distinct$ ?v1))) :named a16))
(assert (! (forall ((?v0 A$) (?v1 A_list$)) (! (=> (not (member$ ?v0 (set$ ?v1))) (= (insert$ ?v0 ?v1) (cons$ ?v0 ?v1))) :pattern ((insert$ ?v0 ?v1)))) :named a17))
(assert (! (forall ((?v0 A$) (?v1 A_list$)) (! (= (insert$ ?v0 ?v1) (ite (member$ ?v0 (set$ ?v1)) ?v1 (cons$ ?v0 ?v1))) :pattern ((insert$ ?v0 ?v1)))) :named a18))
(assert (! (forall ((?v0 A$) (?v1 A_list$)) (= (member$ ?v0 (set$ ?v1)) (member$a ?v1 ?v0))) :named a19))
(check-sat)
;(get-unsat-core)
