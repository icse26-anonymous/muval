; --full-saturate-quant --inst-when=full-last-call --inst-no-entail --term-db-mode=relevant --random-seed=1 --lang=smt2 --tlimit 372
;(set-option :produce-unsat-cores true)
(set-logic ALL_SUPPORTED)
(declare-sort A$ 0)
(declare-sort A_llist_set$ 0)
(declare-sort A_llist_bool_fun$ 0)
(declare-sort A_llist_a_llist_fun$ 0)
(declare-codatatypes () ((A_llist$ (lNil$) (lCons$ (lhd$ A$) (ltl$ A_llist$)))))
(declare-fun x$ () A$)
(declare-fun uu$ () A_llist_a_llist_fun$)
(declare-fun x$a () A$)
(declare-fun xs$ () A_llist$)
(declare-fun inf$ (A_llist_set$ A_llist_set$) A_llist_set$)
(declare-fun uua$ () A_llist_bool_fun$)
(declare-fun uub$ () A_llist_bool_fun$)
(declare-fun uuc$ () A_llist_bool_fun$)
(declare-fun xsa$ () A_llist$)
(declare-fun image$ (A_llist_a_llist_fun$ A_llist_set$) A_llist_set$)
(declare-fun lnull$ (A_llist$) Bool)
(declare-fun member$ (A_llist$ A_llist_set$) Bool)
(declare-fun collect$ (A_llist_bool_fun$) A_llist_set$)
(declare-fun fun_app$ (A_llist_bool_fun$ A_llist$) Bool)
(declare-fun lfinite$ (A_llist$) Bool)
(declare-fun lprefix$ (A_llist$ A_llist$) Bool)
(declare-fun fun_app$a (A_llist_a_llist_fun$ A_llist$) A_llist$)
(assert (! (forall ((?v0 A_llist$)) (! (= (fun_app$ uuc$ ?v0) (and (lprefix$ ?v0 (ltl$ xsa$)) (not (= ?v0 (ltl$ xsa$))))) :pattern ((fun_app$ uuc$ ?v0)))) :named a0))
(assert (! (forall ((?v0 A_llist$)) (! (= (fun_app$ uua$ ?v0) (and (lprefix$ ?v0 xsa$) (not (= ?v0 xsa$)))) :pattern ((fun_app$ uua$ ?v0)))) :named a1))
(assert (! (forall ((?v0 A_llist$)) (! (= (fun_app$ uub$ ?v0) (not (lnull$ ?v0))) :pattern ((fun_app$ uub$ ?v0)))) :named a2))
(assert (! (forall ((?v0 A_llist$)) (! (= (fun_app$a uu$ ?v0) (ltl$ ?v0)) :pattern ((fun_app$a uu$ ?v0)))) :named a3))
(assert (! (not (= (image$ uu$ (inf$ (collect$ uua$) (collect$ uub$))) (collect$ uuc$))) :named a4))
(assert (! (= xsa$ (lCons$ x$ (lCons$ x$a xs$))) :named a5))
(assert (! (not (lfinite$ xsa$)) :named a6))
(assert (! (forall ((?v0 A_llist$)) (lprefix$ ?v0 ?v0)) :named a7))
(assert (! (=> (forall ((?v0 A$) (?v1 A$) (?v2 A_llist$)) (=> (and (= xsa$ (lCons$ ?v0 (lCons$ ?v1 ?v2))) (not (lfinite$ ?v2))) false)) false) :named a8))
(assert (! (forall ((?v0 A_llist_set$)) (=> (and (=> (forall ((?v1 A_llist$)) (=> (member$ ?v1 ?v0) (lnull$ ?v1))) false) (=> (not (forall ((?v1 A_llist$)) (=> (member$ ?v1 ?v0) (lnull$ ?v1)))) false)) false)) :named a9))
(assert (! (forall ((?v0 A_llist$) (?v1 A_llist$)) (=> (and (=> (and (lnull$ ?v0) (lnull$ ?v1)) false) (=> (or (not (lnull$ ?v0)) (not (lnull$ ?v1))) false)) false)) :named a10))
(assert (! (forall ((?v0 A_llist$)) (=> (and (=> (lnull$ ?v0) false) (=> (not (lnull$ ?v0)) false)) false)) :named a11))
(assert (! (forall ((?v0 A_llist$) (?v1 A_llist$)) (=> (and (lprefix$ ?v0 ?v1) (lprefix$ ?v1 ?v0)) (= ?v0 ?v1))) :named a12))
(assert (! (forall ((?v0 A_llist$) (?v1 A_llist$) (?v2 A_llist$)) (=> (and (lprefix$ ?v0 ?v1) (lprefix$ ?v2 ?v1)) (or (lprefix$ ?v0 ?v2) (lprefix$ ?v2 ?v0)))) :named a13))
(assert (! (forall ((?v0 A_llist$) (?v1 A_llist$) (?v2 A_llist$)) (=> (and (lprefix$ ?v0 ?v1) (lprefix$ ?v1 ?v2)) (lprefix$ ?v0 ?v2))) :named a14))
(assert (! (forall ((?v0 A_llist$) (?v1 A_llist$)) (=> (and (lprefix$ ?v0 ?v1) (not (lnull$ ?v0))) (not (lnull$ ?v1)))) :named a15))
(assert (! (forall ((?v0 A_llist$) (?v1 A_llist$)) (=> (and (lprefix$ ?v0 ?v1) (lnull$ ?v1)) (lnull$ ?v0))) :named a16))
(assert (! (forall ((?v0 A_llist$) (?v1 A_llist$)) (=> (lprefix$ ?v0 ?v1) (lprefix$ (ltl$ ?v0) (ltl$ ?v1)))) :named a17))
(assert (! (forall ((?v0 A_llist$) (?v1 A_llist$)) (! (=> (lnull$ ?v0) (= (lprefix$ ?v1 ?v0) (lnull$ ?v1))) :pattern ((lprefix$ ?v1 ?v0)))) :named a18))
(assert (! (forall ((?v0 A_llist$) (?v1 A_llist$)) (=> (lnull$ ?v0) (lprefix$ ?v0 ?v1))) :named a19))
(assert (! (forall ((?v0 A_llist$)) (=> (lnull$ ?v0) (lnull$ (ltl$ ?v0)))) :named a20))
(assert (! (forall ((?v0 A_llist$)) (= (lfinite$ (ltl$ ?v0)) (lfinite$ ?v0))) :named a21))
(check-sat)
;(get-unsat-core)
