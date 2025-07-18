; --full-saturate-quant --inst-when=full-last-call --inst-no-entail --term-db-mode=relevant --random-seed=1 --lang=smt2 --tlimit 22
;(set-option :produce-unsat-cores true)
(set-logic ALL_SUPPORTED)
(declare-sort A$ 0)
(declare-sort A_tree$ 0)
(declare-sort A_tree_fset$ 0)
(declare-codatatypes () ((A_stream$ (sCons$ (shd$ A$) (stl$ A_stream$)))))
(declare-fun t$ () A_tree$)
(declare-fun cont$ (A_tree$) A_tree_fset$)
(declare-fun node$ (A$ A_tree_fset$) A_tree$)
(declare-fun root$ (A_tree$) A$)
(declare-fun ipath$ (A_tree$ A_stream$) Bool)
(declare-fun steps$ () A_stream$)
(declare-fun fmember$ (A_tree$ A_tree_fset$) Bool)
(declare-fun tfinite$ (A_tree$) Bool)
(assert (! (not (not (ipath$ t$ steps$))) :named a0))
(assert (! (tfinite$ t$) :named a1))
(assert (! (forall ((?v0 A_tree$)) (= (tfinite$ ?v0) (exists ((?v1 A_tree$)) (and (= ?v0 ?v1) (forall ((?v2 A_tree$)) (=> (fmember$ ?v2 (cont$ ?v1)) (tfinite$ ?v2))))))) :named a2))
(assert (! (forall ((?v0 A_tree$)) (=> (forall ((?v1 A_tree$)) (=> (fmember$ ?v1 (cont$ ?v0)) (tfinite$ ?v1))) (tfinite$ ?v0))) :named a3))
(assert (! (forall ((?v0 A_tree$)) (=> (and (tfinite$ ?v0) (forall ((?v1 A_tree$)) (=> (and (= ?v0 ?v1) (forall ((?v2 A_tree$)) (=> (fmember$ ?v2 (cont$ ?v1)) (tfinite$ ?v2)))) false))) false)) :named a4))
(assert (! (forall ((?v0 A$) (?v1 A_tree_fset$) (?v2 A$) (?v3 A_tree_fset$)) (= (= (node$ ?v0 ?v1) (node$ ?v2 ?v3)) (and (= ?v0 ?v2) (= ?v1 ?v3)))) :named a5))
(assert (! (forall ((?v0 A$) (?v1 A_tree_fset$)) (! (= (cont$ (node$ ?v0 ?v1)) ?v1) :pattern ((node$ ?v0 ?v1)))) :named a6))
(assert (! (forall ((?v0 A_tree$)) (=> (forall ((?v1 A$) (?v2 A_tree_fset$)) (=> (= ?v0 (node$ ?v1 ?v2)) false)) false)) :named a7))
(assert (! (forall ((?v0 A_tree$)) (= (node$ (root$ ?v0) (cont$ ?v0)) ?v0)) :named a8))
(assert (! (forall ((?v0 Bool) (?v1 A_tree$) (?v2 A_tree$) (?v3 A_tree_fset$)) (= (fmember$ (ite ?v0 ?v1 ?v2) ?v3) (and (=> ?v0 (fmember$ ?v1 ?v3)) (=> (not ?v0) (fmember$ ?v2 ?v3))))) :named a9))
(assert (! (forall ((?v0 A_tree$) (?v1 Bool) (?v2 A_tree_fset$) (?v3 A_tree_fset$)) (= (fmember$ ?v0 (ite ?v1 ?v2 ?v3)) (and (=> ?v1 (fmember$ ?v0 ?v2)) (=> (not ?v1) (fmember$ ?v0 ?v3))))) :named a10))
(assert (! (forall ((?v0 A_tree_fset$) (?v1 A_tree_fset$)) (=> (forall ((?v2 A_tree$)) (= (fmember$ ?v2 ?v0) (fmember$ ?v2 ?v1))) (= ?v0 ?v1))) :named a11))
(assert (! (forall ((?v0 A_tree_fset$) (?v1 A_tree_fset$) (?v2 A_tree$)) (=> (and (= ?v0 ?v1) (and (=> (and (fmember$ ?v2 ?v0) (fmember$ ?v2 ?v1)) false) (=> (and (not (fmember$ ?v2 ?v0)) (not (fmember$ ?v2 ?v1))) false))) false)) :named a12))
(assert (! (forall ((?v0 A_tree$) (?v1 A_tree$) (?v2 A_tree_fset$)) (=> (and (= ?v0 ?v1) (fmember$ ?v1 ?v2)) (fmember$ ?v0 ?v2))) :named a13))
(assert (! (forall ((?v0 A_tree$) (?v1 A_tree$) (?v2 A_tree_fset$)) (=> (= ?v0 ?v1) (= (fmember$ ?v0 ?v2) (fmember$ ?v1 ?v2)))) :named a14))
(assert (! (forall ((?v0 A_tree_fset$) (?v1 A_tree_fset$) (?v2 A_tree$)) (=> (= ?v0 ?v1) (= (fmember$ ?v2 ?v0) (fmember$ ?v2 ?v1)))) :named a15))
(assert (! (forall ((?v0 A_tree$)) (=> (=> (= ?v0 (node$ (root$ ?v0) (cont$ ?v0))) false) false)) :named a16))
(check-sat)
;(get-unsat-core)
