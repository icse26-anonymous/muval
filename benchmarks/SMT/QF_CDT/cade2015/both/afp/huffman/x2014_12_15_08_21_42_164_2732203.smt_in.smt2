; --full-saturate-quant --inst-when=full-last-call --inst-no-entail --term-db-mode=relevant --random-seed=1 --lang=smt2 --tlimit 702
;(set-option :produce-unsat-cores true)
(set-logic ALL_SUPPORTED)
(declare-sort A$ 0)
(declare-sort Nat$ 0)
(declare-sort A_set$ 0)
(declare-datatypes () ((A_tree$ (leaf$ (select$ Nat$) (selecta$ A$)) (innerNode$ (selectb$ Nat$) (selectc$ A_tree$) (selectd$ A_tree$)))))
(declare-fun c$ () A$)
(declare-fun t$ () A_tree$)
(declare-fun u$ () A_tree$)
(declare-fun less$ (Nat$ Nat$) Bool)
(declare-fun zero$ () Nat$)
(declare-fun depth$ (A_tree$ A$) Nat$)
(declare-fun height$ (A_tree$) Nat$)
(declare-fun member$ (A$ A_set$) Bool)
(declare-fun less_eq$ (Nat$ Nat$) Bool)
(declare-fun optimum$ (A_tree$) Bool)
(declare-fun sibling$ (A_tree$ A$) A$)
(declare-fun alphabet$ (A_tree$) A_set$)
(declare-fun swapSyms$ (A_tree$ A$ A$) A_tree$)
(declare-fun consistent$ (A_tree$) Bool)
(declare-fun swapLeaves$ (A_tree$ Nat$ A$ Nat$ A$) A_tree$)
(assert (! (not (= (depth$ u$ (sibling$ u$ c$)) (height$ u$))) :named a0))
(assert (! (consistent$ u$) :named a1))
(assert (! (= (depth$ u$ c$) (height$ u$)) :named a2))
(assert (! (consistent$ t$) :named a3))
(assert (! (optimum$ t$) :named a4))
(assert (! (not (= (sibling$ u$ c$) c$)) :named a5))
(assert (! (member$ c$ (alphabet$ u$)) :named a6))
(assert (! (forall ((?v0 A_tree$) (?v1 A$)) (=> (consistent$ ?v0) (= (depth$ ?v0 (sibling$ ?v0 ?v1)) (depth$ ?v0 ?v1)))) :named a7))
(assert (! (forall ((?v0 A_tree$) (?v1 A$)) (=> (consistent$ ?v0) (= (sibling$ ?v0 (sibling$ ?v0 ?v1)) ?v1))) :named a8))
(assert (! (member$ (sibling$ u$ c$) (alphabet$ u$)) :named a9))
(assert (! (=> (forall ((?v0 A$)) (=> (and (member$ ?v0 (alphabet$ u$)) (= (depth$ u$ ?v0) (height$ u$))) false)) false) :named a10))
(assert (! (exists ((?v0 A$)) (and (member$ ?v0 (alphabet$ u$)) (= (depth$ u$ ?v0) (height$ u$)))) :named a11))
(assert (! (forall ((?v0 A_tree$) (?v1 A$) (?v2 A$)) (=> (and (consistent$ ?v0) (= (sibling$ ?v0 ?v1) ?v2)) (= (sibling$ ?v0 ?v2) ?v1))) :named a12))
(assert (! (forall ((?v0 A_tree$) (?v1 A$)) (! (=> (= (height$ ?v0) zero$) (= (sibling$ ?v0 ?v1) ?v1)) :pattern ((sibling$ ?v0 ?v1)))) :named a13))
(assert (! (less$ zero$ (height$ u$)) :named a14))
(assert (! (forall ((?v0 A_tree$) (?v1 A$)) (less_eq$ (depth$ ?v0 ?v1) (height$ ?v0))) :named a15))
(assert (! (forall ((?v0 A_tree$) (?v1 Nat$) (?v2 A$) (?v3 Nat$) (?v4 A$)) (= (height$ (swapLeaves$ ?v0 ?v1 ?v2 ?v3 ?v4)) (height$ ?v0))) :named a16))
(assert (! (forall ((?v0 A_tree$) (?v1 A$) (?v2 A$) (?v3 A$)) (=> (and (consistent$ ?v0) (and (not (= ?v1 ?v2)) (not (= ?v1 ?v3)))) (= (depth$ (swapSyms$ ?v0 ?v2 ?v3) ?v1) (depth$ ?v0 ?v1)))) :named a17))
(check-sat)
;(get-unsat-core)
