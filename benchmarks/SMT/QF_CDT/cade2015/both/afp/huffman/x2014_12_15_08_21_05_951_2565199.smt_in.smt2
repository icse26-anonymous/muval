; --full-saturate-quant --inst-when=full-last-call --inst-no-entail --term-db-mode=relevant --random-seed=1 --lang=smt2 --tlimit 613
;(set-option :produce-unsat-cores true)
(set-logic ALL_SUPPORTED)
(declare-sort A$ 0)
(declare-sort Nat$ 0)
(declare-sort A_set$ 0)
(declare-sort A_a_tree_fun$ 0)
(declare-datatypes () ((A_tree$ (leaf$ (select$ Nat$) (selecta$ A$)) (innerNode$ (selectb$ Nat$) (selectc$ A_tree$) (selectd$ A_tree$)))))
(declare-fun a$ () A$)
(declare-fun t$ () A_tree$)
(declare-fun depth$ (A_tree$ A$) Nat$)
(declare-fun member$ (A$ A_set$) Bool)
(declare-fun fun_app$ (A_a_tree_fun$ A$) A_tree$)
(declare-fun sibling$ (A_tree$ A$) A$)
(declare-fun alphabet$ (A_tree$) A_set$)
(declare-fun swapSyms$ (A_tree$ A$) A_a_tree_fun$)
(declare-fun consistent$ (A_tree$) Bool)
(declare-fun swapLeaves$ (A_tree$ Nat$ A$ Nat$) A_a_tree_fun$)
(declare-fun mergeSibling$ (A_tree$ A$) A_tree$)
(declare-fun swapFourSyms$ (A_tree$ A$ A$ A$ A$) A_tree$)
(assert (! (not (consistent$ (mergeSibling$ t$ a$))) :named a0))
(assert (! (consistent$ t$) :named a1))
(assert (! (forall ((?v0 A_tree$) (?v1 A$) (?v2 A$) (?v3 A$) (?v4 A$)) (=> (consistent$ ?v0) (consistent$ (swapFourSyms$ ?v0 ?v1 ?v2 ?v3 ?v4)))) :named a2))
(assert (! (forall ((?v0 A_tree$) (?v1 A$)) (! (=> (consistent$ ?v0) (= (fun_app$ (swapSyms$ ?v0 ?v1) ?v1) ?v0)) :pattern ((swapSyms$ ?v0 ?v1)))) :named a3))
(assert (! (forall ((?v0 A_tree$) (?v1 A$) (?v2 A$)) (=> (consistent$ ?v0) (consistent$ (fun_app$ (swapSyms$ ?v0 ?v1) ?v2)))) :named a4))
(assert (! (forall ((?v0 A_tree$) (?v1 Nat$) (?v2 A$) (?v3 Nat$) (?v4 A$)) (=> (consistent$ ?v0) (consistent$ (fun_app$ (swapLeaves$ ?v0 ?v1 ?v2 ?v3) ?v4)))) :named a5))
(assert (! (forall ((?v0 A_tree$) (?v1 A$)) (=> (consistent$ ?v0) (= (sibling$ ?v0 (sibling$ ?v0 ?v1)) ?v1))) :named a6))
(assert (! (forall ((?v0 A$) (?v1 A_tree$)) (! (=> (not (member$ ?v0 (alphabet$ ?v1))) (= (mergeSibling$ ?v1 ?v0) ?v1)) :pattern ((mergeSibling$ ?v1 ?v0)))) :named a7))
(assert (! (forall ((?v0 Nat$) (?v1 A$) (?v2 A$)) (! (= (mergeSibling$ (leaf$ ?v0 ?v1) ?v2) (leaf$ ?v0 ?v1)) :pattern ((mergeSibling$ (leaf$ ?v0 ?v1) ?v2)))) :named a8))
(assert (! (forall ((?v0 A_tree$) (?v1 A$) (?v2 A$)) (=> (and (consistent$ ?v0) (= (sibling$ ?v0 ?v1) ?v2)) (= (sibling$ ?v0 ?v2) ?v1))) :named a9))
(assert (! (forall ((?v0 Nat$) (?v1 A$)) (! (= (consistent$ (leaf$ ?v0 ?v1)) true) :pattern ((leaf$ ?v0 ?v1)))) :named a10))
(assert (! (forall ((?v0 Nat$) (?v1 Nat$) (?v2 A_tree$) (?v3 A_tree$) (?v4 A_tree$) (?v5 A$)) (! (= (mergeSibling$ (innerNode$ ?v0 (innerNode$ ?v1 ?v2 ?v3) ?v4) ?v5) (innerNode$ ?v0 (mergeSibling$ (innerNode$ ?v1 ?v2 ?v3) ?v5) (mergeSibling$ ?v4 ?v5))) :pattern ((mergeSibling$ (innerNode$ ?v0 (innerNode$ ?v1 ?v2 ?v3) ?v4) ?v5)))) :named a11))
(assert (! (forall ((?v0 Nat$) (?v1 A_tree$) (?v2 Nat$) (?v3 A_tree$) (?v4 A_tree$) (?v5 A$)) (! (= (mergeSibling$ (innerNode$ ?v0 ?v1 (innerNode$ ?v2 ?v3 ?v4)) ?v5) (innerNode$ ?v0 (mergeSibling$ ?v1 ?v5) (mergeSibling$ (innerNode$ ?v2 ?v3 ?v4) ?v5))) :pattern ((mergeSibling$ (innerNode$ ?v0 ?v1 (innerNode$ ?v2 ?v3 ?v4)) ?v5)))) :named a12))
(assert (! (forall ((?v0 A_tree$) (?v1 A$) (?v2 A$) (?v3 A$)) (=> (and (consistent$ ?v0) (and (not (= ?v1 ?v2)) (not (= ?v1 ?v3)))) (= (depth$ (fun_app$ (swapSyms$ ?v0 ?v2) ?v3) ?v1) (depth$ ?v0 ?v1)))) :named a13))
(assert (! (forall ((?v0 Nat$) (?v1 A_tree$) (?v2 A_tree$) (?v3 Nat$) (?v4 A_tree$) (?v5 A_tree$)) (= (= (innerNode$ ?v0 ?v1 ?v2) (innerNode$ ?v3 ?v4 ?v5)) (and (= ?v0 ?v3) (and (= ?v1 ?v4) (= ?v2 ?v5))))) :named a14))
(assert (! (forall ((?v0 Nat$) (?v1 A$) (?v2 Nat$) (?v3 A$)) (= (= (leaf$ ?v0 ?v1) (leaf$ ?v2 ?v3)) (and (= ?v0 ?v2) (= ?v1 ?v3)))) :named a15))
(assert (! (forall ((?v0 A$) (?v1 A_tree$)) (! (=> (not (member$ ?v0 (alphabet$ ?v1))) (= (sibling$ ?v1 ?v0) ?v0)) :pattern ((sibling$ ?v1 ?v0)))) :named a16))
(assert (! (forall ((?v0 A$) (?v1 A_tree$) (?v2 Nat$) (?v3 Nat$)) (! (=> (not (member$ ?v0 (alphabet$ ?v1))) (= (fun_app$ (swapLeaves$ ?v1 ?v2 ?v0 ?v3) ?v0) ?v1)) :pattern ((swapLeaves$ ?v1 ?v2 ?v0 ?v3)))) :named a17))
(assert (! (forall ((?v0 A$) (?v1 A_tree$) (?v2 A$)) (=> (and (member$ ?v0 (alphabet$ ?v1)) (member$ ?v2 (alphabet$ ?v1))) (= (alphabet$ (fun_app$ (swapSyms$ ?v1 ?v0) ?v2)) (alphabet$ ?v1)))) :named a18))
(check-sat)
;(get-unsat-core)
