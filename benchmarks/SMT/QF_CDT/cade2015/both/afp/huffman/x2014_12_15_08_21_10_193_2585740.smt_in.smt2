; --full-saturate-quant --inst-when=full-last-call --inst-no-entail --term-db-mode=relevant --random-seed=1 --lang=smt2 --tlimit 590
;(set-option :produce-unsat-cores true)
(set-logic ALL_SUPPORTED)
(declare-sort A$ 0)
(declare-sort Nat$ 0)
(declare-sort A_set$ 0)
(declare-sort A_a_tree_fun$ 0)
(declare-datatypes () ((A_tree$ (leaf$ (select$ Nat$) (selecta$ A$)) (innerNode$ (selectb$ Nat$) (selectc$ A_tree$) (selectd$ A_tree$)))
  (A_tree_list$ (nil$) (cons$ (hd$ A_tree$) (tl$ A_tree_list$)))))
(declare-fun a$ () A$)
(declare-fun b$ () A$)
(declare-fun t$ () A_tree$)
(declare-fun sup$ (A_set$ A_set$) A_set$)
(declare-fun w_a$ () Nat$)
(declare-fun w_b$ () Nat$)
(declare-fun finite$ (A_set$) Bool)
(declare-fun member$ (A$ A_set$) Bool)
(declare-fun fun_app$ (A_a_tree_fun$ A$) A_tree$)
(declare-fun sibling$ (A_tree$ A$) A$)
(declare-fun alphabet$ (A_tree$) A_set$)
(declare-fun swapSyms$ (A_tree$ A$ A$) A_tree$)
(declare-fun splitLeaf$ (A_tree$ Nat$ A$ Nat$ A$) A_tree$)
(declare-fun swapLeaves$ (A_tree$ Nat$ A$ Nat$) A_a_tree_fun$)
(declare-fun uniteTrees$ (A_tree$ A_tree$) A_tree$)
(declare-fun splitLeaf_F$ (A_tree_list$ Nat$ A$ Nat$ A$) A_tree_list$)
(declare-fun mergeSibling$ (A_tree$ A$) A_tree$)
(declare-fun swapFourSyms$ (A_tree$ A$ A$ A$ A$) A_tree$)
(assert (! (not (= (splitLeaf$ t$ w_a$ a$ w_b$ b$) t$)) :named a0))
(assert (! (not (member$ a$ (alphabet$ t$))) :named a1))
(assert (! (forall ((?v0 A_tree$)) (exists ((?v1 A$)) (member$ ?v1 (alphabet$ ?v0)))) :named a2))
(assert (! (forall ((?v0 A$) (?v1 A_tree$) (?v2 A$) (?v3 A$) (?v4 A$)) (=> (and (member$ ?v0 (alphabet$ ?v1)) (and (member$ ?v2 (alphabet$ ?v1)) (and (member$ ?v3 (alphabet$ ?v1)) (member$ ?v4 (alphabet$ ?v1))))) (= (alphabet$ (swapFourSyms$ ?v1 ?v0 ?v2 ?v3 ?v4)) (alphabet$ ?v1)))) :named a3))
(assert (! (forall ((?v0 A$) (?v1 A_tree$) (?v2 A$)) (=> (and (member$ ?v0 (alphabet$ ?v1)) (member$ ?v2 (alphabet$ ?v1))) (= (alphabet$ (swapSyms$ ?v1 ?v0 ?v2)) (alphabet$ ?v1)))) :named a4))
(assert (! (forall ((?v0 A$) (?v1 A_tree$) (?v2 Nat$) (?v3 Nat$)) (! (=> (not (member$ ?v0 (alphabet$ ?v1))) (= (fun_app$ (swapLeaves$ ?v1 ?v2 ?v0 ?v3) ?v0) ?v1)) :pattern ((swapLeaves$ ?v1 ?v2 ?v0 ?v3)))) :named a5))
(assert (! (forall ((?v0 A$) (?v1 A_tree$)) (! (=> (not (member$ ?v0 (alphabet$ ?v1))) (= (mergeSibling$ ?v1 ?v0) ?v1)) :pattern ((mergeSibling$ ?v1 ?v0)))) :named a6))
(assert (! (forall ((?v0 A$) (?v1 A_tree$)) (! (=> (not (member$ ?v0 (alphabet$ ?v1))) (= (sibling$ ?v1 ?v0) ?v0)) :pattern ((sibling$ ?v1 ?v0)))) :named a7))
(assert (! (forall ((?v0 Nat$) (?v1 A_tree$) (?v2 A_tree$) (?v3 Nat$) (?v4 A$) (?v5 Nat$) (?v6 A$)) (! (= (splitLeaf$ (innerNode$ ?v0 ?v1 ?v2) ?v3 ?v4 ?v5 ?v6) (innerNode$ ?v0 (splitLeaf$ ?v1 ?v3 ?v4 ?v5 ?v6) (splitLeaf$ ?v2 ?v3 ?v4 ?v5 ?v6))) :pattern ((splitLeaf$ (innerNode$ ?v0 ?v1 ?v2) ?v3 ?v4 ?v5 ?v6)))) :named a8))
(assert (! (forall ((?v0 A$) (?v1 A_tree$)) (=> (member$ ?v0 (alphabet$ ?v1)) (member$ (sibling$ ?v1 ?v0) (alphabet$ ?v1)))) :named a9))
(assert (! (forall ((?v0 A_tree$) (?v1 A$)) (=> (not (= (sibling$ ?v0 ?v1) ?v1)) (member$ (sibling$ ?v0 ?v1) (alphabet$ ?v0)))) :named a10))
(assert (! (forall ((?v0 A_tree$) (?v1 A_tree_list$) (?v2 Nat$) (?v3 A$) (?v4 Nat$) (?v5 A$)) (! (= (splitLeaf_F$ (cons$ ?v0 ?v1) ?v2 ?v3 ?v4 ?v5) (cons$ (splitLeaf$ ?v0 ?v2 ?v3 ?v4 ?v5) (splitLeaf_F$ ?v1 ?v2 ?v3 ?v4 ?v5))) :pattern ((splitLeaf_F$ (cons$ ?v0 ?v1) ?v2 ?v3 ?v4 ?v5)))) :named a11))
(assert (! (forall ((?v0 A_tree$)) (finite$ (alphabet$ ?v0))) :named a12))
(assert (! (forall ((?v0 A_tree$) (?v1 A_tree$)) (= (alphabet$ (uniteTrees$ ?v0 ?v1)) (sup$ (alphabet$ ?v0) (alphabet$ ?v1)))) :named a13))
(assert (! (forall ((?v0 Nat$) (?v1 A$) (?v2 Nat$) (?v3 A$) (?v4 Nat$) (?v5 A$)) (! (= (splitLeaf$ (leaf$ ?v0 ?v1) ?v2 ?v3 ?v4 ?v5) (ite (= ?v1 ?v3) (innerNode$ ?v0 (leaf$ ?v2 ?v3) (leaf$ ?v4 ?v5)) (leaf$ ?v0 ?v1))) :pattern ((splitLeaf$ (leaf$ ?v0 ?v1) ?v2 ?v3 ?v4 ?v5)))) :named a14))
(assert (! (forall ((?v0 Nat$) (?v1 A_tree$) (?v2 A_tree$) (?v3 Nat$) (?v4 A_tree$) (?v5 A_tree$)) (= (= (innerNode$ ?v0 ?v1 ?v2) (innerNode$ ?v3 ?v4 ?v5)) (and (= ?v0 ?v3) (and (= ?v1 ?v4) (= ?v2 ?v5))))) :named a15))
(assert (! (forall ((?v0 Nat$) (?v1 A$) (?v2 Nat$) (?v3 A$)) (= (= (leaf$ ?v0 ?v1) (leaf$ ?v2 ?v3)) (and (= ?v0 ?v2) (= ?v1 ?v3)))) :named a16))
(assert (! (forall ((?v0 A_tree$) (?v1 A$) (?v2 A$) (?v3 A$) (?v4 A$)) (! (= (swapFourSyms$ ?v0 ?v1 ?v2 ?v3 ?v4) (ite (= ?v1 ?v4) (swapSyms$ ?v0 ?v2 ?v3) (ite (= ?v2 ?v3) (swapSyms$ ?v0 ?v1 ?v4) (swapSyms$ (swapSyms$ ?v0 ?v1 ?v3) ?v2 ?v4)))) :pattern ((swapFourSyms$ ?v0 ?v1 ?v2 ?v3 ?v4)))) :named a17))
(assert (! (forall ((?v0 Nat$) (?v1 A$) (?v2 Nat$) (?v3 A$) (?v4 Nat$) (?v5 A$)) (! (= (fun_app$ (swapLeaves$ (leaf$ ?v0 ?v1) ?v2 ?v3 ?v4) ?v5) (ite (= ?v1 ?v3) (leaf$ ?v4 ?v5) (ite (= ?v1 ?v5) (leaf$ ?v2 ?v3) (leaf$ ?v0 ?v1)))) :pattern ((fun_app$ (swapLeaves$ (leaf$ ?v0 ?v1) ?v2 ?v3 ?v4) ?v5)))) :named a18))
(check-sat)
;(get-unsat-core)
