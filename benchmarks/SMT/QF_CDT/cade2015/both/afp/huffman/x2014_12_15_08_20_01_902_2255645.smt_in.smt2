; --full-saturate-quant --inst-when=full-last-call --inst-no-entail --term-db-mode=relevant --random-seed=1 --lang=smt2 --tlimit 639
;(set-option :produce-unsat-cores true)
(set-logic ALL_SUPPORTED)
(declare-sort A$ 0)
(declare-sort Nat$ 0)
(declare-sort A_set$ 0)
(declare-sort A_a_tree_fun$ 0)
(declare-datatypes () ((A_tree$ (leaf$ (select$ Nat$) (selecta$ A$)) (innerNode$ (selectb$ Nat$) (selectc$ A_tree$) (selectd$ A_tree$)))))
(declare-fun a$ () A$)
(declare-fun b$ () A$)
(declare-fun w$ () Nat$)
(declare-fun sup$ (A_set$ A_set$) A_set$)
(declare-fun t_1$ () A_tree$)
(declare-fun t_2$ () A_tree$)
(declare-fun finite$ (A_set$) Bool)
(declare-fun member$ (A$ A_set$) Bool)
(declare-fun fun_app$ (A_a_tree_fun$ A$) A_tree$)
(declare-fun sibling$ (A_tree$ A$) A$)
(declare-fun alphabet$ (A_tree$) A_set$)
(declare-fun consistent$ (A_tree$) Bool)
(declare-fun swapLeaves$ (A_tree$ Nat$ A$ Nat$) A_a_tree_fun$)
(assert (! (not (not (member$ b$ (alphabet$ t_2$)))) :named a0))
(assert (! (consistent$ (innerNode$ w$ t_1$ t_2$)) :named a1))
(assert (! (member$ b$ (alphabet$ t_1$)) :named a2))
(assert (! (forall ((?v0 A_tree$)) (exists ((?v1 A$)) (member$ ?v1 (alphabet$ ?v0)))) :named a3))
(assert (! (not (member$ a$ (alphabet$ t_2$))) :named a4))
(assert (! (not (= a$ b$)) :named a5))
(assert (! (forall ((?v0 Nat$) (?v1 A_tree$) (?v2 A_tree$) (?v3 Nat$) (?v4 A_tree$) (?v5 A_tree$)) (= (= (innerNode$ ?v0 ?v1 ?v2) (innerNode$ ?v3 ?v4 ?v5)) (and (= ?v0 ?v3) (and (= ?v1 ?v4) (= ?v2 ?v5))))) :named a6))
(assert (! (not (member$ a$ (alphabet$ t_1$))) :named a7))
(assert (! (forall ((?v0 A$) (?v1 A_tree$) (?v2 Nat$) (?v3 Nat$)) (! (=> (not (member$ ?v0 (alphabet$ ?v1))) (= (fun_app$ (swapLeaves$ ?v1 ?v2 ?v0 ?v3) ?v0) ?v1)) :pattern ((swapLeaves$ ?v1 ?v2 ?v0 ?v3)))) :named a8))
(assert (! (forall ((?v0 A$) (?v1 A_tree$)) (! (=> (not (member$ ?v0 (alphabet$ ?v1))) (= (sibling$ ?v1 ?v0) ?v0)) :pattern ((sibling$ ?v1 ?v0)))) :named a9))
(assert (! (forall ((?v0 A$) (?v1 A_tree$)) (=> (member$ ?v0 (alphabet$ ?v1)) (member$ (sibling$ ?v1 ?v0) (alphabet$ ?v1)))) :named a10))
(assert (! (forall ((?v0 A_tree$) (?v1 A$)) (=> (not (= (sibling$ ?v0 ?v1) ?v1)) (member$ (sibling$ ?v0 ?v1) (alphabet$ ?v0)))) :named a11))
(assert (! (forall ((?v0 A_tree$)) (finite$ (alphabet$ ?v0))) :named a12))
(assert (! (forall ((?v0 Nat$) (?v1 Nat$) (?v2 A_tree$) (?v3 A_tree$) (?v4 A_tree$) (?v5 A$)) (! (= (sibling$ (innerNode$ ?v0 (innerNode$ ?v1 ?v2 ?v3) ?v4) ?v5) (ite (member$ ?v5 (alphabet$ (innerNode$ ?v1 ?v2 ?v3))) (sibling$ (innerNode$ ?v1 ?v2 ?v3) ?v5) (ite (member$ ?v5 (alphabet$ ?v4)) (sibling$ ?v4 ?v5) ?v5))) :pattern ((sibling$ (innerNode$ ?v0 (innerNode$ ?v1 ?v2 ?v3) ?v4) ?v5)))) :named a13))
(assert (! (forall ((?v0 Nat$) (?v1 A_tree$) (?v2 Nat$) (?v3 A_tree$) (?v4 A_tree$) (?v5 A$)) (! (= (sibling$ (innerNode$ ?v0 ?v1 (innerNode$ ?v2 ?v3 ?v4)) ?v5) (ite (member$ ?v5 (alphabet$ ?v1)) (sibling$ ?v1 ?v5) (ite (member$ ?v5 (alphabet$ (innerNode$ ?v2 ?v3 ?v4))) (sibling$ (innerNode$ ?v2 ?v3 ?v4) ?v5) ?v5))) :pattern ((sibling$ (innerNode$ ?v0 ?v1 (innerNode$ ?v2 ?v3 ?v4)) ?v5)))) :named a14))
(assert (! (forall ((?v0 Nat$) (?v1 A_tree$) (?v2 A_tree$)) (! (= (alphabet$ (innerNode$ ?v0 ?v1 ?v2)) (sup$ (alphabet$ ?v1) (alphabet$ ?v2))) :pattern ((innerNode$ ?v0 ?v1 ?v2)))) :named a15))
(assert (! (forall ((?v0 A_tree$) (?v1 A$)) (=> (consistent$ ?v0) (= (sibling$ ?v0 (sibling$ ?v0 ?v1)) ?v1))) :named a16))
(assert (! (forall ((?v0 Nat$) (?v1 A_tree$) (?v2 A_tree$) (?v3 Nat$) (?v4 A$) (?v5 Nat$) (?v6 A$)) (! (= (fun_app$ (swapLeaves$ (innerNode$ ?v0 ?v1 ?v2) ?v3 ?v4 ?v5) ?v6) (innerNode$ ?v0 (fun_app$ (swapLeaves$ ?v1 ?v3 ?v4 ?v5) ?v6) (fun_app$ (swapLeaves$ ?v2 ?v3 ?v4 ?v5) ?v6))) :pattern ((fun_app$ (swapLeaves$ (innerNode$ ?v0 ?v1 ?v2) ?v3 ?v4 ?v5) ?v6)))) :named a17))
(check-sat)
;(get-unsat-core)
