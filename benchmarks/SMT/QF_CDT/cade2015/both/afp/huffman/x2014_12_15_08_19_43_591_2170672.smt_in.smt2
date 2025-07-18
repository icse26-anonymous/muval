; --full-saturate-quant --inst-when=full-last-call --inst-no-entail --term-db-mode=relevant --random-seed=1 --lang=smt2 --tlimit 680
;(set-option :produce-unsat-cores true)
(set-logic ALL_SUPPORTED)
(declare-sort A$ 0)
(declare-sort Nat$ 0)
(declare-sort A_set$ 0)
(declare-sort A_a_tree_fun$ 0)
(declare-datatypes () ((A_tree$ (leaf$ (select$ Nat$) (selecta$ A$)) (innerNode$ (selectb$ Nat$) (selectc$ A_tree$) (selectd$ A_tree$)))))
(declare-fun a$ () A$)
(declare-fun b$ () A$)
(declare-fun x1$ () Nat$)
(declare-fun x2$ () A$)
(declare-fun w_a$ () Nat$)
(declare-fun w_b$ () Nat$)
(declare-fun cost$ (A_tree$) Nat$)
(declare-fun freq$ (A_tree$ A$) Nat$)
(declare-fun plus$ (Nat$ Nat$) Nat$)
(declare-fun depth$ (A_tree$ A$) Nat$)
(declare-fun times$ (Nat$ Nat$) Nat$)
(declare-fun member$ (A$ A_set$) Bool)
(declare-fun fun_app$ (A_a_tree_fun$ A$) A_tree$)
(declare-fun alphabet$ (A_tree$) A_set$)
(declare-fun consistent$ (A_tree$) Bool)
(declare-fun swapLeaves$ (A_tree$ Nat$ A$ Nat$) A_a_tree_fun$)
(declare-fun uniteTrees$ (A_tree$ A_tree$) A_tree$)
(assert (! (not (ite (member$ a$ (alphabet$ (leaf$ x1$ x2$))) (ite (member$ b$ (alphabet$ (leaf$ x1$ x2$))) (= (plus$ (plus$ (cost$ (fun_app$ (swapLeaves$ (leaf$ x1$ x2$) w_a$ a$ w_b$) b$)) (times$ (freq$ (leaf$ x1$ x2$) a$) (depth$ (leaf$ x1$ x2$) a$))) (times$ (freq$ (leaf$ x1$ x2$) b$) (depth$ (leaf$ x1$ x2$) b$))) (plus$ (plus$ (cost$ (leaf$ x1$ x2$)) (times$ w_a$ (depth$ (leaf$ x1$ x2$) b$))) (times$ w_b$ (depth$ (leaf$ x1$ x2$) a$)))) (= (plus$ (cost$ (fun_app$ (swapLeaves$ (leaf$ x1$ x2$) w_a$ a$ w_b$) b$)) (times$ (freq$ (leaf$ x1$ x2$) a$) (depth$ (leaf$ x1$ x2$) a$))) (plus$ (cost$ (leaf$ x1$ x2$)) (times$ w_b$ (depth$ (leaf$ x1$ x2$) a$))))) (ite (member$ b$ (alphabet$ (leaf$ x1$ x2$))) (= (plus$ (cost$ (fun_app$ (swapLeaves$ (leaf$ x1$ x2$) w_a$ a$ w_b$) b$)) (times$ (freq$ (leaf$ x1$ x2$) b$) (depth$ (leaf$ x1$ x2$) b$))) (plus$ (cost$ (leaf$ x1$ x2$)) (times$ w_a$ (depth$ (leaf$ x1$ x2$) b$)))) (= (cost$ (fun_app$ (swapLeaves$ (leaf$ x1$ x2$) w_a$ a$ w_b$) b$)) (cost$ (leaf$ x1$ x2$)))))) :named a0))
(assert (! (not (= a$ b$)) :named a1))
(assert (! (forall ((?v0 Nat$) (?v1 A$) (?v2 Nat$) (?v3 A$)) (= (= (leaf$ ?v0 ?v1) (leaf$ ?v2 ?v3)) (and (= ?v0 ?v2) (= ?v1 ?v3)))) :named a2))
(assert (! (forall ((?v0 A$) (?v1 A_tree$) (?v2 Nat$) (?v3 Nat$)) (! (=> (not (member$ ?v0 (alphabet$ ?v1))) (= (fun_app$ (swapLeaves$ ?v1 ?v2 ?v0 ?v3) ?v0) ?v1)) :pattern ((swapLeaves$ ?v1 ?v2 ?v0 ?v3)))) :named a3))
(assert (! (consistent$ (leaf$ x1$ x2$)) :named a4))
(assert (! (forall ((?v0 Nat$) (?v1 A$) (?v2 Nat$) (?v3 A$) (?v4 Nat$) (?v5 A$)) (! (= (fun_app$ (swapLeaves$ (leaf$ ?v0 ?v1) ?v2 ?v3 ?v4) ?v5) (ite (= ?v1 ?v3) (leaf$ ?v4 ?v5) (ite (= ?v1 ?v5) (leaf$ ?v2 ?v3) (leaf$ ?v0 ?v1)))) :pattern ((fun_app$ (swapLeaves$ (leaf$ ?v0 ?v1) ?v2 ?v3 ?v4) ?v5)))) :named a5))
(assert (! (forall ((?v0 A_tree$)) (exists ((?v1 A$)) (member$ ?v1 (alphabet$ ?v0)))) :named a6))
(assert (! (forall ((?v0 Nat$) (?v1 Nat$) (?v2 Nat$)) (= (= (plus$ ?v0 ?v1) (plus$ ?v2 ?v1)) (= ?v0 ?v2))) :named a7))
(assert (! (forall ((?v0 Nat$) (?v1 Nat$) (?v2 Nat$)) (= (= (plus$ ?v0 ?v1) (plus$ ?v0 ?v2)) (= ?v1 ?v2))) :named a8))
(assert (! (forall ((?v0 A_tree$) (?v1 A_tree$) (?v2 A$)) (= (freq$ (uniteTrees$ ?v0 ?v1) ?v2) (plus$ (freq$ ?v0 ?v2) (freq$ ?v1 ?v2)))) :named a9))
(assert (! (forall ((?v0 Nat$) (?v1 Nat$) (?v2 Nat$) (?v3 Nat$)) (= (plus$ (times$ ?v0 ?v1) (plus$ (times$ ?v2 ?v1) ?v3)) (plus$ (times$ (plus$ ?v0 ?v2) ?v1) ?v3))) :named a10))
(assert (! (forall ((?v0 Nat$) (?v1 Nat$) (?v2 Nat$)) (= (times$ (plus$ ?v0 ?v1) ?v2) (plus$ (times$ ?v0 ?v2) (times$ ?v1 ?v2)))) :named a11))
(assert (! (forall ((?v0 Nat$) (?v1 Nat$) (?v2 Nat$)) (= (times$ ?v0 (plus$ ?v1 ?v2)) (plus$ (times$ ?v0 ?v1) (times$ ?v0 ?v2)))) :named a12))
(assert (! (forall ((?v0 Nat$) (?v1 Nat$) (?v2 Nat$) (?v3 Nat$)) (= (= (plus$ (times$ ?v0 ?v1) (times$ ?v2 ?v3)) (plus$ (times$ ?v0 ?v3) (times$ ?v2 ?v1))) (or (= ?v0 ?v2) (= ?v1 ?v3)))) :named a13))
(assert (! (forall ((?v0 Nat$) (?v1 Nat$) (?v2 Nat$) (?v3 Nat$)) (= (plus$ (times$ ?v0 ?v1) (plus$ (times$ ?v2 ?v1) ?v3)) (plus$ (times$ (plus$ ?v0 ?v2) ?v1) ?v3))) :named a14))
(assert (! (forall ((?v0 Nat$) (?v1 Nat$) (?v2 Nat$)) (= (times$ (plus$ ?v0 ?v1) ?v2) (plus$ (times$ ?v0 ?v2) (times$ ?v1 ?v2)))) :named a15))
(assert (! (forall ((?v0 Nat$) (?v1 Nat$) (?v2 Nat$)) (= (times$ (plus$ ?v0 ?v1) ?v2) (plus$ (times$ ?v0 ?v2) (times$ ?v1 ?v2)))) :named a16))
(assert (! (forall ((?v0 Nat$) (?v1 Nat$) (?v2 Nat$)) (= (plus$ (times$ ?v0 ?v1) (times$ ?v2 ?v1)) (times$ (plus$ ?v0 ?v2) ?v1))) :named a17))
(check-sat)
;(get-unsat-core)
