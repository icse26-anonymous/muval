; --full-saturate-quant --inst-when=full-last-call --inst-no-entail --term-db-mode=relevant --random-seed=1 --lang=smt2 --tlimit 296
;(set-option :produce-unsat-cores true)
(set-logic ALL_SUPPORTED)
(declare-sort A$ 0)
(declare-sort A_set$ 0)
(declare-sort A_tree_set$ 0)
(declare-datatypes () ((A_tree$ (leaf$) (node$ (left$ A_tree$) (val$ A$) (right$ A_tree$)))))
(declare-fun b$ () A$)
(declare-fun c$ () A$)
(declare-fun l$ () A_tree$)
(declare-fun r$ () A_tree$)
(declare-fun aa$ () A$)
(declare-fun la$ () A_tree$)
(declare-fun ra$ () A_tree$)
(declare-fun rl$ () A_tree$)
(declare-fun rr$ () A_tree$)
(declare-fun bst$ (A_tree$) Bool)
(declare-fun less$ (A$ A$) Bool)
(declare-fun splay$ (A$ A_tree$) A_tree$)
(declare-fun member$ (A$ A_set$) Bool)
(declare-fun thesis$ () Bool)
(declare-fun member$a (A_tree$ A_tree_set$) Bool)
(declare-fun set_tree$ (A_tree$) A_set$)
(declare-fun subtrees$ (A_tree$) A_tree_set$)
(assert (! (not thesis$) :named a0))
(assert (! (forall ((?v0 A_tree$) (?v1 A$) (?v2 A_tree$)) (=> (= (splay$ aa$ rr$) (node$ ?v0 ?v1 ?v2)) thesis$)) :named a1))
(assert (! (bst$ (node$ l$ c$ r$)) :named a2))
(assert (! (not (= aa$ c$)) :named a3))
(assert (! (member$ aa$ (set_tree$ rr$)) :named a4))
(assert (! (=> (forall ((?v0 A_tree$) (?v1 A$) (?v2 A_tree$)) (=> (= r$ (node$ ?v0 ?v1 ?v2)) false)) false) :named a5))
(assert (! (not (= aa$ b$)) :named a6))
(assert (! (member$a (node$ la$ aa$ ra$) (subtrees$ (node$ l$ c$ r$))) :named a7))
(assert (! (less$ c$ aa$) :named a8))
(assert (! (forall ((?v0 A$) (?v1 A_tree$) (?v2 A_tree$)) (! (= (splay$ ?v0 (node$ ?v1 ?v0 ?v2)) (node$ ?v1 ?v0 ?v2)) :pattern ((node$ ?v1 ?v0 ?v2)))) :named a9))
(assert (! (and (not (member$ aa$ (set_tree$ rl$))) (not (member$ aa$ (set_tree$ l$)))) :named a10))
(assert (! (forall ((?v0 A_tree$) (?v1 A$) (?v2 A_tree$) (?v3 A_tree$) (?v4 A$) (?v5 A_tree$)) (= (= (node$ ?v0 ?v1 ?v2) (node$ ?v3 ?v4 ?v5)) (and (= ?v0 ?v3) (and (= ?v1 ?v4) (= ?v2 ?v5))))) :named a11))
(assert (! (= r$ (node$ rl$ b$ rr$)) :named a12))
(assert (! (less$ b$ aa$) :named a13))
(assert (! (or (less$ aa$ c$) (less$ c$ aa$)) :named a14))
(assert (! (forall ((?v0 A_tree$) (?v1 A$) (?v2 A_tree$)) (=> (and (bst$ ?v0) (= (splay$ ?v1 ?v0) ?v2)) (= (member$ ?v1 (set_tree$ ?v0)) (exists ((?v3 A_tree$) (?v4 A_tree$)) (= ?v2 (node$ ?v3 ?v1 ?v4)))))) :named a15))
(assert (! (forall ((?v0 A_tree$) (?v1 A$)) (=> (bst$ ?v0) (bst$ (splay$ ?v1 ?v0)))) :named a16))
(assert (! (forall ((?v0 A$) (?v1 A_tree$)) (= (set_tree$ (splay$ ?v0 ?v1)) (set_tree$ ?v1))) :named a17))
(assert (! (forall ((?v0 A$) (?v1 A$) (?v2 A$) (?v3 A_tree$) (?v4 A_tree$) (?v5 A$) (?v6 A_tree$) (?v7 A_tree$) (?v8 A_tree$)) (=> (and (less$ ?v0 ?v1) (and (less$ ?v2 ?v0) (= (splay$ ?v0 ?v3) (node$ ?v4 ?v5 ?v6)))) (= (splay$ ?v0 (node$ (node$ ?v7 ?v2 ?v3) ?v1 ?v8)) (node$ (node$ ?v7 ?v2 ?v4) ?v5 (node$ ?v6 ?v1 ?v8))))) :named a18))
(check-sat)
;(get-unsat-core)
