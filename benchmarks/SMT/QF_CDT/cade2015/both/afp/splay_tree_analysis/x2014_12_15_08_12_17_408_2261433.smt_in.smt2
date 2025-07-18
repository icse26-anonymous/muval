; --full-saturate-quant --inst-when=full-last-call --inst-no-entail --term-db-mode=relevant --random-seed=1 --lang=smt2 --tlimit 320
;(set-option :produce-unsat-cores true)
(set-logic ALL_SUPPORTED)
(declare-sort A$ 0)
(declare-sort A_tree_a_tree_fun$ 0)
(declare-datatypes () ((A_tree$ (leaf$) (node$ (left$ A_tree$) (val$ A$) (right$ A_tree$)))
  (A_op_s_t$ (splay$ (select$ A$)) (insert$ (selecta$ A$)) (delete$ (selectb$ A$)))))
(declare-fun a$ () A$)
(declare-fun f$ () A_op_s_t$)
(declare-fun s$ () A_tree$)
(declare-fun bst$ (A_tree$) Bool)
(declare-fun less$ (A$ A$) Bool)
(declare-fun splay$a (A$) A_tree_a_tree_fun$)
(declare-fun thesis$ () Bool)
(declare-fun fun_app$ (A_tree_a_tree_fun$ A_tree$) A_tree$)
(assert (! (not thesis$) :named a0))
(assert (! (forall ((?v0 A_tree$) (?v1 A$) (?v2 A_tree$)) (=> (= (fun_app$ (splay$a a$) s$) (node$ ?v0 ?v1 ?v2)) thesis$)) :named a1))
(assert (! (not (= s$ leaf$)) :named a2))
(assert (! (bst$ s$) :named a3))
(assert (! (forall ((?v0 A$) (?v1 A_tree$) (?v2 A_tree$)) (! (= (fun_app$ (splay$a ?v0) (node$ ?v1 ?v0 ?v2)) (node$ ?v1 ?v0 ?v2)) :pattern ((node$ ?v1 ?v0 ?v2)))) :named a4))
(assert (! (forall ((?v0 A_tree$) (?v1 A$) (?v2 A_tree$) (?v3 A_tree$) (?v4 A$) (?v5 A_tree$)) (= (= (node$ ?v0 ?v1 ?v2) (node$ ?v3 ?v4 ?v5)) (and (= ?v0 ?v3) (and (= ?v1 ?v4) (= ?v2 ?v5))))) :named a5))
(assert (! (= f$ (insert$ a$)) :named a6))
(assert (! (forall ((?v0 A$) (?v1 A_tree$)) (= (= (fun_app$ (splay$a ?v0) ?v1) leaf$) (= ?v1 leaf$))) :named a7))
(assert (! (forall ((?v0 A$)) (! (= (fun_app$ (splay$a ?v0) leaf$) leaf$) :pattern ((splay$a ?v0)))) :named a8))
(assert (! (forall ((?v0 A$) (?v1 A$) (?v2 A$) (?v3 A_tree$) (?v4 A_tree$) (?v5 A$) (?v6 A_tree$) (?v7 A_tree$) (?v8 A_tree$)) (=> (and (less$ ?v0 ?v1) (and (less$ ?v2 ?v0) (= (fun_app$ (splay$a ?v0) ?v3) (node$ ?v4 ?v5 ?v6)))) (= (fun_app$ (splay$a ?v0) (node$ (node$ ?v7 ?v2 ?v3) ?v1 ?v8)) (node$ (node$ ?v7 ?v2 ?v4) ?v5 (node$ ?v6 ?v1 ?v8))))) :named a9))
(assert (! (forall ((?v0 A$) (?v1 A$) (?v2 A$) (?v3 A_tree$) (?v4 A_tree$) (?v5 A$) (?v6 A_tree$) (?v7 A_tree$) (?v8 A_tree$)) (=> (and (less$ ?v0 ?v1) (and (less$ ?v0 ?v2) (= (fun_app$ (splay$a ?v0) ?v3) (node$ ?v4 ?v5 ?v6)))) (= (fun_app$ (splay$a ?v0) (node$ (node$ ?v3 ?v2 ?v7) ?v1 ?v8)) (node$ ?v4 ?v5 (node$ ?v6 ?v2 (node$ ?v7 ?v1 ?v8)))))) :named a10))
(assert (! (forall ((?v0 A$) (?v1 A$) (?v2 A$) (?v3 A_tree$) (?v4 A_tree$) (?v5 A$) (?v6 A_tree$) (?v7 A_tree$) (?v8 A_tree$)) (=> (and (less$ ?v0 ?v1) (and (less$ ?v2 ?v1) (= (fun_app$ (splay$a ?v1) ?v3) (node$ ?v4 ?v5 ?v6)))) (= (fun_app$ (splay$a ?v1) (node$ ?v7 ?v0 (node$ ?v8 ?v2 ?v3))) (node$ (node$ (node$ ?v7 ?v0 ?v8) ?v2 ?v4) ?v5 ?v6)))) :named a11))
(assert (! (forall ((?v0 A$) (?v1 A$) (?v2 A$) (?v3 A_tree$) (?v4 A_tree$) (?v5 A$) (?v6 A_tree$) (?v7 A_tree$) (?v8 A_tree$)) (=> (and (less$ ?v0 ?v1) (and (less$ ?v1 ?v2) (= (fun_app$ (splay$a ?v1) ?v3) (node$ ?v4 ?v5 ?v6)))) (= (fun_app$ (splay$a ?v1) (node$ ?v7 ?v0 (node$ ?v3 ?v2 ?v8))) (node$ (node$ ?v7 ?v0 ?v4) ?v5 (node$ ?v6 ?v2 ?v8))))) :named a12))
(assert (! (forall ((?v0 A$) (?v1 A$) (?v2 A_tree$) (?v3 A_tree$) (?v4 A_tree$)) (! (=> (less$ ?v0 ?v1) (= (fun_app$ (splay$a ?v0) (node$ (node$ ?v2 ?v0 ?v3) ?v1 ?v4)) (node$ ?v2 ?v0 (node$ ?v3 ?v1 ?v4)))) :pattern ((node$ (node$ ?v2 ?v0 ?v3) ?v1 ?v4)))) :named a13))
(assert (! (forall ((?v0 A$) (?v1 A$) (?v2 A_tree$) (?v3 A_tree$) (?v4 A_tree$)) (! (=> (less$ ?v0 ?v1) (= (fun_app$ (splay$a ?v1) (node$ ?v2 ?v0 (node$ ?v3 ?v1 ?v4))) (node$ (node$ ?v2 ?v0 ?v3) ?v1 ?v4))) :pattern ((node$ ?v2 ?v0 (node$ ?v3 ?v1 ?v4))))) :named a14))
(assert (! (forall ((?v0 A_tree$)) (= (not (= ?v0 leaf$)) (exists ((?v1 A_tree$) (?v2 A$) (?v3 A_tree$)) (= ?v0 (node$ ?v1 ?v2 ?v3))))) :named a15))
(assert (! (forall ((?v0 A$) (?v1 A$) (?v2 A_tree$)) (! (=> (less$ ?v0 ?v1) (= (fun_app$ (splay$a ?v0) (node$ leaf$ ?v1 ?v2)) (node$ leaf$ ?v1 ?v2))) :pattern ((fun_app$ (splay$a ?v0) (node$ leaf$ ?v1 ?v2))))) :named a16))
(assert (! (forall ((?v0 A$) (?v1 A$) (?v2 A_tree$)) (! (=> (less$ ?v0 ?v1) (= (fun_app$ (splay$a ?v1) (node$ ?v2 ?v0 leaf$)) (node$ ?v2 ?v0 leaf$))) :pattern ((fun_app$ (splay$a ?v1) (node$ ?v2 ?v0 leaf$))))) :named a17))
(assert (! (forall ((?v0 A$) (?v1 A$) (?v2 A$) (?v3 A_tree$) (?v4 A_tree$)) (! (=> (and (less$ ?v0 ?v1) (less$ ?v1 ?v2)) (= (fun_app$ (splay$a ?v1) (node$ ?v3 ?v0 (node$ leaf$ ?v2 ?v4))) (node$ (node$ ?v3 ?v0 leaf$) ?v2 ?v4))) :pattern ((fun_app$ (splay$a ?v1) (node$ ?v3 ?v0 (node$ leaf$ ?v2 ?v4)))))) :named a18))
(check-sat)
;(get-unsat-core)
