; --full-saturate-quant --inst-when=full-last-call --inst-no-entail --term-db-mode=relevant --random-seed=1 --lang=smt2 --tlimit 361
;(set-option :produce-unsat-cores true)
(set-logic ALL_SUPPORTED)
(declare-sort Node$ 0)
(declare-sort Node_set$ 0)
(declare-sort Node_bool_fun$ 0)
(declare-sort Node_llist_set$ 0)
(declare-sort Node_node_bool_fun_fun$ 0)
(declare-sort Node_set_node_bool_fun_fun$ 0)
(declare-sort Node_bool_fun_node_bool_fun_fun$ 0)
(declare-sort Node_node_set_node_bool_fun_fun_fun$ 0)
(declare-sort Node_node_set_prod_node_bool_fun_fun$ 0)
(declare-codatatypes () ((Node_llist$ (lNil$) (lCons$ (lhd$ Node$) (ltl$ Node_llist$)))))
(declare-datatypes () ((Node_node_set_prod$ (pair$ (fst$ Node$) (snd$ Node_set$)))))
(declare-fun f$ (Node_node_set_prod$) Node_llist$)
(declare-fun na$ () Node$)
(declare-fun uu$ () Node_node_set_node_bool_fun_fun_fun$)
(declare-fun xs$ () Node_llist$)
(declare-fun eps$ (Node_bool_fun$) Node$)
(declare-fun nsa$ () Node_set$)
(declare-fun top$ () Node_set$)
(declare-fun uua$ (Node_bool_fun$) Node_bool_fun_node_bool_fun_fun$)
(declare-fun lset$ (Node_llist$) Node_set$)
(declare-fun graph$ () Node_node_bool_fun_fun$)
(declare-fun paths$ (Node_node_bool_fun_fun$) Node_llist_set$)
(declare-fun finite$ (Node_set$) Bool)
(declare-fun insert$ (Node$ Node_set$) Node_set$)
(declare-fun member$ (Node$ Node_set$) Bool)
(declare-fun uminus$ (Node_set$) Node_set$)
(declare-fun collect$ (Node_bool_fun$) Node_set$)
(declare-fun fun_app$ (Node_bool_fun$ Node$) Bool)
(declare-fun member$a (Node_llist$ Node_llist_set$) Bool)
(declare-fun fun_app$a (Node_set_node_bool_fun_fun$ Node_set$) Node_bool_fun$)
(declare-fun fun_app$b (Node_node_set_node_bool_fun_fun_fun$ Node$) Node_set_node_bool_fun_fun$)
(declare-fun fun_app$c (Node_node_bool_fun_fun$ Node$) Node_bool_fun$)
(declare-fun fun_app$d (Node_bool_fun_node_bool_fun_fun$ Node_bool_fun$) Node_bool_fun$)
(declare-fun fun_app$e (Node_node_set_prod_node_bool_fun_fun$ Node_node_set_prod$) Node_bool_fun$)
(declare-fun case_prod$ (Node_node_set_node_bool_fun_fun_fun$) Node_node_set_prod_node_bool_fun_fun$)
(declare-fun connected$ (Node_node_bool_fun_fun$) Bool)
(declare-fun reachable_via$ (Node_node_bool_fun_fun$ Node_set$ Node$) Node_set$)
(assert (! (forall ((?v0 Node$) (?v1 Node_set$) (?v2 Node$)) (! (= (fun_app$ (fun_app$a (fun_app$b uu$ ?v0) ?v1) ?v2) (and (fun_app$ (fun_app$c graph$ ?v0) ?v2) (and (not (finite$ (reachable_via$ graph$ (uminus$ (insert$ ?v0 (insert$ ?v2 ?v1))) ?v2))) (not (member$ ?v2 (insert$ ?v0 ?v1)))))) :pattern ((fun_app$ (fun_app$a (fun_app$b uu$ ?v0) ?v1) ?v2)))) :named a0))
(assert (! (forall ((?v0 Node_bool_fun$) (?v1 Node_bool_fun$) (?v2 Node$)) (! (= (fun_app$ (fun_app$d (uua$ ?v0) ?v1) ?v2) (or (fun_app$ ?v0 ?v2) (fun_app$ ?v1 ?v2))) :pattern ((fun_app$ (fun_app$d (uua$ ?v0) ?v1) ?v2)))) :named a1))
(assert (! (not (exists ((?v0 Node$) (?v1 Node$) (?v2 Node_llist$)) (and (= xs$ (lCons$ ?v0 (lCons$ ?v1 ?v2))) (and (fun_app$ (fun_app$c graph$ ?v0) ?v1) (or (exists ((?v3 Node$) (?v4 Node_set$)) (and (= (lCons$ ?v1 ?v2) (f$ (pair$ ?v3 ?v4))) (and (finite$ ?v4) (not (finite$ (reachable_via$ graph$ (uminus$ (insert$ ?v3 ?v4)) ?v3)))))) (member$a (lCons$ ?v1 ?v2) (paths$ graph$))))))) :named a2))
(assert (! (finite$ nsa$) :named a3))
(assert (! (connected$ graph$) :named a4))
(assert (! (forall ((?v0 Node$)) (finite$ (collect$ (fun_app$c graph$ ?v0)))) :named a5))
(assert (! (= xs$ (f$ (pair$ na$ nsa$))) :named a6))
(assert (! (not (finite$ top$)) :named a7))
(assert (! (not (finite$ (reachable_via$ graph$ (uminus$ (insert$ na$ nsa$)) na$))) :named a8))
(assert (! (fun_app$ (fun_app$c graph$ na$) (eps$ (fun_app$e (case_prod$ uu$) (pair$ na$ nsa$)))) :named a9))
(assert (! (exists ((?v0 Node$) (?v1 Node_set$)) (and (= xs$ (f$ (pair$ ?v0 ?v1))) (and (finite$ ?v1) (not (finite$ (reachable_via$ graph$ (uminus$ (insert$ ?v0 ?v1)) ?v0)))))) :named a10))
(assert (! (=> (forall ((?v0 Node$) (?v1 Node_set$)) (=> (and (= xs$ (f$ (pair$ ?v0 ?v1))) (and (finite$ ?v1) (not (finite$ (reachable_via$ graph$ (uminus$ (insert$ ?v0 ?v1)) ?v0))))) false)) false) :named a11))
(assert (! (forall ((?v0 Node$) (?v1 Node_set$)) (=> (not (finite$ (reachable_via$ graph$ (uminus$ (insert$ ?v0 ?v1)) ?v0))) (exists ((?v2 Node$)) (fun_app$ (fun_app$e (case_prod$ uu$) (pair$ ?v0 ?v1)) ?v2)))) :named a12))
(assert (! (forall ((?v0 Node$) (?v1 Node_llist$) (?v2 Node_node_bool_fun_fun$)) (=> (member$a (lCons$ ?v0 ?v1) (paths$ ?v2)) (member$a ?v1 (paths$ ?v2)))) :named a13))
(assert (! (forall ((?v0 Node_node_bool_fun_fun$) (?v1 Node$) (?v2 Node$) (?v3 Node_llist$)) (=> (and (fun_app$ (fun_app$c ?v0 ?v1) ?v2) (member$a (lCons$ ?v2 ?v3) (paths$ ?v0))) (member$a (lCons$ ?v1 (lCons$ ?v2 ?v3)) (paths$ ?v0)))) :named a14))
(assert (! (exists ((?v0 Node$)) (fun_app$ (fun_app$e (case_prod$ uu$) (pair$ na$ nsa$)) ?v0)) :named a15))
(assert (! (fun_app$ (fun_app$e (case_prod$ uu$) (pair$ na$ nsa$)) (eps$ (fun_app$e (case_prod$ uu$) (pair$ na$ nsa$)))) :named a16))
(assert (! (forall ((?v0 Node$) (?v1 Node$) (?v2 Node_set$)) (=> (and (member$ ?v0 (lset$ (f$ (pair$ ?v1 ?v2)))) (and (not (member$ ?v1 ?v2)) (and (finite$ ?v2) (not (finite$ (reachable_via$ graph$ (uminus$ (insert$ ?v1 ?v2)) ?v1)))))) (not (member$ ?v0 ?v2)))) :named a17))
(assert (! (forall ((?v0 Node$) (?v1 Node_set$)) (= (finite$ (insert$ ?v0 ?v1)) (finite$ ?v1))) :named a18))
(assert (! (forall ((?v0 Node_bool_fun$) (?v1 Node_bool_fun$)) (= (finite$ (collect$ (fun_app$d (uua$ ?v0) ?v1))) (and (finite$ (collect$ ?v0)) (finite$ (collect$ ?v1))))) :named a19))
(check-sat)
;(get-unsat-core)
