; --full-saturate-quant --inst-when=full-last-call --inst-no-entail --term-db-mode=relevant --random-seed=1 --lang=smt2 --tlimit 284
;(set-option :produce-unsat-cores true)
(set-logic ALL_SUPPORTED)
(declare-sort Node$ 0)
(declare-sort Node_set$ 0)
(declare-sort Node_bool_fun$ 0)
(declare-sort Node_node_bool_fun_fun$ 0)
(declare-sort Node_set_node_bool_fun_fun$ 0)
(declare-sort Node_node_set_node_bool_fun_fun_fun$ 0)
(declare-codatatypes () ((Node_llist$ (lNil$) (lCons$ (lhd$ Node$) (ltl$ Node_llist$)))))
(declare-datatypes () ((Node_node_set_prod$ (pair$ (fst$ Node$) (snd$ Node_set$)))))
(declare-fun f$ (Node_node_set_prod$) Node_llist$)
(declare-fun na$ () Node$)
(declare-fun uu$ () Node_node_set_node_bool_fun_fun_fun$)
(declare-fun eps$ (Node_bool_fun$) Node$)
(declare-fun nsa$ () Node_set$)
(declare-fun top$ () Node_set$)
(declare-fun lset$ (Node_llist$) Node_set$)
(declare-fun graph$ () Node_node_bool_fun_fun$)
(declare-fun lnull$ (Node_llist$) Bool)
(declare-fun finite$ (Node_set$) Bool)
(declare-fun insert$ (Node$ Node_set$) Node_set$)
(declare-fun member$ (Node$ Node_set$) Bool)
(declare-fun uminus$ (Node_set$) Node_set$)
(declare-fun fun_app$ (Node_bool_fun$ Node$) Bool)
(declare-fun fun_app$a (Node_set_node_bool_fun_fun$ Node_set$) Node_bool_fun$)
(declare-fun fun_app$b (Node_node_set_node_bool_fun_fun_fun$ Node$) Node_set_node_bool_fun_fun$)
(declare-fun fun_app$c (Node_node_bool_fun_fun$ Node$) Node_bool_fun$)
(declare-fun case_prod$ (Node_node_set_node_bool_fun_fun_fun$ Node_node_set_prod$) Node_bool_fun$)
(declare-fun connected$ (Node_node_bool_fun_fun$) Bool)
(declare-fun ldistinct$ (Node_llist$) Bool)
(declare-fun reachable_via$ (Node_node_bool_fun_fun$ Node_set$ Node$) Node_set$)
(assert (! (forall ((?v0 Node$) (?v1 Node_set$) (?v2 Node$)) (! (= (fun_app$ (fun_app$a (fun_app$b uu$ ?v0) ?v1) ?v2) (and (fun_app$ (fun_app$c graph$ ?v0) ?v2) (and (not (finite$ (reachable_via$ graph$ (uminus$ (insert$ ?v0 (insert$ ?v2 ?v1))) ?v2))) (not (member$ ?v2 (insert$ ?v0 ?v1)))))) :pattern ((fun_app$ (fun_app$a (fun_app$b uu$ ?v0) ?v1) ?v2)))) :named a0))
(assert (! (not (and (not (member$ (lhd$ (f$ (pair$ na$ nsa$))) (lset$ (ltl$ (f$ (pair$ na$ nsa$)))))) (or (exists ((?v0 Node$) (?v1 Node_set$)) (and (= (ltl$ (f$ (pair$ na$ nsa$))) (f$ (pair$ ?v0 ?v1))) (and (not (finite$ (reachable_via$ graph$ (uminus$ (insert$ ?v0 ?v1)) ?v0))) (finite$ ?v1)))) (ldistinct$ (ltl$ (f$ (pair$ na$ nsa$))))))) :named a1))
(assert (! (finite$ nsa$) :named a2))
(assert (! (connected$ graph$) :named a3))
(assert (! (not (finite$ top$)) :named a4))
(assert (! (and (not (finite$ (reachable_via$ graph$ (uminus$ (insert$ na$ nsa$)) na$))) (finite$ nsa$)) :named a5))
(assert (! (not (finite$ (reachable_via$ graph$ (uminus$ (insert$ na$ nsa$)) na$))) :named a6))
(assert (! (=> (=> (and (finite$ nsa$) (not (finite$ (reachable_via$ graph$ (uminus$ (insert$ na$ nsa$)) na$)))) false) false) :named a7))
(assert (! (forall ((?v0 Node$) (?v1 Node$) (?v2 Node_set$)) (=> (and (member$ ?v0 (lset$ (f$ (pair$ ?v1 ?v2)))) (and (not (member$ ?v1 ?v2)) (and (finite$ ?v2) (not (finite$ (reachable_via$ graph$ (uminus$ (insert$ ?v1 ?v2)) ?v1)))))) (not (member$ ?v0 ?v2)))) :named a8))
(assert (! (forall ((?v0 Node$) (?v1 Node_set$)) (= (lhd$ (f$ (pair$ ?v0 ?v1))) ?v0)) :named a9))
(assert (! (not (lnull$ (f$ (pair$ na$ nsa$)))) :named a10))
(assert (! (forall ((?v0 Node$) (?v1 Node_set$)) (= (finite$ (insert$ ?v0 ?v1)) (finite$ ?v1))) :named a11))
(assert (! (not (member$ na$ (lset$ (f$ (pair$ (eps$ (case_prod$ uu$ (pair$ na$ nsa$))) (insert$ na$ nsa$)))))) :named a12))
(assert (! (not (finite$ (reachable_via$ graph$ (uminus$ (insert$ (eps$ (case_prod$ uu$ (pair$ na$ nsa$))) (insert$ na$ nsa$))) (eps$ (case_prod$ uu$ (pair$ na$ nsa$)))))) :named a13))
(assert (! (forall ((?v0 Node_set$) (?v1 Node_set$)) (= (= (uminus$ ?v0) (uminus$ ?v1)) (= ?v0 ?v1))) :named a14))
(assert (! (forall ((?v0 Node$) (?v1 Node_set$)) (= (member$ ?v0 (uminus$ ?v1)) (not (member$ ?v0 ?v1)))) :named a15))
(assert (! (forall ((?v0 Node$) (?v1 Node_set$)) (=> (=> (member$ ?v0 ?v1) false) (member$ ?v0 (uminus$ ?v1)))) :named a16))
(assert (! (forall ((?v0 Node$) (?v1 Node_set$)) (= (insert$ ?v0 (insert$ ?v0 ?v1)) (insert$ ?v0 ?v1))) :named a17))
(assert (! (forall ((?v0 Node$) (?v1 Node$) (?v2 Node_set$)) (= (member$ ?v0 (insert$ ?v1 ?v2)) (or (= ?v0 ?v1) (member$ ?v0 ?v2)))) :named a18))
(check-sat)
;(get-unsat-core)
