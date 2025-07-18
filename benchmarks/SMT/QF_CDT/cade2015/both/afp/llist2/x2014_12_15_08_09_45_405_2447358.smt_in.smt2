; --full-saturate-quant --inst-when=full-last-call --inst-no-entail --term-db-mode=relevant --random-seed=1 --lang=smt2 --tlimit 426
;(set-option :produce-unsat-cores true)
(set-logic ALL_SUPPORTED)
(declare-sort A$ 0)
(declare-sort Nat$ 0)
(declare-sort A_set$ 0)
(declare-sort A_bool_fun$ 0)
(declare-sort A_llist_set$ 0)
(declare-sort Nat_a_llist_fun$ 0)
(declare-sort A_llist_bool_fun$ 0)
(declare-sort A_llist_a_set_fun$ 0)
(declare-sort A_llist_a_llist_fun$ 0)
(declare-codatatypes () ((A_llist$ (lNil$) (lCons$ (lhd$ A$) (ltl$ A_llist$)))))
(declare-fun i$ () Nat$)
(declare-fun lrev$ (A_llist$) A_llist$)
(declare-fun zero$ () Nat$)
(declare-fun ltake$ (A_llist$) Nat_a_llist_fun$)
(declare-fun member$ (A_llist$ A_llist_set$) Bool)
(declare-fun alllsts$ (A_set$) A_llist_set$)
(declare-fun fun_app$ (Nat_a_llist_fun$ Nat$) A_llist$)
(declare-fun lappend$ (A_llist$) A_llist_a_llist_fun$)
(declare-fun lmember$ (A$) A_llist_bool_fun$)
(declare-fun alllstsp$ (A_bool_fun$ A_llist$) Bool)
(declare-fun finlstsp$ (A_bool_fun$ A_llist$) Bool)
(declare-fun fun_app$a (A_llist_bool_fun$ A_llist$) Bool)
(declare-fun fun_app$b (A_llist_a_llist_fun$ A_llist$) A_llist$)
(declare-fun fun_app$c (A_llist_a_set_fun$ A_llist$) A_set$)
(declare-fun gen_lset$ (A_set$) A_llist_a_set_fun$)
(declare-fun lbutlast$ (A_llist$) A_llist$)
(assert (! (not (= (fun_app$ (ltake$ lNil$) i$) lNil$)) :named a0))
(assert (! (= (lbutlast$ lNil$) lNil$) :named a1))
(assert (! (forall ((?v0 A_llist$)) (! (= (fun_app$ (ltake$ ?v0) zero$) lNil$) :pattern ((ltake$ ?v0)))) :named a2))
(assert (! (= (lrev$ lNil$) lNil$) :named a3))
(assert (! (forall ((?v0 A_bool_fun$)) (finlstsp$ ?v0 lNil$)) :named a4))
(assert (! (forall ((?v0 A_bool_fun$)) (alllstsp$ ?v0 lNil$)) :named a5))
(assert (! (forall ((?v0 A_set$)) (member$ lNil$ (alllsts$ ?v0))) :named a6))
(assert (! (forall ((?v0 A$)) (! (= (fun_app$a (lmember$ ?v0) lNil$) false) :pattern ((lmember$ ?v0)))) :named a7))
(assert (! (forall ((?v0 A_llist$) (?v1 A_llist$)) (= (= lNil$ (fun_app$b (lappend$ ?v0) ?v1)) (and (= ?v0 lNil$) (= ?v1 lNil$)))) :named a8))
(assert (! (forall ((?v0 A_llist$) (?v1 A_llist$)) (= (= (fun_app$b (lappend$ ?v0) ?v1) lNil$) (and (= ?v0 lNil$) (= ?v1 lNil$)))) :named a9))
(assert (! (forall ((?v0 A_set$)) (! (= (fun_app$c (gen_lset$ ?v0) lNil$) ?v0) :pattern ((gen_lset$ ?v0)))) :named a10))
(assert (! (forall ((?v0 A_llist$)) (! (= (fun_app$b (lappend$ lNil$) ?v0) ?v0) :pattern ((fun_app$b (lappend$ lNil$) ?v0)))) :named a11))
(assert (! (forall ((?v0 A_llist$)) (! (= (fun_app$b (lappend$ ?v0) lNil$) ?v0) :pattern ((lappend$ ?v0)))) :named a12))
(assert (! (forall ((?v0 A_llist$) (?v1 A_llist$)) (= (= (fun_app$b (lappend$ ?v0) ?v1) lNil$) (and (= ?v0 lNil$) (= ?v1 lNil$)))) :named a13))
(assert (! (forall ((?v0 A_llist$) (?v1 A_llist$)) (= (= lNil$ (fun_app$b (lappend$ ?v0) ?v1)) (and (= ?v0 lNil$) (= ?v1 lNil$)))) :named a14))
(assert (! (forall ((?v0 A_llist$) (?v1 A_llist$) (?v2 A_llist$)) (= (fun_app$b (lappend$ (fun_app$b (lappend$ ?v0) ?v1)) ?v2) (fun_app$b (lappend$ ?v0) (fun_app$b (lappend$ ?v1) ?v2)))) :named a15))
(check-sat)
;(get-unsat-core)
