; --full-saturate-quant --inst-when=full-last-call --inst-no-entail --term-db-mode=relevant --random-seed=1 --lang=smt2 --tlimit 420
;(set-option :produce-unsat-cores true)
(set-logic ALL_SUPPORTED)
(declare-sort A$ 0)
(declare-sort Nat$ 0)
(declare-sort A_set$ 0)
(declare-sort A_llist_set$ 0)
(declare-sort Nat_a_llist_fun$ 0)
(declare-codatatypes () ((A_llist$ (lNil$) (lCons$ (lhd$ A$) (ltl$ A_llist$)))))
(declare-fun a$ () A_set$)
(declare-fun i$ () Nat$)
(declare-fun t$ () A_llist$)
(declare-fun top$ () A_set$)
(declare-fun lrev$ (A_llist$) A_llist$)
(declare-fun plus$ (Nat$ Nat$) Nat$)
(declare-fun zero$ () Nat$)
(declare-fun ldrop$ (A_llist$) Nat_a_llist_fun$)
(declare-fun member$ (A_llist$ A_llist_set$) Bool)
(declare-fun alllsts$ (A_set$) A_llist_set$)
(declare-fun finlsts$ (A_set$) A_llist_set$)
(declare-fun fun_app$ (Nat_a_llist_fun$ Nat$) A_llist$)
(declare-fun lappend$ (A_llist$ A_llist$) A_llist$)
(assert (! (not (member$ (fun_app$ (ldrop$ t$) i$) (finlsts$ a$))) :named a0))
(assert (! (member$ t$ (finlsts$ a$)) :named a1))
(assert (! (forall ((?v0 A_llist$) (?v1 A_set$)) (=> (member$ ?v0 (finlsts$ ?v1)) (member$ (lrev$ ?v0) (finlsts$ ?v1)))) :named a2))
(assert (! (forall ((?v0 Nat$)) (! (= (fun_app$ (ldrop$ lNil$) ?v0) lNil$) :pattern ((fun_app$ (ldrop$ lNil$) ?v0)))) :named a3))
(assert (! (forall ((?v0 A_llist$) (?v1 A_set$) (?v2 Nat$)) (=> (member$ ?v0 (alllsts$ ?v1)) (member$ (fun_app$ (ldrop$ ?v0) ?v2) (alllsts$ ?v1)))) :named a4))
(assert (! (forall ((?v0 A_llist$)) (! (= (fun_app$ (ldrop$ ?v0) zero$) ?v0) :pattern ((ldrop$ ?v0)))) :named a5))
(assert (! (forall ((?v0 A_llist$) (?v1 Nat$) (?v2 Nat$)) (= (fun_app$ (ldrop$ ?v0) (plus$ ?v1 ?v2)) (fun_app$ (ldrop$ (fun_app$ (ldrop$ ?v0) ?v1)) ?v2))) :named a6))
(assert (! (forall ((?v0 A_llist$) (?v1 A_set$) (?v2 A_set$)) (=> (and (member$ ?v0 (finlsts$ ?v1)) (member$ ?v0 (alllsts$ ?v2))) (member$ ?v0 (finlsts$ ?v2)))) :named a7))
(assert (! (forall ((?v0 A_llist$) (?v1 A_set$)) (=> (member$ ?v0 (finlsts$ ?v1)) (member$ ?v0 (alllsts$ ?v1)))) :named a8))
(assert (! (forall ((?v0 A_llist$) (?v1 A_llist$) (?v2 A_set$)) (= (member$ (lappend$ ?v0 ?v1) (finlsts$ ?v2)) (and (member$ ?v0 (finlsts$ ?v2)) (member$ ?v1 (finlsts$ ?v2))))) :named a9))
(assert (! (forall ((?v0 A_llist$) (?v1 A_set$) (?v2 A_llist$) (?v3 A_llist$)) (=> (member$ ?v0 (finlsts$ ?v1)) (= (= (lappend$ ?v0 ?v2) (lappend$ ?v0 ?v3)) (= ?v2 ?v3)))) :named a10))
(assert (! (forall ((?v0 A_llist$) (?v1 A_set$)) (=> (and (member$ ?v0 (finlsts$ ?v1)) (not (member$ ?v0 (finlsts$ top$)))) false)) :named a11))
(assert (! (forall ((?v0 A_llist$) (?v1 A_set$)) (=> (member$ ?v0 (finlsts$ ?v1)) (member$ ?v0 (finlsts$ top$)))) :named a12))
(assert (! (forall ((?v0 A_set$)) (member$ lNil$ (finlsts$ ?v0))) :named a13))
(assert (! (forall ((?v0 A_llist$) (?v1 A_llist$)) (= (= lNil$ (lappend$ ?v0 ?v1)) (and (= ?v0 lNil$) (= ?v1 lNil$)))) :named a14))
(assert (! (forall ((?v0 A_llist$) (?v1 A_llist$)) (= (= (lappend$ ?v0 ?v1) lNil$) (and (= ?v0 lNil$) (= ?v1 lNil$)))) :named a15))
(assert (! (forall ((?v0 A_llist$)) (member$ ?v0 (alllsts$ top$))) :named a16))
(assert (! (= (lrev$ lNil$) lNil$) :named a17))
(assert (! (forall ((?v0 A_llist$)) (=> (member$ ?v0 (finlsts$ top$)) (= (lrev$ (lrev$ ?v0)) ?v0))) :named a18))
(check-sat)
;(get-unsat-core)
