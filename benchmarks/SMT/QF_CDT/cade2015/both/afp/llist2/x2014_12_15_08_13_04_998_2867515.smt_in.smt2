; --full-saturate-quant --inst-when=full-last-call --inst-no-entail --term-db-mode=relevant --random-seed=1 --lang=smt2 --tlimit 435
;(set-option :produce-unsat-cores true)
(set-logic ALL_SUPPORTED)
(declare-sort A$ 0)
(declare-sort A_llist_a_llist_fun$ 0)
(declare-codatatypes () ((A_llist$ (lNil$) (lCons$ (lhd$ A$) (ltl$ A_llist$)))))
(declare-fun r$ () A_llist$)
(declare-fun s$ () A_llist$)
(declare-fun fun_app$ (A_llist_a_llist_fun$ A_llist$) A_llist$)
(declare-fun lappend$ (A_llist$) A_llist_a_llist_fun$)
(declare-fun less_eq$ (A_llist$ A_llist$) Bool)
(assert (! (not (less_eq$ r$ (fun_app$ (lappend$ r$) s$))) :named a0))
(assert (! (forall ((?v0 A_llist$)) (less_eq$ ?v0 ?v0)) :named a1))
(assert (! (forall ((?v0 A_llist$) (?v1 A_llist$)) (= (less_eq$ ?v0 ?v1) (exists ((?v2 A_llist$)) (= ?v1 (fun_app$ (lappend$ ?v0) ?v2))))) :named a2))
(assert (! (forall ((?v0 A_llist$) (?v1 A_llist$)) (=> (and (less_eq$ ?v0 ?v1) (less_eq$ ?v1 ?v0)) (= ?v0 ?v1))) :named a3))
(assert (! (forall ((?v0 A_llist$) (?v1 A_llist$) (?v2 A_llist$)) (=> (and (less_eq$ ?v0 ?v1) (less_eq$ ?v1 ?v2)) (less_eq$ ?v0 ?v2))) :named a4))
(assert (! (forall ((?v0 A_llist$)) (less_eq$ ?v0 ?v0)) :named a5))
(assert (! (forall ((?v0 A_llist$) (?v1 A_llist$) (?v2 A_llist$)) (= (fun_app$ (lappend$ (fun_app$ (lappend$ ?v0) ?v1)) ?v2) (fun_app$ (lappend$ ?v0) (fun_app$ (lappend$ ?v1) ?v2)))) :named a6))
(assert (! (forall ((?v0 A_llist$) (?v1 A_llist$)) (= (= ?v0 ?v1) (and (less_eq$ ?v0 ?v1) (less_eq$ ?v1 ?v0)))) :named a7))
(assert (! (forall ((?v0 A_llist$) (?v1 A_llist_a_llist_fun$) (?v2 A_llist$) (?v3 A_llist$)) (=> (and (= ?v0 (fun_app$ ?v1 ?v2)) (and (less_eq$ ?v2 ?v3) (forall ((?v4 A_llist$) (?v5 A_llist$)) (=> (less_eq$ ?v4 ?v5) (less_eq$ (fun_app$ ?v1 ?v4) (fun_app$ ?v1 ?v5)))))) (less_eq$ ?v0 (fun_app$ ?v1 ?v3)))) :named a8))
(assert (! (forall ((?v0 A_llist$) (?v1 A_llist$) (?v2 A_llist$)) (=> (and (= ?v0 ?v1) (less_eq$ ?v1 ?v2)) (less_eq$ ?v0 ?v2))) :named a9))
(assert (! (forall ((?v0 A_llist$) (?v1 A_llist$)) (=> (= ?v0 ?v1) (less_eq$ ?v0 ?v1))) :named a10))
(assert (! (forall ((?v0 A_llist$)) (less_eq$ ?v0 ?v0)) :named a11))
(check-sat)
;(get-unsat-core)
