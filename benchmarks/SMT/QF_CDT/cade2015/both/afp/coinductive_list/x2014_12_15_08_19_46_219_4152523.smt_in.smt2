; --full-saturate-quant --inst-when=full-last-call --inst-no-entail --term-db-mode=relevant --random-seed=1 --lang=smt2 --tlimit 649
;(set-option :produce-unsat-cores true)
(set-logic ALL_SUPPORTED)
(declare-sort A$ 0)
(declare-sort Nat$ 0)
(declare-sort A_a_fun$ 0)
(declare-sort A_llist_a_fun$ 0)
(declare-sort A_a_fun_a_a_fun_fun$ 0)
(declare-sort A_a_llist_a_fun_fun$ 0)
(declare-sort Nat_a_a_fun_a_a_fun_fun_fun$ 0)
(declare-codatatypes () ((A_llist$ (lNil$) (lCons$ (lhd$ A$) (ltl$ A_llist$)))))
(declare-fun f$ () A_a_fun$)
(declare-fun na$ () Nat$)
(declare-fun uu$ (Nat$) A_a_llist_a_fun_fun$)
(declare-fun xa$ () A$)
(declare-fun suc$ (Nat$) Nat$)
(declare-fun comp$ (A_a_fun$) A_a_fun_a_a_fun_fun$)
(declare-fun lnth$ (A_llist$ Nat$) A$)
(declare-fun compow$ () Nat_a_a_fun_a_a_fun_fun_fun$)
(declare-fun funpow$ () Nat_a_a_fun_a_a_fun_fun_fun$)
(declare-fun ldropn$ (Nat$ A_llist$) A_llist$)
(declare-fun fun_app$ (A_llist_a_fun$ A_llist$) A$)
(declare-fun fun_app$a (A_a_llist_a_fun_fun$ A$) A_llist_a_fun$)
(declare-fun fun_app$b (A_a_fun$ A$) A$)
(declare-fun fun_app$c (A_a_fun_a_a_fun_fun$ A_a_fun$) A_a_fun$)
(declare-fun fun_app$d (Nat_a_a_fun_a_a_fun_fun_fun$ Nat$) A_a_fun_a_a_fun_fun$)
(declare-fun iterates$ (A_a_fun$ A$) A_llist$)
(declare-fun undefined$ (Nat$) A$)
(declare-fun case_llist$ (A$ A_a_llist_a_fun_fun$ A_llist$) A$)
(assert (! (forall ((?v0 Nat$) (?v1 A$) (?v2 A_llist$)) (! (= (fun_app$ (fun_app$a (uu$ ?v0) ?v1) ?v2) (lnth$ ?v2 ?v0)) :pattern ((fun_app$ (fun_app$a (uu$ ?v0) ?v1) ?v2)))) :named a0))
(assert (! (not (= (lnth$ (iterates$ f$ xa$) (suc$ na$)) (fun_app$b (fun_app$c (fun_app$d compow$ (suc$ na$)) f$) xa$))) :named a1))
(assert (! (= (lnth$ (iterates$ f$ (fun_app$b f$ xa$)) na$) (fun_app$b (fun_app$c (fun_app$d compow$ na$) f$) (fun_app$b f$ xa$))) :named a2))
(assert (! (forall ((?v0 A$)) (= (lnth$ (iterates$ f$ ?v0) na$) (fun_app$b (fun_app$c (fun_app$d compow$ na$) f$) ?v0))) :named a3))
(assert (! (forall ((?v0 Nat$) (?v1 Nat$)) (= (= (suc$ ?v0) (suc$ ?v1)) (= ?v0 ?v1))) :named a4))
(assert (! (forall ((?v0 Nat$) (?v1 Nat$)) (= (= (suc$ ?v0) (suc$ ?v1)) (= ?v0 ?v1))) :named a5))
(assert (! (forall ((?v0 A_a_fun$) (?v1 Nat$) (?v2 A$)) (= (fun_app$b ?v0 (fun_app$b (fun_app$c (fun_app$d compow$ ?v1) ?v0) ?v2)) (fun_app$b (fun_app$c (fun_app$d compow$ ?v1) ?v0) (fun_app$b ?v0 ?v2)))) :named a6))
(assert (! (forall ((?v0 Nat$) (?v1 Nat$)) (=> (= (suc$ ?v0) (suc$ ?v1)) (= ?v0 ?v1))) :named a7))
(assert (! (forall ((?v0 Nat$)) (not (= ?v0 (suc$ ?v0)))) :named a8))
(assert (! (forall ((?v0 Nat$) (?v1 A_a_fun$) (?v2 A$)) (= (ldropn$ ?v0 (iterates$ ?v1 ?v2)) (iterates$ ?v1 (fun_app$b (fun_app$c (fun_app$d compow$ ?v0) ?v1) ?v2)))) :named a9))
(assert (! (forall ((?v0 A$) (?v1 A_llist$) (?v2 Nat$)) (! (= (lnth$ (lCons$ ?v0 ?v1) (suc$ ?v2)) (lnth$ ?v1 ?v2)) :pattern ((lnth$ (lCons$ ?v0 ?v1) (suc$ ?v2))))) :named a10))
(assert (! (= funpow$ compow$) :named a11))
(assert (! (forall ((?v0 A_llist$) (?v1 Nat$)) (= (lnth$ ?v0 (suc$ ?v1)) (case_llist$ (undefined$ (suc$ ?v1)) (uu$ ?v1) ?v0))) :named a12))
(assert (! (forall ((?v0 Nat$) (?v1 A_a_fun$)) (! (= (fun_app$c (fun_app$d compow$ (suc$ ?v0)) ?v1) (fun_app$c (comp$ ?v1) (fun_app$c (fun_app$d compow$ ?v0) ?v1))) :pattern ((fun_app$c (fun_app$d compow$ (suc$ ?v0)) ?v1)))) :named a13))
(assert (! (forall ((?v0 Nat$) (?v1 A_a_fun$)) (! (= (fun_app$c (fun_app$d compow$ (suc$ ?v0)) ?v1) (fun_app$c (comp$ (fun_app$c (fun_app$d compow$ ?v0) ?v1)) ?v1)) :pattern ((fun_app$c (fun_app$d compow$ (suc$ ?v0)) ?v1)))) :named a14))
(assert (! (forall ((?v0 A$) (?v1 A_llist$) (?v2 A$) (?v3 A_llist$)) (= (= (lCons$ ?v0 ?v1) (lCons$ ?v2 ?v3)) (and (= ?v0 ?v2) (= ?v1 ?v3)))) :named a15))
(assert (! (forall ((?v0 Nat$) (?v1 A$) (?v2 A_llist$)) (! (= (ldropn$ (suc$ ?v0) (lCons$ ?v1 ?v2)) (ldropn$ ?v0 ?v2)) :pattern ((ldropn$ (suc$ ?v0) (lCons$ ?v1 ?v2))))) :named a16))
(assert (! (forall ((?v0 A$) (?v1 A_a_llist_a_fun_fun$) (?v2 A$) (?v3 A_llist$)) (! (= (case_llist$ ?v0 ?v1 (lCons$ ?v2 ?v3)) (fun_app$ (fun_app$a ?v1 ?v2) ?v3)) :pattern ((case_llist$ ?v0 ?v1 (lCons$ ?v2 ?v3))))) :named a17))
(check-sat)
;(get-unsat-core)
