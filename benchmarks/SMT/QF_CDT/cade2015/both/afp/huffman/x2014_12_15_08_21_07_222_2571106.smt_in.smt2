; --full-saturate-quant --inst-when=full-last-call --inst-no-entail --term-db-mode=relevant --random-seed=1 --lang=smt2 --tlimit 645
;(set-option :produce-unsat-cores true)
(set-logic ALL_SUPPORTED)
(declare-sort A$ 0)
(declare-sort Nat$ 0)
(declare-sort A_set$ 0)
(declare-sort A_nat_fun$ 0)
(declare-sort Nat_nat_fun$ 0)
(declare-datatypes () ((A_tree$ (leaf$ (select$ Nat$) (selecta$ A$)) (innerNode$ (selectb$ Nat$) (selectc$ A_tree$) (selectd$ A_tree$)))))
(declare-fun a$ () A$)
(declare-fun t$ () A_tree$)
(declare-fun uu$ () A_nat_fun$)
(declare-fun freq$ (A_tree$) A_nat_fun$)
(declare-fun plus$ (Nat$) Nat_nat_fun$)
(declare-fun zero$ () Nat$)
(declare-fun member$ (A$ A_set$) Bool)
(declare-fun fun_app$ (A_nat_fun$ A$) Nat$)
(declare-fun sibling$ (A_tree$ A$) A$)
(declare-fun alphabet$ (A_tree$) A_set$)
(declare-fun fun_app$a (Nat_nat_fun$ Nat$) Nat$)
(declare-fun consistent$ (A_tree$) Bool)
(declare-fun mergeSibling$ (A_tree$ A$) A_tree$)
(assert (! (forall ((?v0 A$)) (! (= (fun_app$ uu$ ?v0) (ite (= ?v0 a$) (fun_app$a (plus$ (fun_app$ (freq$ t$) a$)) (fun_app$ (freq$ t$) (sibling$ t$ a$))) (ite (= ?v0 (sibling$ t$ a$)) zero$ (fun_app$ (freq$ t$) ?v0)))) :pattern ((fun_app$ uu$ ?v0)))) :named a0))
(assert (! (not (= (freq$ (mergeSibling$ t$ a$)) uu$)) :named a1))
(assert (! (consistent$ t$) :named a2))
(assert (! (member$ a$ (alphabet$ t$)) :named a3))
(assert (! (not (= (sibling$ t$ a$) a$)) :named a4))
(assert (! (forall ((?v0 A$) (?v1 A_tree$)) (! (=> (not (member$ ?v0 (alphabet$ ?v1))) (= (sibling$ ?v1 ?v0) ?v0)) :pattern ((sibling$ ?v1 ?v0)))) :named a5))
(assert (! (forall ((?v0 A_tree$) (?v1 A$)) (=> (consistent$ ?v0) (= (sibling$ ?v0 (sibling$ ?v0 ?v1)) ?v1))) :named a6))
(assert (! (forall ((?v0 A$) (?v1 A_tree$)) (! (=> (not (member$ ?v0 (alphabet$ ?v1))) (= (mergeSibling$ ?v1 ?v0) ?v1)) :pattern ((mergeSibling$ ?v1 ?v0)))) :named a7))
(assert (! (forall ((?v0 A$) (?v1 A_tree$)) (! (=> (not (member$ ?v0 (alphabet$ ?v1))) (= (fun_app$ (freq$ ?v1) ?v0) zero$)) :pattern ((fun_app$ (freq$ ?v1) ?v0)))) :named a8))
(assert (! (forall ((?v0 A$) (?v1 A_tree$)) (=> (member$ ?v0 (alphabet$ ?v1)) (member$ (sibling$ ?v1 ?v0) (alphabet$ ?v1)))) :named a9))
(assert (! (forall ((?v0 A_tree$) (?v1 A$)) (=> (not (= (sibling$ ?v0 ?v1) ?v1)) (member$ (sibling$ ?v0 ?v1) (alphabet$ ?v0)))) :named a10))
(assert (! (forall ((?v0 A_tree$) (?v1 A$) (?v2 A$)) (=> (and (consistent$ ?v0) (= (sibling$ ?v0 ?v1) ?v2)) (= (sibling$ ?v0 ?v2) ?v1))) :named a11))
(assert (! (forall ((?v0 A_tree$) (?v1 A$)) (=> (consistent$ ?v0) (consistent$ (mergeSibling$ ?v0 ?v1)))) :named a12))
(assert (! (forall ((?v0 A_tree$)) (exists ((?v1 A$)) (member$ ?v1 (alphabet$ ?v0)))) :named a13))
(assert (! (forall ((?v0 Nat$) (?v1 Nat$)) (= (= (fun_app$a (plus$ ?v0) ?v1) zero$) (and (= ?v0 zero$) (= ?v1 zero$)))) :named a14))
(assert (! (forall ((?v0 Nat$)) (! (= (fun_app$a (plus$ ?v0) zero$) ?v0) :pattern ((plus$ ?v0)))) :named a15))
(assert (! (forall ((?v0 Nat$)) (= (fun_app$a (plus$ ?v0) zero$) ?v0)) :named a16))
(assert (! (forall ((?v0 Nat$)) (= (fun_app$a (plus$ ?v0) zero$) ?v0)) :named a17))
(assert (! (forall ((?v0 Nat$)) (= (fun_app$a (plus$ zero$) ?v0) ?v0)) :named a18))
(assert (! (forall ((?v0 Nat$)) (= (fun_app$a (plus$ zero$) ?v0) ?v0)) :named a19))
(check-sat)
;(get-unsat-core)
