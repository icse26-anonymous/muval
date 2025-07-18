; --full-saturate-quant --inst-when=full-last-call --inst-no-entail --term-db-mode=relevant --random-seed=1 --lang=smt2 --tlimit 466
;(set-option :produce-unsat-cores true)
(set-logic ALL_SUPPORTED)
(declare-sort Ref$ 0)
(declare-sort Ref_set$ 0)
(declare-sort Dag_dag_fun$ 0)
(declare-sort Dag_ref_set_fun$ 0)
(declare-sort Ref_set_dag_fun$ 0)
(declare-sort Ref_set_ref_set_fun$ 0)
(declare-datatypes () ((Dag$ (tip$) (node$ (select$ Dag$) (selecta$ Ref$) (selectb$ Dag$)))))
(declare-fun x$ () Dag$)
(declare-fun y$ () Dag$)
(declare-fun dag$ (Dag$) Bool)
(declare-fun less$ (Ref_set$ Ref_set$) Bool)
(declare-fun less$a (Dag$ Dag$) Bool)
(declare-fun member$ (Ref$ Ref_set$) Bool)
(declare-fun set_of$ (Dag$) Ref_set$)
(declare-fun fun_app$ (Ref_set_ref_set_fun$ Ref_set$) Ref_set$)
(declare-fun fun_app$a (Ref_set_dag_fun$ Ref_set$) Dag$)
(declare-fun fun_app$b (Dag_ref_set_fun$ Dag$) Ref_set$)
(declare-fun fun_app$c (Dag_dag_fun$ Dag$) Dag$)
(assert (! (not (less$ (set_of$ x$) (set_of$ y$))) :named a0))
(assert (! (= y$ tip$) :named a1))
(assert (! (dag$ y$) :named a2))
(assert (! (less$a x$ y$) :named a3))
(assert (! (forall ((?v0 Ref_set$) (?v1 Ref_set$) (?v2 Ref$)) (=> (and (less$ ?v0 ?v1) (member$ ?v2 ?v0)) (member$ ?v2 ?v1))) :named a4))
(assert (! (forall ((?v0 Ref_set$) (?v1 Ref_set$) (?v2 Ref_set$)) (=> (and (less$ ?v0 ?v1) (less$ ?v1 ?v2)) (less$ ?v0 ?v2))) :named a5))
(assert (! (forall ((?v0 Ref_set$) (?v1 Ref_set_ref_set_fun$) (?v2 Ref_set$) (?v3 Ref_set$)) (=> (and (= ?v0 (fun_app$ ?v1 ?v2)) (and (less$ ?v2 ?v3) (forall ((?v4 Ref_set$) (?v5 Ref_set$)) (=> (less$ ?v4 ?v5) (less$ (fun_app$ ?v1 ?v4) (fun_app$ ?v1 ?v5)))))) (less$ ?v0 (fun_app$ ?v1 ?v3)))) :named a6))
(assert (! (forall ((?v0 Dag$) (?v1 Ref_set_dag_fun$) (?v2 Ref_set$) (?v3 Ref_set$)) (=> (and (= ?v0 (fun_app$a ?v1 ?v2)) (and (less$ ?v2 ?v3) (forall ((?v4 Ref_set$) (?v5 Ref_set$)) (=> (less$ ?v4 ?v5) (less$a (fun_app$a ?v1 ?v4) (fun_app$a ?v1 ?v5)))))) (less$a ?v0 (fun_app$a ?v1 ?v3)))) :named a7))
(assert (! (forall ((?v0 Ref_set$) (?v1 Dag_ref_set_fun$) (?v2 Dag$) (?v3 Dag$)) (=> (and (= ?v0 (fun_app$b ?v1 ?v2)) (and (less$a ?v2 ?v3) (forall ((?v4 Dag$) (?v5 Dag$)) (=> (less$a ?v4 ?v5) (less$ (fun_app$b ?v1 ?v4) (fun_app$b ?v1 ?v5)))))) (less$ ?v0 (fun_app$b ?v1 ?v3)))) :named a8))
(assert (! (forall ((?v0 Dag$) (?v1 Dag_dag_fun$) (?v2 Dag$) (?v3 Dag$)) (=> (and (= ?v0 (fun_app$c ?v1 ?v2)) (and (less$a ?v2 ?v3) (forall ((?v4 Dag$) (?v5 Dag$)) (=> (less$a ?v4 ?v5) (less$a (fun_app$c ?v1 ?v4) (fun_app$c ?v1 ?v5)))))) (less$a ?v0 (fun_app$c ?v1 ?v3)))) :named a9))
(assert (! (forall ((?v0 Ref_set$) (?v1 Ref_set$) (?v2 Ref_set$)) (=> (and (= ?v0 ?v1) (less$ ?v1 ?v2)) (less$ ?v0 ?v2))) :named a10))
(assert (! (forall ((?v0 Dag$) (?v1 Dag$) (?v2 Dag$)) (=> (and (= ?v0 ?v1) (less$a ?v1 ?v2)) (less$a ?v0 ?v2))) :named a11))
(assert (! (forall ((?v0 Ref_set$) (?v1 Ref_set$)) (=> (and (less$ ?v0 ?v1) (=> (not false) (less$ ?v1 ?v0))) false)) :named a12))
(assert (! (forall ((?v0 Dag$) (?v1 Dag$)) (=> (and (less$a ?v0 ?v1) (=> (not false) (less$a ?v1 ?v0))) false)) :named a13))
(assert (! (forall ((?v0 Ref_set$) (?v1 Ref_set$) (?v2 Ref_set_ref_set_fun$) (?v3 Ref_set$)) (=> (and (less$ ?v0 ?v1) (and (= (fun_app$ ?v2 ?v1) ?v3) (forall ((?v4 Ref_set$) (?v5 Ref_set$)) (=> (less$ ?v4 ?v5) (less$ (fun_app$ ?v2 ?v4) (fun_app$ ?v2 ?v5)))))) (less$ (fun_app$ ?v2 ?v0) ?v3))) :named a14))
(assert (! (forall ((?v0 Ref_set$) (?v1 Ref_set$) (?v2 Ref_set_dag_fun$) (?v3 Dag$)) (=> (and (less$ ?v0 ?v1) (and (= (fun_app$a ?v2 ?v1) ?v3) (forall ((?v4 Ref_set$) (?v5 Ref_set$)) (=> (less$ ?v4 ?v5) (less$a (fun_app$a ?v2 ?v4) (fun_app$a ?v2 ?v5)))))) (less$a (fun_app$a ?v2 ?v0) ?v3))) :named a15))
(assert (! (forall ((?v0 Dag$) (?v1 Dag$) (?v2 Dag_ref_set_fun$) (?v3 Ref_set$)) (=> (and (less$a ?v0 ?v1) (and (= (fun_app$b ?v2 ?v1) ?v3) (forall ((?v4 Dag$) (?v5 Dag$)) (=> (less$a ?v4 ?v5) (less$ (fun_app$b ?v2 ?v4) (fun_app$b ?v2 ?v5)))))) (less$ (fun_app$b ?v2 ?v0) ?v3))) :named a16))
(assert (! (forall ((?v0 Dag$) (?v1 Dag$) (?v2 Dag_dag_fun$) (?v3 Dag$)) (=> (and (less$a ?v0 ?v1) (and (= (fun_app$c ?v2 ?v1) ?v3) (forall ((?v4 Dag$) (?v5 Dag$)) (=> (less$a ?v4 ?v5) (less$a (fun_app$c ?v2 ?v4) (fun_app$c ?v2 ?v5)))))) (less$a (fun_app$c ?v2 ?v0) ?v3))) :named a17))
(assert (! (forall ((?v0 Ref_set$) (?v1 Ref_set$) (?v2 Ref_set$)) (=> (and (less$ ?v0 ?v1) (= ?v1 ?v2)) (less$ ?v0 ?v2))) :named a18))
(assert (! (forall ((?v0 Dag$) (?v1 Dag$) (?v2 Dag$)) (=> (and (less$a ?v0 ?v1) (= ?v1 ?v2)) (less$a ?v0 ?v2))) :named a19))
(assert (! (forall ((?v0 Dag$) (?v1 Dag$)) (=> (and (dag$ ?v0) (less$a ?v1 ?v0)) (dag$ ?v1))) :named a20))
(assert (! (= (dag$ tip$) true) :named a21))
(check-sat)
;(get-unsat-core)
