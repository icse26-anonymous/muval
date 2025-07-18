; --full-saturate-quant --inst-when=full-last-call --inst-no-entail --term-db-mode=relevant --random-seed=1 --lang=smt2 --tlimit 662
;(set-option :produce-unsat-cores true)
(set-logic ALL_SUPPORTED)
(declare-sort A$ 0)
(declare-sort Nat$ 0)
(declare-sort Nat_bool_fun$ 0)
(declare-sort Nat_nat_bool_fun_fun$ 0)
(declare-datatypes () ((Nat_option$ (none$) (some$ (the$ Nat$)))
  (Enat$ (abs_enat$ (rep_enat$ Nat_option$)))))
(declare-codatatypes () ((A_llist$ (lNil$) (lCons$ (lhd$ A$) (ltl$ A_llist$)))))
(declare-fun i$ () Nat$)
(declare-fun j$ () Nat$)
(declare-fun ia$ () Nat$)
(declare-fun ja$ () Nat$)
(declare-fun xs$ () A_llist$)
(declare-fun enat$ (Nat$) Enat$)
(declare-fun less$ (Nat$) Nat_bool_fun$)
(declare-fun less$a (Enat$ Enat$) Bool)
(declare-fun fun_app$ (Nat_bool_fun$ Nat$) Bool)
(declare-fun less_eq$ (Nat$) Nat_bool_fun$)
(declare-fun llength$ (A_llist$) Enat$)
(declare-fun fun_app$a (Nat_nat_bool_fun_fun$ Nat$) Nat_bool_fun$)
(declare-fun ldistinct$ (A_llist$) Bool)
(assert (! (not (fun_app$ (less$ ia$) ja$)) :named a0))
(assert (! (not (= i$ j$)) :named a1))
(assert (! (not (= ia$ ja$)) :named a2))
(assert (! (fun_app$ (less_eq$ ia$) ja$) :named a3))
(assert (! (less$a (enat$ ia$) (llength$ xs$)) :named a4))
(assert (! (ldistinct$ xs$) :named a5))
(assert (! (less$a (enat$ ja$) (llength$ xs$)) :named a6))
(assert (! (forall ((?v0 Nat$) (?v1 Nat$)) (= (not (= ?v0 ?v1)) (or (fun_app$ (less$ ?v0) ?v1) (fun_app$ (less$ ?v1) ?v0)))) :named a7))
(assert (! (forall ((?v0 Nat$) (?v1 Nat$) (?v2 Nat_nat_bool_fun_fun$)) (=> (and (=> (fun_app$ (less$ ?v0) ?v1) (fun_app$ (fun_app$a ?v2 ?v1) ?v0)) (and (=> (= ?v0 ?v1) (fun_app$ (fun_app$a ?v2 ?v1) ?v0)) (=> (fun_app$ (less$ ?v1) ?v0) (fun_app$ (fun_app$a ?v2 ?v1) ?v0)))) (fun_app$ (fun_app$a ?v2 ?v1) ?v0))) :named a8))
(assert (! (forall ((?v0 Nat_bool_fun$) (?v1 Nat$)) (=> (forall ((?v2 Nat$)) (=> (not (fun_app$ ?v0 ?v2)) (exists ((?v3 Nat$)) (and (fun_app$ (less$ ?v3) ?v2) (not (fun_app$ ?v0 ?v3)))))) (fun_app$ ?v0 ?v1))) :named a9))
(assert (! (forall ((?v0 Nat_bool_fun$) (?v1 Nat$)) (=> (forall ((?v2 Nat$)) (=> (forall ((?v3 Nat$)) (=> (fun_app$ (less$ ?v3) ?v2) (fun_app$ ?v0 ?v3))) (fun_app$ ?v0 ?v2))) (fun_app$ ?v0 ?v1))) :named a10))
(assert (! (forall ((?v0 Nat$) (?v1 Nat$)) (=> (fun_app$ (less$ ?v0) ?v1) (not (= ?v0 ?v1)))) :named a11))
(assert (! (forall ((?v0 Nat$) (?v1 Nat$)) (=> (fun_app$ (less$ ?v0) ?v1) (not (= ?v1 ?v0)))) :named a12))
(assert (! (forall ((?v0 Nat$)) (=> (fun_app$ (less$ ?v0) ?v0) false)) :named a13))
(assert (! (forall ((?v0 Nat$) (?v1 Nat$)) (=> (and (not (= ?v0 ?v1)) (and (=> (fun_app$ (less$ ?v0) ?v1) false) (=> (fun_app$ (less$ ?v1) ?v0) false))) false)) :named a14))
(check-sat)
;(get-unsat-core)
