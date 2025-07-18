; --full-saturate-quant --inst-when=full-last-call --inst-no-entail --term-db-mode=relevant --random-seed=1 --lang=smt2 --tlimit 661
;(set-option :produce-unsat-cores true)
(set-logic ALL_SUPPORTED)
(declare-sort A$ 0)
(declare-sort Nat$ 0)
(declare-sort A_a_fun$ 0)
(declare-sort Nat_nat_fun$ 0)
(declare-sort Enat_nat_fun$ 0)
(declare-sort Nat_bool_fun$ 0)
(declare-sort Nat_enat_fun$ 0)
(declare-sort Enat_bool_fun$ 0)
(declare-sort Enat_enat_fun$ 0)
(declare-datatypes () ((Nat_option$ (none$) (some$ (the$ Nat$)))
  (Enat$ (abs_enat$ (rep_enat$ Nat_option$)))))
(declare-codatatypes () ((A_llist$ (lNil$) (lCons$ (lhd$ A$) (ltl$ A_llist$)))))
(declare-fun x$ () A$)
(declare-fun xs$ () A_llist$)
(declare-fun enat$ (Nat$) Enat$)
(declare-fun less$ (Enat$) Enat_bool_fun$)
(declare-fun lmap$ (A_a_fun$ A_llist$) A_llist$)
(declare-fun lnth$ (A_llist$ Nat$) A$)
(declare-fun less$a (Nat$) Nat_bool_fun$)
(declare-fun thesis$ () Bool)
(declare-fun fun_app$ (Enat_bool_fun$ Enat$) Bool)
(declare-fun llength$ (A_llist$) Enat$)
(declare-fun fun_app$a (A_a_fun$ A$) A$)
(declare-fun fun_app$b (Nat_bool_fun$ Nat$) Bool)
(declare-fun fun_app$c (Enat_enat_fun$ Enat$) Enat$)
(declare-fun fun_app$d (Enat_nat_fun$ Enat$) Nat$)
(declare-fun fun_app$e (Nat_enat_fun$ Nat$) Enat$)
(declare-fun fun_app$f (Nat_nat_fun$ Nat$) Nat$)
(assert (! (not thesis$) :named a0))
(assert (! (forall ((?v0 Nat$)) (=> (and (fun_app$ (less$ (enat$ ?v0)) (llength$ xs$)) (= (lnth$ xs$ ?v0) x$)) thesis$)) :named a1))
(assert (! (exists ((?v0 Nat$)) (and (fun_app$ (less$ (enat$ ?v0)) (llength$ xs$)) (= (lnth$ xs$ ?v0) x$))) :named a2))
(assert (! (forall ((?v0 Nat$) (?v1 Nat$)) (= (= (enat$ ?v0) (enat$ ?v1)) (= ?v0 ?v1))) :named a3))
(assert (! (forall ((?v0 Enat$) (?v1 Nat$)) (=> (fun_app$ (less$ ?v0) (enat$ ?v1)) (exists ((?v2 Nat$)) (= ?v0 (enat$ ?v2))))) :named a4))
(assert (! (forall ((?v0 Nat$) (?v1 A_llist$) (?v2 A_a_fun$)) (=> (fun_app$ (less$ (enat$ ?v0)) (llength$ ?v1)) (= (lnth$ (lmap$ ?v2 ?v1) ?v0) (fun_app$a ?v2 (lnth$ ?v1 ?v0))))) :named a5))
(assert (! (forall ((?v0 Enat_bool_fun$) (?v1 Enat$)) (=> (forall ((?v2 Enat$)) (=> (forall ((?v3 Enat$)) (=> (fun_app$ (less$ ?v3) ?v2) (fun_app$ ?v0 ?v3))) (fun_app$ ?v0 ?v2))) (fun_app$ ?v0 ?v1))) :named a6))
(assert (! (forall ((?v0 Enat$) (?v1 Enat$)) (= (not (= ?v0 ?v1)) (or (fun_app$ (less$ ?v0) ?v1) (fun_app$ (less$ ?v1) ?v0)))) :named a7))
(assert (! (forall ((?v0 Nat$) (?v1 Nat$)) (= (not (= ?v0 ?v1)) (or (fun_app$b (less$a ?v0) ?v1) (fun_app$b (less$a ?v1) ?v0)))) :named a8))
(assert (! (forall ((?v0 Enat$) (?v1 Enat$)) (= (not (fun_app$ (less$ ?v0) ?v1)) (or (fun_app$ (less$ ?v1) ?v0) (= ?v0 ?v1)))) :named a9))
(assert (! (forall ((?v0 Nat$) (?v1 Nat$)) (= (not (fun_app$b (less$a ?v0) ?v1)) (or (fun_app$b (less$a ?v1) ?v0) (= ?v0 ?v1)))) :named a10))
(assert (! (forall ((?v0 Enat$) (?v1 Enat$)) (=> (and (=> (fun_app$ (less$ ?v0) ?v1) false) (and (=> (= ?v0 ?v1) false) (=> (fun_app$ (less$ ?v1) ?v0) false))) false)) :named a11))
(assert (! (forall ((?v0 Nat$) (?v1 Nat$)) (=> (and (=> (fun_app$b (less$a ?v0) ?v1) false) (and (=> (= ?v0 ?v1) false) (=> (fun_app$b (less$a ?v1) ?v0) false))) false)) :named a12))
(assert (! (forall ((?v0 Enat_bool_fun$) (?v1 Enat$)) (=> (forall ((?v2 Enat$)) (=> (forall ((?v3 Enat$)) (=> (fun_app$ (less$ ?v3) ?v2) (fun_app$ ?v0 ?v3))) (fun_app$ ?v0 ?v2))) (fun_app$ ?v0 ?v1))) :named a13))
(assert (! (forall ((?v0 Nat_bool_fun$) (?v1 Nat$)) (=> (forall ((?v2 Nat$)) (=> (forall ((?v3 Nat$)) (=> (fun_app$b (less$a ?v3) ?v2) (fun_app$b ?v0 ?v3))) (fun_app$b ?v0 ?v2))) (fun_app$b ?v0 ?v1))) :named a14))
(assert (! (forall ((?v0 Enat$) (?v1 Enat_enat_fun$) (?v2 Enat$) (?v3 Enat$)) (=> (and (= ?v0 (fun_app$c ?v1 ?v2)) (and (fun_app$ (less$ ?v2) ?v3) (forall ((?v4 Enat$) (?v5 Enat$)) (=> (fun_app$ (less$ ?v4) ?v5) (fun_app$ (less$ (fun_app$c ?v1 ?v4)) (fun_app$c ?v1 ?v5)))))) (fun_app$ (less$ ?v0) (fun_app$c ?v1 ?v3)))) :named a15))
(assert (! (forall ((?v0 Nat$) (?v1 Enat_nat_fun$) (?v2 Enat$) (?v3 Enat$)) (=> (and (= ?v0 (fun_app$d ?v1 ?v2)) (and (fun_app$ (less$ ?v2) ?v3) (forall ((?v4 Enat$) (?v5 Enat$)) (=> (fun_app$ (less$ ?v4) ?v5) (fun_app$b (less$a (fun_app$d ?v1 ?v4)) (fun_app$d ?v1 ?v5)))))) (fun_app$b (less$a ?v0) (fun_app$d ?v1 ?v3)))) :named a16))
(assert (! (forall ((?v0 Enat$) (?v1 Nat_enat_fun$) (?v2 Nat$) (?v3 Nat$)) (=> (and (= ?v0 (fun_app$e ?v1 ?v2)) (and (fun_app$b (less$a ?v2) ?v3) (forall ((?v4 Nat$) (?v5 Nat$)) (=> (fun_app$b (less$a ?v4) ?v5) (fun_app$ (less$ (fun_app$e ?v1 ?v4)) (fun_app$e ?v1 ?v5)))))) (fun_app$ (less$ ?v0) (fun_app$e ?v1 ?v3)))) :named a17))
(assert (! (forall ((?v0 Nat$) (?v1 Nat_nat_fun$) (?v2 Nat$) (?v3 Nat$)) (=> (and (= ?v0 (fun_app$f ?v1 ?v2)) (and (fun_app$b (less$a ?v2) ?v3) (forall ((?v4 Nat$) (?v5 Nat$)) (=> (fun_app$b (less$a ?v4) ?v5) (fun_app$b (less$a (fun_app$f ?v1 ?v4)) (fun_app$f ?v1 ?v5)))))) (fun_app$b (less$a ?v0) (fun_app$f ?v1 ?v3)))) :named a18))
(assert (! (forall ((?v0 Enat$) (?v1 Enat$) (?v2 Enat$)) (=> (and (= ?v0 ?v1) (fun_app$ (less$ ?v1) ?v2)) (fun_app$ (less$ ?v0) ?v2))) :named a19))
(assert (! (forall ((?v0 Nat$) (?v1 Nat$) (?v2 Nat$)) (=> (and (= ?v0 ?v1) (fun_app$b (less$a ?v1) ?v2)) (fun_app$b (less$a ?v0) ?v2))) :named a20))
(assert (! (forall ((?v0 Nat$) (?v1 Nat$)) (! (= (fun_app$ (less$ (enat$ ?v0)) (enat$ ?v1)) (fun_app$b (less$a ?v0) ?v1)) :pattern ((fun_app$ (less$ (enat$ ?v0)) (enat$ ?v1))))) :named a21))
(assert (! (forall ((?v0 A_a_fun$) (?v1 A_llist$)) (= (llength$ (lmap$ ?v0 ?v1)) (llength$ ?v1))) :named a22))
(assert (! (forall ((?v0 Enat$) (?v1 Nat$)) (=> (and (fun_app$ (less$ ?v0) (enat$ ?v1)) (forall ((?v2 Nat$)) (=> (and (= ?v0 (enat$ ?v2)) (fun_app$b (less$a ?v2) ?v1)) false))) false)) :named a23))
(assert (! (forall ((?v0 Enat$)) (not (fun_app$ (less$ ?v0) ?v0))) :named a24))
(assert (! (forall ((?v0 Nat$)) (not (fun_app$b (less$a ?v0) ?v0))) :named a25))
(check-sat)
;(get-unsat-core)
