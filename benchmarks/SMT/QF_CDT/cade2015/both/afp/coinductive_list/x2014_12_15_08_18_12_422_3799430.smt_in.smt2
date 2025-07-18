; --full-saturate-quant --inst-when=full-last-call --inst-no-entail --term-db-mode=relevant --random-seed=1 --lang=smt2 --tlimit 685
;(set-option :produce-unsat-cores true)
(set-logic ALL_SUPPORTED)
(declare-sort A$ 0)
(declare-sort Nat$ 0)
(declare-sort Enat_bool_fun$ 0)
(declare-sort A_llist_enat_fun$ 0)
(declare-datatypes () ((Nat_option$ (none$) (some$ (the$ Nat$)))
  (Enat$ (abs_enat$ (rep_enat$ Nat_option$)))))
(declare-codatatypes () ((A_llist$ (lNil$) (lCons$ (lhd$ A$) (ltl$ A_llist$)))))
(declare-fun n$ () Enat$)
(declare-fun xs$ () A_llist$)
(declare-fun enat$ (Nat$) Enat$)
(declare-fun less$ (Enat$) Enat_bool_fun$)
(declare-fun plus$ (Enat$ Enat$) Enat$)
(declare-fun thesis$ () Bool)
(declare-fun fun_app$ (Enat_bool_fun$ Enat$) Bool)
(declare-fun lfinite$ (A_llist$) Bool)
(declare-fun llength$ (A_llist$) Enat$)
(declare-fun fun_app$a (A_llist_enat_fun$ A_llist$) Enat$)
(declare-fun the_enat$ (Enat$) Nat$)
(declare-fun gen_llength$ (Nat$) A_llist_enat_fun$)
(assert (! (not thesis$) :named a0))
(assert (! (forall ((?v0 Nat$)) (=> (= n$ (enat$ ?v0)) thesis$)) :named a1))
(assert (! (fun_app$ (less$ n$) (llength$ xs$)) :named a2))
(assert (! (forall ((?v0 Nat$) (?v1 Nat$)) (= (= (enat$ ?v0) (enat$ ?v1)) (= ?v0 ?v1))) :named a3))
(assert (! (forall ((?v0 Enat$) (?v1 Nat$)) (=> (fun_app$ (less$ ?v0) (enat$ ?v1)) (exists ((?v2 Nat$)) (= ?v0 (enat$ ?v2))))) :named a4))
(assert (! (forall ((?v0 Nat$)) (! (= (the_enat$ (enat$ ?v0)) ?v0) :pattern ((enat$ ?v0)))) :named a5))
(assert (! (forall ((?v0 A_llist$)) (= (lfinite$ ?v0) (exists ((?v1 Nat$)) (= (llength$ ?v0) (enat$ ?v1))))) :named a6))
(assert (! (forall ((?v0 A_llist$) (?v1 Nat$)) (=> (= (llength$ ?v0) (enat$ ?v1)) (lfinite$ ?v0))) :named a7))
(assert (! (forall ((?v0 A_llist$)) (=> (lfinite$ ?v0) (exists ((?v1 Nat$)) (= (llength$ ?v0) (enat$ ?v1))))) :named a8))
(assert (! (forall ((?v0 Nat$)) (! (= (fun_app$a (gen_llength$ ?v0) lNil$) (enat$ ?v0)) :pattern ((gen_llength$ ?v0)))) :named a9))
(assert (! (forall ((?v0 Nat$) (?v1 Enat$) (?v2 Enat$)) (= (= (plus$ (enat$ ?v0) ?v1) (plus$ (enat$ ?v0) ?v2)) (= ?v1 ?v2))) :named a10))
(assert (! (forall ((?v0 Enat$) (?v1 Nat$) (?v2 Enat$)) (= (= (plus$ ?v0 (enat$ ?v1)) (plus$ ?v2 (enat$ ?v1))) (= ?v0 ?v2))) :named a11))
(assert (! (= (lfinite$ lNil$) true) :named a12))
(assert (! (forall ((?v0 Nat$) (?v1 Enat$) (?v2 Enat$)) (= (fun_app$ (less$ (plus$ (enat$ ?v0) ?v1)) (plus$ (enat$ ?v0) ?v2)) (fun_app$ (less$ ?v1) ?v2))) :named a13))
(assert (! (forall ((?v0 Enat_bool_fun$) (?v1 Enat$)) (=> (forall ((?v2 Enat$)) (=> (forall ((?v3 Enat$)) (=> (fun_app$ (less$ ?v3) ?v2) (fun_app$ ?v0 ?v3))) (fun_app$ ?v0 ?v2))) (fun_app$ ?v0 ?v1))) :named a14))
(assert (! (lfinite$ lNil$) :named a15))
(check-sat)
;(get-unsat-core)
