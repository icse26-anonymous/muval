; --full-saturate-quant --inst-when=full-last-call --inst-no-entail --term-db-mode=relevant --random-seed=1 --lang=smt2 --tlimit 702
;(set-option :produce-unsat-cores true)
(set-logic ALL_SUPPORTED)
(declare-sort A$ 0)
(declare-sort Nat$ 0)
(declare-sort Enat_bool_fun$ 0)
(declare-sort Enat_enat_fun$ 0)
(declare-sort Enat_enat_bool_fun_fun$ 0)
(declare-datatypes () ((Nat_option$ (none$) (some$ (the$ Nat$)))
  (Enat$ (abs_enat$ (rep_enat$ Nat_option$)))))
(declare-codatatypes () ((A_llist$ (lNil$) (lCons$ (lhd$ A$) (ltl$ A_llist$)))))
(declare-fun xs$ () A_llist$)
(declare-fun ys$ () A_llist$)
(declare-fun less$ (Enat$ Enat$) Bool)
(declare-fun fun_app$ (Enat_bool_fun$ Enat$) Bool)
(declare-fun less_eq$ (Enat$ Enat$) Bool)
(declare-fun llength$ (A_llist$) Enat$)
(declare-fun lprefix$ (A_llist$ A_llist$) Bool)
(declare-fun fun_app$a (Enat_enat_bool_fun_fun$ Enat$) Enat_bool_fun$)
(declare-fun fun_app$b (Enat_enat_fun$ Enat$) Enat$)
(declare-fun lstrict_prefix$ (A_llist$ A_llist$) Bool)
(assert (! (not (less_eq$ (llength$ xs$) (llength$ ys$))) :named a0))
(assert (! (lprefix$ xs$ ys$) :named a1))
(assert (! (lstrict_prefix$ xs$ ys$) :named a2))
(assert (! (not (= xs$ ys$)) :named a3))
(assert (! (not (less$ (llength$ xs$) (llength$ ys$))) :named a4))
(assert (! (forall ((?v0 Enat_enat_bool_fun_fun$) (?v1 Enat$) (?v2 Enat$)) (=> (and (forall ((?v3 Enat$) (?v4 Enat$)) (=> (less_eq$ ?v3 ?v4) (fun_app$ (fun_app$a ?v0 ?v3) ?v4))) (=> (fun_app$ (fun_app$a ?v0 ?v1) ?v2) (fun_app$ (fun_app$a ?v0 ?v2) ?v1))) (fun_app$ (fun_app$a ?v0 ?v2) ?v1))) :named a5))
(assert (! (forall ((?v0 A_llist$) (?v1 A_llist$)) (=> (lprefix$ ?v0 ?v1) (less_eq$ (llength$ ?v0) (llength$ ?v1)))) :named a6))
(assert (! (forall ((?v0 Enat$)) (less_eq$ ?v0 ?v0)) :named a7))
(assert (! (forall ((?v0 A_llist$) (?v1 A_llist$)) (=> (and (lprefix$ ?v0 ?v1) (= (llength$ ?v0) (llength$ ?v1))) (= ?v0 ?v1))) :named a8))
(assert (! (forall ((?v0 A_llist$)) (lprefix$ ?v0 ?v0)) :named a9))
(assert (! (forall ((?v0 A_llist$)) (lprefix$ ?v0 ?v0)) :named a10))
(assert (! (forall ((?v0 Enat$) (?v1 Enat$)) (= (= ?v0 ?v1) (and (less_eq$ ?v0 ?v1) (less_eq$ ?v1 ?v0)))) :named a11))
(assert (! (forall ((?v0 Enat$) (?v1 Enat$)) (=> (and (=> (less_eq$ ?v0 ?v1) false) (=> (less_eq$ ?v1 ?v0) false)) false)) :named a12))
(assert (! (forall ((?v0 Enat_enat_bool_fun_fun$) (?v1 Enat$) (?v2 Enat$)) (=> (and (forall ((?v3 Enat$) (?v4 Enat$)) (=> (less_eq$ ?v3 ?v4) (fun_app$ (fun_app$a ?v0 ?v3) ?v4))) (forall ((?v3 Enat$) (?v4 Enat$)) (=> (fun_app$ (fun_app$a ?v0 ?v4) ?v3) (fun_app$ (fun_app$a ?v0 ?v3) ?v4)))) (fun_app$ (fun_app$a ?v0 ?v1) ?v2))) :named a13))
(assert (! (forall ((?v0 Enat$) (?v1 Enat_enat_fun$) (?v2 Enat$) (?v3 Enat$)) (=> (and (= ?v0 (fun_app$b ?v1 ?v2)) (and (less_eq$ ?v2 ?v3) (forall ((?v4 Enat$) (?v5 Enat$)) (=> (less_eq$ ?v4 ?v5) (less_eq$ (fun_app$b ?v1 ?v4) (fun_app$b ?v1 ?v5)))))) (less_eq$ ?v0 (fun_app$b ?v1 ?v3)))) :named a14))
(assert (! (forall ((?v0 Enat$) (?v1 Enat$) (?v2 Enat$)) (=> (and (= ?v0 ?v1) (less_eq$ ?v1 ?v2)) (less_eq$ ?v0 ?v2))) :named a15))
(check-sat)
;(get-unsat-core)
