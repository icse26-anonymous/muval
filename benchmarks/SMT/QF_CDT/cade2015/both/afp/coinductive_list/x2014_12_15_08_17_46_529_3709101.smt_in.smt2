; --full-saturate-quant --inst-when=full-last-call --inst-no-entail --term-db-mode=relevant --random-seed=1 --lang=smt2 --tlimit 665
;(set-option :produce-unsat-cores true)
(set-logic ALL_SUPPORTED)
(declare-sort A$ 0)
(declare-sort Nat$ 0)
(declare-sort A_a_fun$ 0)
(declare-sort A_llist_a_llist_fun$ 0)
(declare-codatatypes () ((A_llist$ (lNil$) (lCons$ (lhd$ A$) (ltl$ A_llist$)))))
(declare-datatypes () ((Nat_option$ (none$) (some$ (the$ Nat$)))
  (Enat$ (abs_enat$ (rep_enat$ Nat_option$)))
  (A_list$ (nil$) (cons$ (hd$ A$) (tl$ A_list$)))))
(declare-fun n$ () Nat$)
(declare-fun xs$ () A_list$)
(declare-fun drop$ (Nat$ A_list$) A_list$)
(declare-fun enat$ (Nat$) Enat$)
(declare-fun lmap$ (A_a_fun$ A_llist$) A_llist$)
(declare-fun plus$ (Enat$ Enat$) Enat$)
(declare-fun size$ (A_list$) Nat$)
(declare-fun zero$ () Enat$)
(declare-fun ldrop$ (Enat$) A_llist_a_llist_fun$)
(declare-fun ldropn$ (Nat$) A_llist_a_llist_fun$)
(declare-fun fun_app$ (A_llist_a_llist_fun$ A_llist$) A_llist$)
(declare-fun lfinite$ (A_llist$) Bool)
(declare-fun list_of$ (A_llist$) A_list$)
(declare-fun llength$ (A_llist$) Enat$)
(declare-fun llist_of$ (A_list$) A_llist$)
(assert (! (not (= (fun_app$ (ldrop$ (enat$ n$)) (llist_of$ xs$)) (llist_of$ (drop$ n$ xs$)))) :named a0))
(assert (! (forall ((?v0 A_list$) (?v1 A_list$)) (= (= (llist_of$ ?v0) (llist_of$ ?v1)) (= ?v0 ?v1))) :named a1))
(assert (! (forall ((?v0 Nat$) (?v1 Nat$)) (= (= (enat$ ?v0) (enat$ ?v1)) (= ?v0 ?v1))) :named a2))
(assert (! (forall ((?v0 Nat$) (?v1 A_list$)) (= (fun_app$ (ldropn$ ?v0) (llist_of$ ?v1)) (llist_of$ (drop$ ?v0 ?v1)))) :named a3))
(assert (! (forall ((?v0 Nat$) (?v1 A_llist$)) (! (= (fun_app$ (ldrop$ (enat$ ?v0)) ?v1) (fun_app$ (ldropn$ ?v0) ?v1)) :pattern ((fun_app$ (ldrop$ (enat$ ?v0)) ?v1)))) :named a4))
(assert (! (forall ((?v0 A_list$)) (= (list_of$ (llist_of$ ?v0)) ?v0)) :named a5))
(assert (! (forall ((?v0 A_llist$)) (= (fun_app$ (ldrop$ zero$) ?v0) ?v0)) :named a6))
(assert (! (forall ((?v0 Enat$) (?v1 Enat$) (?v2 A_llist$)) (= (fun_app$ (ldrop$ ?v0) (fun_app$ (ldrop$ ?v1) ?v2)) (fun_app$ (ldrop$ (plus$ ?v0 ?v1)) ?v2))) :named a7))
(assert (! (forall ((?v0 Enat$)) (! (= (fun_app$ (ldrop$ ?v0) lNil$) lNil$) :pattern ((ldrop$ ?v0)))) :named a8))
(assert (! (forall ((?v0 Enat$) (?v1 A_a_fun$) (?v2 A_llist$)) (= (fun_app$ (ldrop$ ?v0) (lmap$ ?v1 ?v2)) (lmap$ ?v1 (fun_app$ (ldrop$ ?v0) ?v2)))) :named a9))
(assert (! (forall ((?v0 A_list$)) (lfinite$ (llist_of$ ?v0))) :named a10))
(assert (! (forall ((?v0 A_list$)) (= (llength$ (llist_of$ ?v0)) (enat$ (size$ ?v0)))) :named a11))
(assert (! (= (lfinite$ lNil$) true) :named a12))
(assert (! (forall ((?v0 Nat$)) (! (= (fun_app$ (ldropn$ ?v0) lNil$) lNil$) :pattern ((ldropn$ ?v0)))) :named a13))
(assert (! (forall ((?v0 A_a_fun$) (?v1 A_llist$)) (= (lfinite$ (lmap$ ?v0 ?v1)) (lfinite$ ?v1))) :named a14))
(assert (! (forall ((?v0 A_a_fun$) (?v1 A_llist$)) (= (llength$ (lmap$ ?v0 ?v1)) (llength$ ?v1))) :named a15))
(check-sat)
;(get-unsat-core)
