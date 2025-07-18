; --full-saturate-quant --inst-when=full-last-call --inst-no-entail --term-db-mode=relevant --random-seed=1 --lang=smt2 --tlimit 616
;(set-option :produce-unsat-cores true)
(set-logic ALL_SUPPORTED)
(declare-sort A$ 0)
(declare-sort Nat$ 0)
(declare-sort A_set$ 0)
(declare-sort A_a_fun$ 0)
(declare-sort A_llist_a_llist_fun$ 0)
(declare-codatatypes () ((A_llist$ (lNil$) (lCons$ (lhd$ A$) (ltl$ A_llist$)))))
(declare-datatypes () ((Nat_option$ (none$) (some$ (the$ Nat$)))
  (Enat$ (abs_enat$ (rep_enat$ Nat_option$)))
  (A_list$ (nil$) (cons$ (hd$ A$) (tl$ A_list$)))))
(declare-fun us$ () A_llist$)
(declare-fun vs$ () A_llist$)
(declare-fun xs$ () A_llist$)
(declare-fun ys$ () A_llist$)
(declare-fun lmap$ (A_a_fun$ A_llist$) A_llist$)
(declare-fun lset$ (A_llist$) A_set$)
(declare-fun lnull$ (A_llist$) Bool)
(declare-fun ldropn$ (Nat$ A_llist$) A_llist$)
(declare-fun member$ (A$ A_set$) Bool)
(declare-fun fun_app$ (A_llist_a_llist_fun$ A_llist$) A_llist$)
(declare-fun lappend$ (A_llist$) A_llist_a_llist_fun$)
(declare-fun lfinite$ (A_llist$) Bool)
(declare-fun llength$ (A_llist$) Enat$)
(declare-fun lprefix$ (A_llist$ A_llist$) Bool)
(declare-fun llist_of$ (A_list$) A_llist$)
(assert (! (not (= (= (fun_app$ (lappend$ xs$) ys$) (fun_app$ (lappend$ us$) vs$)) (and (= xs$ us$) (=> (lfinite$ xs$) (= ys$ vs$))))) :named a0))
(assert (! (forall ((?v0 A_llist$) (?v1 A_llist$)) (= (lfinite$ (fun_app$ (lappend$ ?v0) ?v1)) (and (lfinite$ ?v0) (lfinite$ ?v1)))) :named a1))
(assert (! (= (llength$ xs$) (llength$ us$)) :named a2))
(assert (! (forall ((?v0 A_llist$) (?v1 A_llist$) (?v2 A_llist$)) (= (fun_app$ (lappend$ (fun_app$ (lappend$ ?v0) ?v1)) ?v2) (fun_app$ (lappend$ ?v0) (fun_app$ (lappend$ ?v1) ?v2)))) :named a3))
(assert (! (forall ((?v0 A_llist$) (?v1 A_llist$)) (! (=> (not (lfinite$ ?v0)) (= (fun_app$ (lappend$ ?v0) ?v1) ?v0)) :pattern ((fun_app$ (lappend$ ?v0) ?v1)))) :named a4))
(assert (! (forall ((?v0 A_llist$) (?v1 A_llist$) (?v2 A_llist$)) (= (lprefix$ (fun_app$ (lappend$ ?v0) ?v1) (fun_app$ (lappend$ ?v0) ?v2)) (=> (lfinite$ ?v0) (lprefix$ ?v1 ?v2)))) :named a5))
(assert (! (forall ((?v0 A$) (?v1 A_llist$) (?v2 A_llist$)) (= (member$ ?v0 (lset$ (fun_app$ (lappend$ ?v1) ?v2))) (or (member$ ?v0 (lset$ ?v1)) (and (lfinite$ ?v1) (member$ ?v0 (lset$ ?v2)))))) :named a6))
(assert (! (forall ((?v0 Nat$) (?v1 A_llist$)) (= (lfinite$ (ldropn$ ?v0 ?v1)) (lfinite$ ?v1))) :named a7))
(assert (! (forall ((?v0 A_list$)) (lfinite$ (llist_of$ ?v0))) :named a8))
(assert (! (= (lfinite$ lNil$) true) :named a9))
(assert (! (forall ((?v0 A_llist$)) (! (= (fun_app$ (lappend$ ?v0) lNil$) ?v0) :pattern ((lappend$ ?v0)))) :named a10))
(assert (! (forall ((?v0 A_llist$)) (! (= (fun_app$ (lappend$ lNil$) ?v0) ?v0) :pattern ((fun_app$ (lappend$ lNil$) ?v0)))) :named a11))
(assert (! (forall ((?v0 A_a_fun$) (?v1 A_llist$)) (= (lfinite$ (lmap$ ?v0 ?v1)) (lfinite$ ?v1))) :named a12))
(assert (! (forall ((?v0 A_llist$) (?v1 A_llist$)) (= (not (lnull$ (fun_app$ (lappend$ ?v0) ?v1))) (or (not (lnull$ ?v0)) (not (lnull$ ?v1))))) :named a13))
(assert (! (forall ((?v0 A_llist$) (?v1 A_llist$)) (= (lnull$ (fun_app$ (lappend$ ?v0) ?v1)) (and (lnull$ ?v0) (lnull$ ?v1)))) :named a14))
(assert (! (forall ((?v0 A$) (?v1 A_llist$)) (! (= (lfinite$ (lCons$ ?v0 ?v1)) (lfinite$ ?v1)) :pattern ((lCons$ ?v0 ?v1)))) :named a15))
(assert (! (forall ((?v0 A$) (?v1 A_llist$)) (! (= (lfinite$ (lCons$ ?v0 ?v1)) (lfinite$ ?v1)) :pattern ((lCons$ ?v0 ?v1)))) :named a16))
(assert (! (forall ((?v0 A_llist$)) (lprefix$ ?v0 ?v0)) :named a17))
(check-sat)
;(get-unsat-core)
