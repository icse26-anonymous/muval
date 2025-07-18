; --full-saturate-quant --inst-when=full-last-call --inst-no-entail --term-db-mode=relevant --random-seed=1 --lang=smt2 --tlimit 490
;(set-option :produce-unsat-cores true)
(set-logic ALL_SUPPORTED)
(declare-sort A$ 0)
(declare-sort Nat$ 0)
(declare-sort A_a_fun$ 0)
(declare-codatatypes () ((A_llist$ (lNil$) (lCons$ (lhd$ A$) (ltl$ A_llist$)))))
(declare-datatypes () ((A_list$ (nil$) (cons$ (hd$ A$) (tl$ A_list$)))
  (Nat_option$ (none$) (some$ (the$ Nat$)))
  (Enat$ (abs_enat$ (rep_enat$ Nat_option$)))))
(declare-fun x$ () A$)
(declare-fun na$ () Nat$)
(declare-fun xs$ () A_llist$)
(declare-fun suc$ (Nat$) Nat$)
(declare-fun xsa$ () A_llist$)
(declare-fun enat$ (Nat$) Enat$)
(declare-fun lmap$ (A_a_fun$ A_llist$) A_llist$)
(declare-fun lappend$ (A_llist$ A_llist$) A_llist$)
(declare-fun lfinite$ (A_llist$) Bool)
(declare-fun llength$ (A_llist$) Enat$)
(declare-fun llist_of$ (A_list$) A_llist$)
(assert (! (not (lfinite$ xsa$)) :named a0))
(assert (! (lfinite$ xs$) :named a1))
(assert (! (= xsa$ (lCons$ x$ xs$)) :named a2))
(assert (! (=> (forall ((?v0 A$) (?v1 A_llist$)) (=> (= xsa$ (lCons$ ?v0 ?v1)) false)) false) :named a3))
(assert (! (forall ((?v0 A$) (?v1 A_llist$)) (! (= (lfinite$ (lCons$ ?v0 ?v1)) (lfinite$ ?v1)) :pattern ((lCons$ ?v0 ?v1)))) :named a4))
(assert (! (forall ((?v0 A$) (?v1 A_llist$)) (! (= (lfinite$ (lCons$ ?v0 ?v1)) (lfinite$ ?v1)) :pattern ((lCons$ ?v0 ?v1)))) :named a5))
(assert (! (forall ((?v0 A_llist$) (?v1 A$)) (=> (lfinite$ ?v0) (lfinite$ (lCons$ ?v1 ?v0)))) :named a6))
(assert (! (forall ((?v0 A$) (?v1 A_llist$) (?v2 A$) (?v3 A_llist$)) (= (= (lCons$ ?v0 ?v1) (lCons$ ?v2 ?v3)) (and (= ?v0 ?v2) (= ?v1 ?v3)))) :named a7))
(assert (! (forall ((?v0 A_list$)) (lfinite$ (llist_of$ ?v0))) :named a8))
(assert (! (forall ((?v0 A_llist$) (?v1 A_llist$)) (= (lfinite$ (lappend$ ?v0 ?v1)) (and (lfinite$ ?v0) (lfinite$ ?v1)))) :named a9))
(assert (! (forall ((?v0 A_a_fun$) (?v1 A_llist$)) (= (lfinite$ (lmap$ ?v0 ?v1)) (lfinite$ ?v1))) :named a10))
(assert (! (= (lfinite$ lNil$) true) :named a11))
(assert (! (forall ((?v0 A_llist$)) (= (lfinite$ (ltl$ ?v0)) (lfinite$ ?v0))) :named a12))
(assert (! (forall ((?v0 A_llist$) (?v1 A_llist$)) (! (=> (not (lfinite$ ?v0)) (= (lappend$ ?v0 ?v1) ?v0)) :pattern ((lappend$ ?v0 ?v1)))) :named a13))
(assert (! (forall ((?v0 A_llist$)) (=> (= (llength$ ?v0) (enat$ na$)) (lfinite$ ?v0))) :named a14))
(assert (! (= (llength$ xsa$) (enat$ (suc$ na$))) :named a15))
(assert (! (forall ((?v0 A_list$) (?v1 A_list$)) (= (= (llist_of$ ?v0) (llist_of$ ?v1)) (= ?v0 ?v1))) :named a16))
(assert (! (= (llength$ xs$) (enat$ na$)) :named a17))
(check-sat)
;(get-unsat-core)
