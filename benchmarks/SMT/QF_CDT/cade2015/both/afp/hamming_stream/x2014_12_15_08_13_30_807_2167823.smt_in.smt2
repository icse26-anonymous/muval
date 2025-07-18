; --full-saturate-quant --inst-when=full-last-call --inst-no-entail --term-db-mode=relevant --random-seed=1 --lang=smt2 --tlimit 543
;(set-option :produce-unsat-cores true)
(set-logic ALL_SUPPORTED)
(declare-sort Nat$ 0)
(declare-sort Nat_llist_nat_llist_fun$ 0)
(declare-codatatypes () ((Nat_llist$ (lNil$) (lCons$ (lhd$ Nat$) (ltl$ Nat_llist$)))))
(declare-fun zero$ () Nat$)
(declare-fun lnull$ (Nat_llist$) Bool)
(declare-fun times$ (Nat$ Nat$) Nat$)
(declare-fun lmerge$ (Nat_llist$) Nat_llist_nat_llist_fun$)
(declare-fun smooth$ (Nat$) Bool)
(declare-fun fun_app$ (Nat_llist_nat_llist_fun$ Nat_llist$) Nat_llist$)
(declare-fun hamming$ () Nat_llist$)
(declare-fun lfinite$ (Nat_llist$) Bool)
(assert (! (not false) :named a0))
(assert (! (lfinite$ hamming$) :named a1))
(assert (! (forall ((?v0 Nat_llist$) (?v1 Nat_llist$)) (=> (and (=> (or (lnull$ ?v0) (lnull$ ?v1)) false) (=> (and (not (lnull$ ?v0)) (not (lnull$ ?v1))) false)) false)) :named a2))
(assert (! (forall ((?v0 Nat_llist$) (?v1 Nat_llist$)) (=> (and (=> (or (lnull$ ?v0) (lnull$ ?v1)) false) (=> (and (not (lnull$ ?v0)) (not (lnull$ ?v1))) false)) false)) :named a3))
(assert (! (forall ((?v0 Nat_llist$) (?v1 Nat_llist$)) (=> (and (=> (or (lnull$ ?v0) (lnull$ ?v1)) false) (=> (and (not (lnull$ ?v0)) (not (lnull$ ?v1))) false)) false)) :named a4))
(assert (! (forall ((?v0 Nat$) (?v1 Nat$)) (= (smooth$ (times$ ?v0 ?v1)) (and (smooth$ ?v0) (smooth$ ?v1)))) :named a5))
(assert (! (not (smooth$ zero$)) :named a6))
(assert (! (= (= hamming$ lNil$) false) :named a7))
(assert (! (forall ((?v0 Nat_llist$)) (! (= (fun_app$ (lmerge$ ?v0) lNil$) lNil$) :pattern ((lmerge$ ?v0)))) :named a8))
(assert (! (forall ((?v0 Nat_llist$)) (! (= (fun_app$ (lmerge$ lNil$) ?v0) lNil$) :pattern ((fun_app$ (lmerge$ lNil$) ?v0)))) :named a9))
(assert (! (forall ((?v0 Nat_llist$) (?v1 Nat_llist$)) (= (not (lnull$ (fun_app$ (lmerge$ ?v0) ?v1))) (and (not (lnull$ ?v0)) (not (lnull$ ?v1))))) :named a10))
(assert (! (forall ((?v0 Nat_llist$) (?v1 Nat_llist$)) (= (lnull$ (fun_app$ (lmerge$ ?v0) ?v1)) (or (lnull$ ?v0) (lnull$ ?v1)))) :named a11))
(assert (! (forall ((?v0 Nat_llist$) (?v1 Nat_llist$)) (= (= (fun_app$ (lmerge$ ?v0) ?v1) lNil$) (or (= ?v0 lNil$) (= ?v1 lNil$)))) :named a12))
(assert (! (forall ((?v0 Nat_llist$) (?v1 Nat_llist$)) (! (=> (or (lnull$ ?v0) (lnull$ ?v1)) (= (fun_app$ (lmerge$ ?v0) ?v1) lNil$)) :pattern ((fun_app$ (lmerge$ ?v0) ?v1)))) :named a13))
(assert (! (forall ((?v0 Nat_llist$) (?v1 Nat_llist$)) (=> (or (lnull$ ?v0) (lnull$ ?v1)) (lnull$ (fun_app$ (lmerge$ ?v0) ?v1)))) :named a14))
(assert (! (forall ((?v0 Nat_llist$) (?v1 Nat_llist$)) (=> (and (not (lfinite$ ?v0)) (not (lfinite$ ?v1))) (not (lfinite$ (fun_app$ (lmerge$ ?v0) ?v1))))) :named a15))
(assert (! (forall ((?v0 Nat_llist$) (?v1 Nat_llist$)) (=> (and (not (lnull$ ?v0)) (not (lnull$ ?v1))) (not (lnull$ (fun_app$ (lmerge$ ?v0) ?v1))))) :named a16))
(check-sat)
;(get-unsat-core)
