; --full-saturate-quant --inst-when=full-last-call --inst-no-entail --term-db-mode=relevant --random-seed=1 --lang=smt2 --tlimit 523
;(set-option :produce-unsat-cores true)
(set-logic ALL_SUPPORTED)
(declare-sort A$ 0)
(declare-sort Nat$ 0)
(declare-codatatypes () ((A_llist$ (lNil$) (lCons$ (lhd$ A$) (ltl$ A_llist$)))))
(declare-datatypes () ((Nat_option$ (none$) (some$ (the$ Nat$)))
  (Enat$ (abs_enat$ (rep_enat$ Nat_option$)))
  (A_list$ (nil$) (cons$ (hd$ A$) (tl$ A_list$)))))
(declare-fun na$ () Nat$)
(declare-fun suc$ (Nat$) Nat$)
(declare-fun xsa$ () A_list$)
(declare-fun eSuc$ (Enat$) Enat$)
(declare-fun enat$ (Nat$) Enat$)
(declare-fun take$ (Nat$ A_list$) A_list$)
(declare-fun ltake$ (Enat$ A_llist$) A_llist$)
(declare-fun llist_of$ (A_list$) A_llist$)
(assert (! (not (= (ltake$ (eSuc$ (enat$ na$)) (llist_of$ xsa$)) (llist_of$ (take$ (suc$ na$) xsa$)))) :named a0))
(assert (! (forall ((?v0 A_list$)) (= (ltake$ (enat$ na$) (llist_of$ ?v0)) (llist_of$ (take$ na$ ?v0)))) :named a1))
(assert (! (forall ((?v0 A_list$) (?v1 A_list$)) (= (= (llist_of$ ?v0) (llist_of$ ?v1)) (= ?v0 ?v1))) :named a2))
(assert (! (forall ((?v0 Enat$) (?v1 Nat$)) (= (= (eSuc$ ?v0) (enat$ ?v1)) (exists ((?v2 Nat$)) (and (= ?v1 (suc$ ?v2)) (= ?v0 (enat$ ?v2)))))) :named a3))
(assert (! (forall ((?v0 Nat$) (?v1 Enat$)) (= (= (enat$ ?v0) (eSuc$ ?v1)) (exists ((?v2 Nat$)) (and (= ?v0 (suc$ ?v2)) (= (enat$ ?v2) ?v1))))) :named a4))
(assert (! (forall ((?v0 Nat$)) (= (eSuc$ (enat$ ?v0)) (enat$ (suc$ ?v0)))) :named a5))
(assert (! (forall ((?v0 Nat$) (?v1 Nat$)) (= (= (enat$ ?v0) (enat$ ?v1)) (= ?v0 ?v1))) :named a6))
(assert (! (forall ((?v0 Enat$) (?v1 Enat$)) (= (= (eSuc$ ?v0) (eSuc$ ?v1)) (= ?v0 ?v1))) :named a7))
(assert (! (forall ((?v0 Enat$) (?v1 Enat$)) (= (= (eSuc$ ?v0) (eSuc$ ?v1)) (= ?v0 ?v1))) :named a8))
(assert (! (forall ((?v0 Nat$) (?v1 Nat$)) (= (= (suc$ ?v0) (suc$ ?v1)) (= ?v0 ?v1))) :named a9))
(assert (! (forall ((?v0 Nat$) (?v1 Nat$)) (= (= (suc$ ?v0) (suc$ ?v1)) (= ?v0 ?v1))) :named a10))
(assert (! (forall ((?v0 A_list$) (?v1 A_list$)) (=> (forall ((?v2 Nat$)) (= (take$ ?v2 ?v0) (take$ ?v2 ?v1))) (= ?v0 ?v1))) :named a11))
(assert (! (forall ((?v0 Nat$) (?v1 Nat$)) (=> (= (suc$ ?v0) (suc$ ?v1)) (= ?v0 ?v1))) :named a12))
(assert (! (forall ((?v0 Nat$)) (not (= ?v0 (suc$ ?v0)))) :named a13))
(check-sat)
;(get-unsat-core)
