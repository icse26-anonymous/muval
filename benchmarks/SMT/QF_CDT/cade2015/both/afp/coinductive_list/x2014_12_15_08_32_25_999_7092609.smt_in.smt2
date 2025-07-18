; --full-saturate-quant --inst-when=full-last-call --inst-no-entail --term-db-mode=relevant --random-seed=1 --lang=smt2 --tlimit 642
;(set-option :produce-unsat-cores true)
(set-logic ALL_SUPPORTED)
(declare-sort A$ 0)
(declare-sort Nat$ 0)
(declare-sort Nat_set$ 0)
(declare-sort Nat_nat_fun$ 0)
(declare-sort Nat_enat_fun$ 0)
(declare-datatypes () ((Nat_option$ (none$) (some$ (the$ Nat$)))
  (Enat$ (abs_enat$ (rep_enat$ Nat_option$)))))
(declare-codatatypes () ((A_llist$ (lNil$) (lCons$ (lhd$ A$) (ltl$ A_llist$)))
  (A_llist_llist$ (lNil$a) (lCons$a (lhd$a A_llist$) (ltl$a A_llist_llist$)))))
(declare-fun na$ () Nat$)
(declare-fun uu$ () Nat_enat_fun$)
(declare-fun xs$ () A_llist$)
(declare-fun one$ () Nat$)
(declare-fun suc$ (Nat$) Nat$)
(declare-fun uua$ () Nat_nat_fun$)
(declare-fun uub$ () Nat_enat_fun$)
(declare-fun uuc$ (Nat_nat_fun$) Nat_nat_fun$)
(declare-fun uud$ (Nat_enat_fun$) Nat_enat_fun$)
(declare-fun uue$ () Nat_enat_fun$)
(declare-fun uuf$ () Nat_enat_fun$)
(declare-fun xss$ () A_llist_llist$)
(declare-fun lnth$ (A_llist_llist$ Nat$) A_llist$)
(declare-fun plus$ (Enat$ Enat$) Enat$)
(declare-fun xssa$ () A_llist_llist$)
(declare-fun zero$ () Enat$)
(declare-fun plus$a (Nat$) Nat_nat_fun$)
(declare-fun zero$a () Nat$)
(declare-fun setsum$ (Nat_enat_fun$ Nat_set$) Enat$)
(declare-fun fun_app$ (Nat_enat_fun$ Nat$) Enat$)
(declare-fun llength$ (A_llist$) Enat$)
(declare-fun setsum$a (Nat_nat_fun$ Nat_set$) Nat$)
(declare-fun fun_app$a (Nat_nat_fun$ Nat$) Nat$)
(declare-fun lessThan$ (Nat$) Nat_set$)
(declare-fun atLeastLessThan$ (Nat$ Nat$) Nat_set$)
(assert (! (forall ((?v0 Nat$)) (! (= (fun_app$ uu$ ?v0) (llength$ (lnth$ (lCons$a xs$ xss$) ?v0))) :pattern ((fun_app$ uu$ ?v0)))) :named a0))
(assert (! (forall ((?v0 Nat$)) (! (= (fun_app$ uuf$ ?v0) (llength$ (lnth$ xssa$ ?v0))) :pattern ((fun_app$ uuf$ ?v0)))) :named a1))
(assert (! (forall ((?v0 Nat$)) (! (= (fun_app$ uue$ ?v0) (llength$ (lnth$ xss$ ?v0))) :pattern ((fun_app$ uue$ ?v0)))) :named a2))
(assert (! (forall ((?v0 Nat_enat_fun$) (?v1 Nat$)) (! (= (fun_app$ (uud$ ?v0) ?v1) (fun_app$ ?v0 (suc$ ?v1))) :pattern ((fun_app$ (uud$ ?v0) ?v1)))) :named a3))
(assert (! (forall ((?v0 Nat_nat_fun$) (?v1 Nat$)) (! (= (fun_app$a (uuc$ ?v0) ?v1) (fun_app$a ?v0 (suc$ ?v1))) :pattern ((fun_app$a (uuc$ ?v0) ?v1)))) :named a4))
(assert (! (forall ((?v0 Nat$)) (! (= (fun_app$ uub$ ?v0) zero$) :pattern ((fun_app$ uub$ ?v0)))) :named a5))
(assert (! (forall ((?v0 Nat$)) (! (= (fun_app$a uua$ ?v0) zero$a) :pattern ((fun_app$a uua$ ?v0)))) :named a6))
(assert (! (not (= (plus$ (llength$ xs$) (setsum$ uu$ (atLeastLessThan$ one$ (suc$ na$)))) (setsum$ uu$ (atLeastLessThan$ zero$a (suc$ na$))))) :named a7))
(assert (! (forall ((?v0 A_llist$) (?v1 A_llist_llist$) (?v2 A_llist$) (?v3 A_llist_llist$)) (= (= (lCons$a ?v0 ?v1) (lCons$a ?v2 ?v3)) (and (= ?v0 ?v2) (= ?v1 ?v3)))) :named a8))
(assert (! (= xssa$ (lCons$a xs$ xss$)) :named a9))
(assert (! (forall ((?v0 A_llist$) (?v1 A_llist_llist$)) (! (= (lnth$ (lCons$a ?v0 ?v1) zero$a) ?v0) :pattern ((lCons$a ?v0 ?v1)))) :named a10))
(assert (! (forall ((?v0 A_llist$) (?v1 A_llist_llist$) (?v2 Nat$)) (! (= (lnth$ (lCons$a ?v0 ?v1) (suc$ ?v2)) (lnth$ ?v1 ?v2)) :pattern ((lnth$ (lCons$a ?v0 ?v1) (suc$ ?v2))))) :named a11))
(assert (! (forall ((?v0 Nat_set$)) (= (setsum$a uua$ ?v0) zero$a)) :named a12))
(assert (! (forall ((?v0 Nat_set$)) (= (setsum$ uub$ ?v0) zero$)) :named a13))
(assert (! (forall ((?v0 Nat_nat_fun$) (?v1 Nat$)) (=> (= (fun_app$a ?v0 zero$a) zero$a) (= (setsum$a ?v0 (atLeastLessThan$ (suc$ zero$a) ?v1)) (setsum$a ?v0 (atLeastLessThan$ zero$a ?v1))))) :named a14))
(assert (! (forall ((?v0 Nat_enat_fun$) (?v1 Nat$)) (=> (= (fun_app$ ?v0 zero$a) zero$) (= (setsum$ ?v0 (atLeastLessThan$ (suc$ zero$a) ?v1)) (setsum$ ?v0 (atLeastLessThan$ zero$a ?v1))))) :named a15))
(assert (! (forall ((?v0 Enat$)) (= (plus$ ?v0 zero$) ?v0)) :named a16))
(assert (! (forall ((?v0 Nat$)) (= (fun_app$a (plus$a ?v0) zero$a) ?v0)) :named a17))
(assert (! (forall ((?v0 Enat$)) (= (plus$ ?v0 zero$) ?v0)) :named a18))
(assert (! (forall ((?v0 Nat$)) (= (fun_app$a (plus$a ?v0) zero$a) ?v0)) :named a19))
(assert (! (forall ((?v0 Enat$)) (= (plus$ zero$ ?v0) ?v0)) :named a20))
(assert (! (forall ((?v0 Nat$)) (= (fun_app$a (plus$a zero$a) ?v0) ?v0)) :named a21))
(assert (! (forall ((?v0 Enat$)) (= (plus$ zero$ ?v0) ?v0)) :named a22))
(assert (! (forall ((?v0 Nat$)) (= (fun_app$a (plus$a zero$a) ?v0) ?v0)) :named a23))
(assert (! (forall ((?v0 Nat_nat_fun$) (?v1 Nat$) (?v2 Nat$)) (= (setsum$a ?v0 (atLeastLessThan$ (suc$ ?v1) (suc$ ?v2))) (setsum$a (uuc$ ?v0) (atLeastLessThan$ ?v1 ?v2)))) :named a24))
(assert (! (forall ((?v0 Nat_enat_fun$) (?v1 Nat$) (?v2 Nat$)) (= (setsum$ ?v0 (atLeastLessThan$ (suc$ ?v1) (suc$ ?v2))) (setsum$ (uud$ ?v0) (atLeastLessThan$ ?v1 ?v2)))) :named a25))
(assert (! (= (setsum$ uue$ (lessThan$ na$)) (setsum$ uuf$ (atLeastLessThan$ one$ (suc$ na$)))) :named a26))
(assert (! (= one$ (suc$ zero$a)) :named a27))
(assert (! (forall ((?v0 Nat$) (?v1 Nat$)) (= (= (suc$ ?v0) (suc$ ?v1)) (= ?v0 ?v1))) :named a28))
(check-sat)
;(get-unsat-core)
