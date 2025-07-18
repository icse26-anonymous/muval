; --full-saturate-quant --inst-when=full-last-call --inst-no-entail --term-db-mode=relevant --random-seed=1 --lang=smt2 --tlimit 635
;(set-option :produce-unsat-cores true)
(set-logic ALL_SUPPORTED)
(declare-sort A$ 0)
(declare-sort Nat$ 0)
(declare-sort A_a_fun$ 0)
(declare-sort A_a_fun_a_a_fun_fun$ 0)
(declare-sort A_llist_a_llist_fun$ 0)
(declare-sort Nat_a_a_fun_a_a_fun_fun_fun$ 0)
(declare-sort A_llist_a_llist_fun_a_llist_a_llist_fun_fun$ 0)
(declare-sort Nat_a_llist_a_llist_fun_a_llist_a_llist_fun_fun_fun$ 0)
(declare-codatatypes () ((A_llist$ (lNil$) (lCons$ (lhd$ A$) (ltl$ A_llist$)))))
(declare-datatypes () ((Nat_option$ (none$) (some$ (the$ Nat$)))
  (Enat$ (abs_enat$ (rep_enat$ Nat_option$)))))
(declare-codatatypes () ((A_llist_llist$ (lNil$a) (lCons$a (lhd$a A_llist$) (ltl$a A_llist_llist$)))))
(declare-fun f$ () A_a_fun$)
(declare-fun n$ () Nat$)
(declare-fun x$ () A$)
(declare-fun enat$ (Nat$) Enat$)
(declare-fun lmap$ (A_a_fun$) A_llist_a_llist_fun$)
(declare-fun plus$ (Enat$ Enat$) Enat$)
(declare-fun zero$ () Enat$)
(declare-fun ldrop$ (Enat$) A_llist_a_llist_fun$)
(declare-fun lnull$ (A_llist$) Bool)
(declare-fun compow$ () Nat_a_a_fun_a_a_fun_fun_fun$)
(declare-fun funpow$ () Nat_a_llist_a_llist_fun_a_llist_a_llist_fun_fun_fun$)
(declare-fun ldropn$ (Nat$ A_llist_llist$) A_llist_llist$)
(declare-fun compow$a () Nat_a_llist_a_llist_fun_a_llist_a_llist_fun_fun_fun$)
(declare-fun fun_app$ (A_llist_a_llist_fun$ A_llist$) A_llist$)
(declare-fun funpow$a () Nat_a_a_fun_a_a_fun_fun_fun$)
(declare-fun ldropn$a (Nat$) A_llist_a_llist_fun$)
(declare-fun fun_app$a (A_a_fun$ A$) A$)
(declare-fun fun_app$b (A_a_fun_a_a_fun_fun$ A_a_fun$) A_a_fun$)
(declare-fun fun_app$c (Nat_a_a_fun_a_a_fun_fun_fun$ Nat$) A_a_fun_a_a_fun_fun$)
(declare-fun fun_app$d (A_llist_a_llist_fun_a_llist_a_llist_fun_fun$ A_llist_a_llist_fun$) A_llist_a_llist_fun$)
(declare-fun fun_app$e (Nat_a_llist_a_llist_fun_a_llist_a_llist_fun_fun_fun$ Nat$) A_llist_a_llist_fun_a_llist_a_llist_fun_fun$)
(declare-fun iterates$ (A_a_fun$ A$) A_llist$)
(declare-fun iterates$a (A_llist_a_llist_fun$ A_llist$) A_llist_llist$)
(assert (! (not (= (fun_app$ (ldrop$ (enat$ n$)) (iterates$ f$ x$)) (iterates$ f$ (fun_app$a (fun_app$b (fun_app$c compow$ n$) f$) x$)))) :named a0))
(assert (! (forall ((?v0 Nat$) (?v1 Nat$)) (= (= (enat$ ?v0) (enat$ ?v1)) (= ?v0 ?v1))) :named a1))
(assert (! (forall ((?v0 A_llist_a_llist_fun$) (?v1 Nat$) (?v2 A_llist$)) (= (fun_app$ ?v0 (fun_app$ (fun_app$d (fun_app$e compow$a ?v1) ?v0) ?v2)) (fun_app$ (fun_app$d (fun_app$e compow$a ?v1) ?v0) (fun_app$ ?v0 ?v2)))) :named a2))
(assert (! (forall ((?v0 A_a_fun$) (?v1 Nat$) (?v2 A$)) (= (fun_app$a ?v0 (fun_app$a (fun_app$b (fun_app$c compow$ ?v1) ?v0) ?v2)) (fun_app$a (fun_app$b (fun_app$c compow$ ?v1) ?v0) (fun_app$a ?v0 ?v2)))) :named a3))
(assert (! (forall ((?v0 Nat$) (?v1 A_llist_a_llist_fun$) (?v2 A_llist$)) (= (ldropn$ ?v0 (iterates$a ?v1 ?v2)) (iterates$a ?v1 (fun_app$ (fun_app$d (fun_app$e compow$a ?v0) ?v1) ?v2)))) :named a4))
(assert (! (forall ((?v0 Nat$) (?v1 A_a_fun$) (?v2 A$)) (= (fun_app$ (ldropn$a ?v0) (iterates$ ?v1 ?v2)) (iterates$ ?v1 (fun_app$a (fun_app$b (fun_app$c compow$ ?v0) ?v1) ?v2)))) :named a5))
(assert (! (forall ((?v0 Nat$) (?v1 A_llist$)) (! (= (fun_app$ (ldrop$ (enat$ ?v0)) ?v1) (fun_app$ (ldropn$a ?v0) ?v1)) :pattern ((fun_app$ (ldrop$ (enat$ ?v0)) ?v1)))) :named a6))
(assert (! (= funpow$ compow$a) :named a7))
(assert (! (= funpow$a compow$) :named a8))
(assert (! (forall ((?v0 A_llist$)) (= (fun_app$ (ldrop$ zero$) ?v0) ?v0)) :named a9))
(assert (! (forall ((?v0 Enat$) (?v1 Enat$) (?v2 A_llist$)) (= (fun_app$ (ldrop$ ?v0) (fun_app$ (ldrop$ ?v1) ?v2)) (fun_app$ (ldrop$ (plus$ ?v0 ?v1)) ?v2))) :named a10))
(assert (! (forall ((?v0 Enat$)) (! (= (fun_app$ (ldrop$ ?v0) lNil$) lNil$) :pattern ((ldrop$ ?v0)))) :named a11))
(assert (! (forall ((?v0 Enat$) (?v1 A_a_fun$) (?v2 A_llist$)) (= (fun_app$ (ldrop$ ?v0) (fun_app$ (lmap$ ?v1) ?v2)) (fun_app$ (lmap$ ?v1) (fun_app$ (ldrop$ ?v0) ?v2)))) :named a12))
(assert (! (forall ((?v0 A_a_fun$) (?v1 A$)) (not (lnull$ (iterates$ ?v0 ?v1)))) :named a13))
(assert (! (forall ((?v0 Nat$) (?v1 A_a_fun$) (?v2 A_llist$)) (= (lnull$ (fun_app$ (fun_app$d (fun_app$e compow$a ?v0) (lmap$ ?v1)) ?v2)) (lnull$ ?v2))) :named a14))
(assert (! (forall ((?v0 A_a_fun$) (?v1 A_llist$)) (= (lnull$ (fun_app$ (lmap$ ?v0) ?v1)) (lnull$ ?v1))) :named a15))
(assert (! (forall ((?v0 Nat$)) (! (= (fun_app$ (ldropn$a ?v0) lNil$) lNil$) :pattern ((ldropn$a ?v0)))) :named a16))
(assert (! (forall ((?v0 Nat$) (?v1 A_a_fun$) (?v2 A_llist$)) (= (fun_app$ (ldropn$a ?v0) (fun_app$ (lmap$ ?v1) ?v2)) (fun_app$ (lmap$ ?v1) (fun_app$ (ldropn$a ?v0) ?v2)))) :named a17))
(assert (! (forall ((?v0 A_a_fun$) (?v1 A_llist$)) (= (= (fun_app$ (lmap$ ?v0) ?v1) lNil$) (= ?v1 lNil$))) :named a18))
(check-sat)
;(get-unsat-core)
