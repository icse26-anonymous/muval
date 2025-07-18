; --full-saturate-quant --inst-when=full-last-call --inst-no-entail --term-db-mode=relevant --random-seed=1 --lang=smt2 --tlimit 591
;(set-option :produce-unsat-cores true)
(set-logic ALL_SUPPORTED)
(declare-sort A$ 0)
(declare-sort Nat$ 0)
(declare-sort A_set$ 0)
(declare-sort A_llist_set$ 0)
(declare-sort Nat_a_llist_fun$ 0)
(declare-sort A_llist_a_llist_fun$ 0)
(declare-codatatypes () ((A_llist$ (lNil$) (lCons$ (lhd$ A$) (ltl$ A_llist$)))))
(declare-datatypes () ((Nibble$ (nibble0$) (nibble1$) (nibble2$) (nibble3$) (nibble4$) (nibble5$) (nibble6$) (nibble7$) (nibble8$) (nibble9$) (nibbleA$) (nibbleB$) (nibbleC$) (nibbleD$) (nibbleE$) (nibbleF$))
  (Char$ (char$ (select$ Nibble$) (selecta$ Nibble$)))))
(declare-fun xa$ () A_llist$)
(declare-fun size$ (Char$) Nat$)
(declare-fun zero$ () Nat$)
(declare-fun ldrop$ (A_llist$) Nat_a_llist_fun$)
(declare-fun ltake$ (A_llist$) Nat_a_llist_fun$)
(declare-fun member$ (A_llist$ A_llist_set$) Bool)
(declare-fun fun_app$ (A_llist_a_llist_fun$ A_llist$) A_llist$)
(declare-fun inflsts$ (A_set$) A_llist_set$)
(declare-fun lappend$ (A_llist$) A_llist_a_llist_fun$)
(declare-fun fun_app$a (Nat_a_llist_fun$ Nat$) A_llist$)
(declare-fun size_bool$ (Bool) Nat$)
(declare-fun size_char$ (Char$) Nat$)
(assert (! (not (= (fun_app$ (lappend$ (fun_app$a (ltake$ xa$) zero$)) (fun_app$a (ldrop$ xa$) zero$)) xa$)) :named a0))
(assert (! (forall ((?v0 A_llist$)) (! (= (fun_app$a (ldrop$ ?v0) zero$) ?v0) :pattern ((ldrop$ ?v0)))) :named a1))
(assert (! (forall ((?v0 A_llist$) (?v1 A_llist$) (?v2 A_llist$)) (= (fun_app$ (lappend$ (fun_app$ (lappend$ ?v0) ?v1)) ?v2) (fun_app$ (lappend$ ?v0) (fun_app$ (lappend$ ?v1) ?v2)))) :named a2))
(assert (! (= zero$ zero$) :named a3))
(assert (! (forall ((?v0 Nat$)) (=> (and (=> (= ?v0 zero$) false) (=> (not (= ?v0 zero$)) false)) false)) :named a4))
(assert (! (forall ((?v0 Nat$)) (= (= zero$ ?v0) (= ?v0 zero$))) :named a5))
(assert (! (forall ((?v0 A_llist$)) (! (= (fun_app$a (ltake$ ?v0) zero$) lNil$) :pattern ((ltake$ ?v0)))) :named a6))
(assert (! (forall ((?v0 Char$)) (! (= (size_char$ ?v0) zero$) :pattern ((size_char$ ?v0)))) :named a7))
(assert (! (= (size_bool$ true) zero$) :named a8))
(assert (! (= (size_bool$ false) zero$) :named a9))
(assert (! (forall ((?v0 Nat$)) (! (= (fun_app$a (ltake$ lNil$) ?v0) lNil$) :pattern ((fun_app$a (ltake$ lNil$) ?v0)))) :named a10))
(assert (! (forall ((?v0 A_llist$) (?v1 A_set$) (?v2 A_llist$)) (=> (member$ ?v0 (inflsts$ ?v1)) (= (fun_app$ (lappend$ ?v0) ?v2) ?v0))) :named a11))
(assert (! (forall ((?v0 Char$)) (! (= (size$ ?v0) zero$) :pattern ((size$ ?v0)))) :named a12))
(assert (! (forall ((?v0 A_llist$)) (! (= (fun_app$ (lappend$ lNil$) ?v0) ?v0) :pattern ((fun_app$ (lappend$ lNil$) ?v0)))) :named a13))
(assert (! (forall ((?v0 A_llist$)) (! (= (fun_app$ (lappend$ ?v0) lNil$) ?v0) :pattern ((lappend$ ?v0)))) :named a14))
(assert (! (forall ((?v0 A_llist$) (?v1 A_llist$)) (= (= (fun_app$ (lappend$ ?v0) ?v1) lNil$) (and (= ?v0 lNil$) (= ?v1 lNil$)))) :named a15))
(assert (! (forall ((?v0 A_llist$) (?v1 A_llist$)) (= (= lNil$ (fun_app$ (lappend$ ?v0) ?v1)) (and (= ?v0 lNil$) (= ?v1 lNil$)))) :named a16))
(check-sat)
;(get-unsat-core)
