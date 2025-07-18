; --full-saturate-quant --inst-when=full-last-call --inst-no-entail --term-db-mode=relevant --random-seed=1 --lang=smt2 --tlimit 651
;(set-option :produce-unsat-cores true)
(set-logic ALL_SUPPORTED)
(declare-sort Nat$ 0)
(declare-sort Nat_set$ 0)
(declare-datatypes () ((Num$ (one$) (bit0$ (select$ Num$)) (bit1$ (selecta$ Num$)))))
(declare-codatatypes () ((Nat_llist$ (lNil$) (lCons$ (lhd$ Nat$) (ltl$ Nat_llist$)))))
(declare-fun n$ () Nat$)
(declare-fun p$ () Nat$)
(declare-fun n$a () Nat$)
(declare-fun na$ () Nat$)
(declare-fun less$ (Nat$ Nat$) Bool)
(declare-fun lset$ (Nat_llist$) Nat_set$)
(declare-fun times$ (Nat$ Nat$) Nat$)
(declare-fun member$ (Nat$ Nat_set$) Bool)
(declare-fun smooth$ (Nat$) Bool)
(declare-fun times$a (Num$ Num$) Num$)
(declare-fun hamming$ () Nat_llist$)
(declare-fun numeral$ (Num$) Nat$)
(assert (! (not (member$ (times$ (numeral$ (bit0$ one$)) (times$ (numeral$ (bit0$ one$)) n$)) (lset$ hamming$))) :named a0))
(assert (! (smooth$ na$) :named a1))
(assert (! (smooth$ n$a) :named a2))
(assert (! (less$ (times$ (numeral$ (bit0$ one$)) (times$ (numeral$ (bit0$ one$)) n$)) na$) :named a3))
(assert (! (member$ n$ (lset$ hamming$)) :named a4))
(assert (! (less$ n$ na$) :named a5))
(assert (! (= na$ (times$ p$ n$)) :named a6))
(assert (! (smooth$ n$) :named a7))
(assert (! (forall ((?v0 Num$)) (= (= (bit0$ ?v0) one$) false)) :named a8))
(assert (! (forall ((?v0 Num$)) (= (= one$ (bit0$ ?v0)) false)) :named a9))
(assert (! (forall ((?v0 Num$) (?v1 Num$) (?v2 Nat$)) (= (times$ (numeral$ ?v0) (times$ (numeral$ ?v1) ?v2)) (times$ (numeral$ (times$a ?v0 ?v1)) ?v2))) :named a10))
(assert (! (forall ((?v0 Num$) (?v1 Num$)) (= (times$ (numeral$ ?v0) (numeral$ ?v1)) (numeral$ (times$a ?v0 ?v1)))) :named a11))
(assert (! (forall ((?v0 Nat$)) (= (times$ (numeral$ one$) ?v0) ?v0)) :named a12))
(assert (! (forall ((?v0 Nat$)) (= (times$ ?v0 (numeral$ one$)) ?v0)) :named a13))
(assert (! (forall ((?v0 Num$) (?v1 Num$)) (= (= (bit0$ ?v0) (bit0$ ?v1)) (= ?v0 ?v1))) :named a14))
(assert (! (forall ((?v0 Num$) (?v1 Num$)) (= (= (bit0$ ?v0) (bit0$ ?v1)) (= ?v0 ?v1))) :named a15))
(assert (! (forall ((?v0 Num$) (?v1 Num$)) (= (= (numeral$ ?v0) (numeral$ ?v1)) (= ?v0 ?v1))) :named a16))
(check-sat)
;(get-unsat-core)
