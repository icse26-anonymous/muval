; --full-saturate-quant --inst-when=full-last-call --inst-no-entail --term-db-mode=relevant --random-seed=1 --lang=smt2 --tlimit 388
;(set-option :produce-unsat-cores true)
(set-logic ALL_SUPPORTED)
(declare-sort A$ 0)
(declare-sort Nat$ 0)
(declare-datatypes () ((Num$ (one$) (bit0$ (select$ Num$)) (bit1$ (selecta$ Num$)))
  (A_tree$ (leaf$) (node$ (left$ A_tree$) (val$ A$) (right$ A_tree$)))))
(declare-fun l$ () A_tree$)
(declare-fun r$ () A_tree$)
(declare-fun log$ (Real Real) Real)
(declare-fun plus$ (Num$ Num$) Num$)
(declare-fun real$ (Nat$) Real)
(declare-fun size$ (A_tree$) Nat$)
(declare-fun size1$ (A_tree$) Nat$)
(declare-fun less_eq$ (Num$ Num$) Bool)
(declare-fun numeral$ (Num$) Real)
(assert (! (not (<= (log$ 2.0 (+ 1.0 (+ (real$ (size1$ l$)) (real$ (size1$ r$))))) (+ (log$ 2.0 (+ (real$ (size1$ l$)) (real$ (size1$ r$)))) 1.0))) :named a0))
(assert (! (<= (log$ 2.0 (+ 2.0 (real$ (size$ r$)))) (log$ 2.0 (+ (real$ (size1$ l$)) (real$ (size1$ r$))))) :named a1))
(assert (! (= (+ 1.0 1.0) 2.0) :named a2))
(assert (! (forall ((?v0 Num$)) (= (+ (numeral$ ?v0) 1.0) (numeral$ (plus$ ?v0 one$)))) :named a3))
(assert (! (forall ((?v0 Num$)) (= (+ 1.0 (numeral$ ?v0)) (numeral$ (plus$ one$ ?v0)))) :named a4))
(assert (! (forall ((?v0 Num$)) (= (<= (numeral$ ?v0) 1.0) (less_eq$ ?v0 one$))) :named a5))
(assert (! (forall ((?v0 Num$)) (= (= (numeral$ ?v0) 1.0) (= ?v0 one$))) :named a6))
(assert (! (forall ((?v0 Num$)) (= (= 1.0 (numeral$ ?v0)) (= one$ ?v0))) :named a7))
(assert (! (forall ((?v0 Num$)) (= (= (bit0$ ?v0) one$) false)) :named a8))
(assert (! (forall ((?v0 Num$)) (= (= one$ (bit0$ ?v0)) false)) :named a9))
(assert (! (forall ((?v0 Num$) (?v1 Num$) (?v2 Real)) (= (+ (numeral$ ?v0) (+ (numeral$ ?v1) ?v2)) (+ (numeral$ (plus$ ?v0 ?v1)) ?v2))) :named a10))
(assert (! (forall ((?v0 Num$) (?v1 Num$)) (= (+ (numeral$ ?v0) (numeral$ ?v1)) (numeral$ (plus$ ?v0 ?v1)))) :named a11))
(assert (! (forall ((?v0 Num$) (?v1 Num$)) (= (<= (numeral$ ?v0) (numeral$ ?v1)) (less_eq$ ?v0 ?v1))) :named a12))
(assert (! (forall ((?v0 Num$) (?v1 Num$)) (= (= (numeral$ ?v0) (numeral$ ?v1)) (= ?v0 ?v1))) :named a13))
(assert (! (forall ((?v0 Num$) (?v1 Num$)) (= (= (bit0$ ?v0) (bit0$ ?v1)) (= ?v0 ?v1))) :named a14))
(assert (! (forall ((?v0 Num$) (?v1 Num$)) (= (= (bit0$ ?v0) (bit0$ ?v1)) (= ?v0 ?v1))) :named a15))
(assert (! (forall ((?v0 Num$) (?v1 Num$)) (! (= (plus$ (bit0$ ?v0) (bit0$ ?v1)) (bit0$ (plus$ ?v0 ?v1))) :pattern ((plus$ (bit0$ ?v0) (bit0$ ?v1))))) :named a16))
(check-sat)
;(get-unsat-core)
