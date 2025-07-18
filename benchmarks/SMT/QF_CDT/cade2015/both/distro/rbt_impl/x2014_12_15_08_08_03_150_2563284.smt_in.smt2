; --full-saturate-quant --inst-when=full-last-call --inst-no-entail --term-db-mode=relevant --random-seed=1 --lang=smt2 --tlimit 495
;(set-option :produce-unsat-cores true)
(set-logic ALL_SUPPORTED)
(declare-sort A$ 0)
(declare-sort B$ 0)
(declare-sort Nat$ 0)
(declare-datatypes () ((Color$ (r$) (b$))
  (A_b_rbt$ (empty$) (branch$ (select$ Color$) (selecta$ A_b_rbt$) (selectb$ A$) (selectc$ B$) (selectd$ A_b_rbt$)))))
(declare-fun k$ () A$)
(declare-fun v$ () B$)
(declare-fun lt$ () A_b_rbt$)
(declare-fun rt$ () A_b_rbt$)
(declare-fun one$ () Nat$)
(declare-fun inv1$ (A_b_rbt$) Bool)
(declare-fun inv2$ (A_b_rbt$) Bool)
(declare-fun plus$ (Nat$ Nat$) Nat$)
(declare-fun bheight$ (A_b_rbt$) Nat$)
(declare-fun balance_left$ (A_b_rbt$ A$ B$ A_b_rbt$) A_b_rbt$)
(assert (! (not (= (bheight$ (balance_left$ lt$ k$ v$ rt$)) (plus$ (bheight$ lt$) one$))) :named a0))
(assert (! (inv1$ rt$) :named a1))
(assert (! (inv2$ rt$) :named a2))
(assert (! (inv2$ lt$) :named a3))
(assert (! (= (plus$ (bheight$ lt$) one$) (bheight$ rt$)) :named a4))
(assert (! (forall ((?v0 Nat$) (?v1 Nat$) (?v2 Nat$)) (= (= (plus$ ?v0 ?v1) (plus$ ?v2 ?v1)) (= ?v0 ?v2))) :named a5))
(assert (! (forall ((?v0 Nat$) (?v1 Nat$) (?v2 Nat$)) (= (= (plus$ ?v0 ?v1) (plus$ ?v0 ?v2)) (= ?v1 ?v2))) :named a6))
(assert (! (= one$ one$) :named a7))
(assert (! (forall ((?v0 Nat$) (?v1 Nat$) (?v2 Nat$)) (= (= (plus$ ?v0 ?v1) (plus$ ?v2 ?v1)) (= ?v0 ?v2))) :named a8))
(assert (! (forall ((?v0 Nat$) (?v1 Nat$) (?v2 Nat$)) (= (= (plus$ ?v0 ?v1) (plus$ ?v0 ?v2)) (= ?v1 ?v2))) :named a9))
(assert (! (forall ((?v0 Nat$)) (= (= one$ ?v0) (= ?v0 one$))) :named a10))
(assert (! (forall ((?v0 Nat$) (?v1 Nat$) (?v2 Nat$) (?v3 Nat$)) (= (plus$ (plus$ ?v0 ?v1) (plus$ ?v2 ?v3)) (plus$ (plus$ ?v0 ?v2) (plus$ ?v1 ?v3)))) :named a11))
(assert (! (forall ((?v0 Nat$) (?v1 Nat$) (?v2 Nat$)) (= (plus$ (plus$ ?v0 ?v1) ?v2) (plus$ (plus$ ?v0 ?v2) ?v1))) :named a12))
(assert (! (forall ((?v0 Nat$) (?v1 Nat$) (?v2 Nat$)) (= (plus$ (plus$ ?v0 ?v1) ?v2) (plus$ ?v0 (plus$ ?v1 ?v2)))) :named a13))
(assert (! (forall ((?v0 Nat$) (?v1 Nat$) (?v2 Nat$)) (= (plus$ (plus$ ?v0 ?v1) ?v2) (plus$ ?v0 (plus$ ?v1 ?v2)))) :named a14))
(assert (! (forall ((?v0 Nat$) (?v1 Nat$) (?v2 Nat$)) (= (plus$ ?v0 (plus$ ?v1 ?v2)) (plus$ (plus$ ?v0 ?v1) ?v2))) :named a15))
(assert (! (forall ((?v0 Nat$) (?v1 Nat$) (?v2 Nat$) (?v3 Nat$)) (=> (and (= ?v0 ?v1) (= ?v2 ?v3)) (= (plus$ ?v0 ?v2) (plus$ ?v1 ?v3)))) :named a16))
(check-sat)
;(get-unsat-core)
