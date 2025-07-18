(set-logic HORN)
(set-info :source |
  Benchmark: ./benchmarks/Table1/sum-acc.ml
  Generated by Refinement Caml
|)
(set-info :status unknown)
(declare-fun |$P0| (Int Int) Bool)
(declare-fun |$P1| (Int Int Int) Bool)
(assert (forall ((x1 Int)(x0 Int)(x2 Int)(x3 Int)) (=> (and (|$P0| x2 x3) (and (<= (+ 1 x1) 0) (and (= x2 (+ 1 x1)) (= x0 (+ x1 x3))))) (|$P0| x1 x0))))
(assert (forall ((x0 Int)(x1 Int)) (=> (and (= x0 0) (= x1 0)) (|$P0| x0 x1))))
(assert (forall ((x1 Int)(x0 Int)(x2 Int)(x3 Int)) (=> (and (|$P0| x2 x3) (and (>= x1 1) (and (= x1 (+ 1 x2)) (= x0 (+ x1 x3))))) (|$P0| x1 x0))))
(assert (forall ((x1 Int)(x0 Int)(x4 Int)(x2 Int)(x3 Int)) (=> (and (|$P1| x2 x3 x4) (and (<= (+ 1 x1) 0) (and (= x2 (+ 1 x1)) (= x3 (+ x0 x1))))) (|$P1| x1 x0 x4))))
(assert (forall ((x0 Int)(x2 Int)(x1 Int)) (=> (and (= x0 0) (= x1 x2)) (|$P1| x0 x2 x1))))
(assert (forall ((x1 Int)(x0 Int)(x4 Int)(x2 Int)(x3 Int)) (=> (and (|$P1| x2 x3 x4) (and (>= x1 1) (and (= x1 (+ 1 x2)) (= x3 (+ x0 x1))))) (|$P1| x1 x0 x4))))
(assert (not (exists ((x0 Int)(x4 Int)(x1 Int)(x3 Int)(x2 Int)) (and (|$P0| x2 x1) (and (|$P1| x2 x3 x4) (and (or (< x0 x4) (> x0 x4)) (= x0 (+ x1 x3))))))))
(check-sat)
