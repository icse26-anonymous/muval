(set-logic HORN)
(set-info :source |
  Benchmark: ./benchmarks/Table1/ack.ml
  Generated by Refinement Caml
|)
(set-info :status unknown)
(declare-fun |$P0| (Int Int Int) Bool)
(assert (forall ((x2 Int)(x1 Int)(x0 Int)) (=> (and (= x0 (+ 1 x1)) (= x2 0)) (|$P0| x2 x1 x0))))
(assert (forall ((x0 Int)(x1 Int)(x3 Int)(x2 Int)) (=> (and (|$P0| x2 1 x3) (and (or (< x0 0) (> x0 0)) (and (= x0 (+ 1 x2)) (= x1 0)))) (|$P0| x0 x1 x3))))
(assert (forall ((x1 Int)(x0 Int)(x5 Int)(x2 Int)(x3 Int)(x4 Int)) (=> (and (|$P0| x1 x2 x4) (and (|$P0| x3 x4 x5) (and (and (or (< x1 0) (> x1 0)) (or (< x0 0) (> x0 0))) (and (= x0 (+ 1 x2)) (= x1 (+ 1 x3)))))) (|$P0| x1 x0 x5))))
(assert (not (exists ((x0 Int)(x1 Int)(x2 Int)) (and (|$P0| x0 x1 x2) (and (>= x0 0) (and (>= x1 0) (<= x2 x1)))))))
(check-sat)
