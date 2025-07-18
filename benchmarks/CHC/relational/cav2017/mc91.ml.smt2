(set-logic HORN)
(set-info :source |
  Benchmark: ./benchmarks/Table1/mc91.ml
  Generated by Refinement Caml
|)
(set-info :status unknown)
(declare-fun |$P0| (Int Int) Bool)
(assert (forall ((x0 Int)(x1 Int)) (=> (and (>= x0 101) (= x0 (+ 10 x1))) (|$P0| x0 x1))))
(assert (forall ((x0 Int)(x3 Int)(x1 Int)(x2 Int)) (=> (and (|$P0| x1 x2) (and (|$P0| x2 x3) (and (<= x0 100) (= x1 (+ 11 x0))))) (|$P0| x0 x3))))
(assert (not (exists ((x0 Int)(x1 Int)) (and (|$P0| x0 x1) (and (<= x0 101) (or (< x1 91) (> x1 91)))))))
(check-sat)
