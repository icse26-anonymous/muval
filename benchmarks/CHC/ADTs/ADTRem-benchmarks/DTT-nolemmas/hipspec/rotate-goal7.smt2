;(set-logic ALL_SUPPORTED)

(declare-datatypes () ((Lst (cons (head Int) (tail Lst)) (nil))))

(declare-fun len (Lst) Int)
(assert (= (len nil) 0))
(assert (forall ((x Int) (y Lst)) (= (len (cons x y)) (+ 1 (len y)))))

(declare-fun append (Lst Lst) Lst)
(assert (forall ((x Lst)) (= (append nil x) x)))
(assert (forall ((x Int) (y Lst) (z Lst)) (= (append (cons x y) z) (cons x (append y z)))))

(declare-fun rotate (Int Lst) Lst)
(assert (forall ((x Lst)) (= (rotate 0 x) x)))
(assert (forall ((n Int)) (=> (>= n 0) (= (rotate (+ 1 n) nil) nil))))
(assert (forall ((n Int) (y Int) (x Lst)) (=> (>= n 0) (= (rotate (+ 1 n) (cons y x)) (rotate n (append x (cons y nil)))))))

(declare-fun plus (Int Int) Int)
; plus equivalent
(assert (forall ((n Int) (m Int)) (=> (and (>= n 0) (>= m 0)) (= (plus n m) (+ n m)))))










; proven
; conjecture
(assert (not 
(forall ((n Int) (x Lst)) (=> (>= n 0) (= (len (rotate n x)) (len x)))) ; G-rotate-7 
))
(check-sat)
