(set-logic HORN)

(declare-fun InvF (Int Int) Bool)
(assert (forall ((A Int) (B Int))
  (let ((a!1 (and (InvF B A)
                     (>= (- 100 B) 0)
                     (= (+ (- 100) B A) 0)
                     (or (>= (+ (- 100) A) 0) (>= (- (- 1) A) 0)))))
       (=> a!1 false))
    ))
(assert (forall ((A Int) (B Int)) (=> (= (+ (- 1) B) 0) (InvF B A))))
(assert (forall ((A Int) (B Int) (C Int) (D Int))
  (let ((a!1 (and (InvF B A)
                     (>= (- 100 B) 0)
                     (= (+ (- 100) C B) 0)
                     (= (- (+ (- 1) D) B) 0))))
       (=> a!1 (InvF D C)))
    ))


(check-sat)
(exit)
