(set-logic HORN)

(declare-fun InvF (Int Int Int Int) Bool)
(assert (forall ((A Int) (B Int) (C Int) (D Int))
  (let ((a!1 (and (InvF D C B A)
                     (= (+ (- 1) C) 0)
                     (< (- D B) 0)
                     (not (= (- B A) 0)))))
       (=> a!1 false))
    ))
(assert (forall ((A Int) (B Int) (C Int) (D Int))
  (let ((a!1 (and (= B 0) (= A 0) (or (= (+ (- 1) C) 0) (= (+ (- 2) C) 0)))))
       (=> a!1 (InvF D C B A)))
    ))
(assert (forall ((A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) (H Int))
  (let ((a!1 (and (InvF D C B A)
                     (= (- (+ (- 1) F) B) 0)
                     (= (- G C) 0)
                     (= (- H D) 0)
                     (>= (- D B) 0)
                     (= (- (- E C) A) 0))))
       (=> a!1 (InvF H G F E)))
    ))


(check-sat)
(exit)
