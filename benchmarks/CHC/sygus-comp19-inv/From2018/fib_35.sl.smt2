(set-logic HORN)

(declare-fun inv-f (Int Int) Bool)
(assert (forall ((A Int) (B Int))
  (let ((a!1 (and (inv-f B A) (>= (- B A) 0) (not (= (- B A) 0)))))
       (=> a!1 false))
    ))
(assert (forall ((A Int) (B Int))
  (=> (and (>= (+ (- 1) A) 0) (= B 0)) (inv-f B A))))
(assert (forall ((A Int) (B Int) (C Int) (D Int))
  (let ((a!1 (and (>= (+ (- (- 1) B) A) 0)
                     (= (- (+ (- 1) D) B) 0)
                     (= (- C A) 0))))
     (let ((a!2 (or (and (>= (- B A) 0) (= (- D B) 0) (= (- C A) 0)) a!1)))
       (=> (and (inv-f B A) a!2) (inv-f D C))))
    ))


(check-sat)
(exit)
