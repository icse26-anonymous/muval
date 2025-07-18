(set-logic HORN)

(declare-fun inv-f (Int Int Int Int) Bool)
(assert (forall ((A Int) (B Int) (C Int) (D Int))
  (let ((a!1 (and (inv-f D C B A) (< (+ B (* 2 A)) 0))))
       (=> a!1 false))
    ))
(assert (forall ((A Int) (B Int) (C Int) (D Int))
  (=> (and (= B 0) (= A 0)) (inv-f D C B A))))
(assert (forall ((A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) (H Int))
  (let ((a!1 (= (+ (- (+ (- 1) H) B) (* (- 2) A)) 0))
           (a!2 (= (- (+ (- G H) (* 2 B)) A) 0))
           (a!3 (= (- (+ H G (* 2 B)) A) 0))
           (a!4 (= (+ (- (* 2 G) H) F) 0))
           (a!5 (= (+ (- (* (- 2) H) G) E) 0)))
       (=> (and (inv-f D C B A) a!1 (or a!2 a!3) a!4 a!5) (inv-f H G F E)))
    ))


(check-sat)
(exit)
