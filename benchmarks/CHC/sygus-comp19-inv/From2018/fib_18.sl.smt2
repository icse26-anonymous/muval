(set-logic HORN)

(declare-fun inv-f (Int Int Int Int) Bool)
(assert (forall ((A Int) (B Int) (C Int) (D Int))
  (let ((a!1 (and (inv-f D C B A)
                     (= (+ (- 1) A) 0)
                     (< (+ (- (- 1) D) B) 0)
                     (not (= (- C B) 0)))))
       (=> a!1 false))
    ))
(assert (forall ((A Int) (B Int) (C Int) (D Int))
  (=> (and (>= (+ (- 1) B) 0) (= C 0) (= D 0)) (inv-f D C B A))))
(assert (forall ((A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) (H Int))
  (let ((a!1 (and (= (- F B) 0) (= (- E A) 0))))
     (let ((a!2 (and (= (- (+ (- 1) H) D) 0) a!1)))
     (let ((a!3 (and (>= (+ (- (- 1) D) B) 0)
                     (= (+ (- 1) A) 0)
                     (= (- (+ (- 1) G) C) 0)
                     a!2))
           (a!4 (and (>= (+ (- (- 1) D) B) 0)
                     (not (= (+ (- 1) A) 0))
                     (= (- G C) 0)
                     a!2)))
     (let ((a!5 (or a!3
                    a!4
                    (and (>= (- D B) 0) (= (- G C) 0) (= (- H D) 0) a!1))))
       (=> (and (inv-f D C B A) a!5) (inv-f H G F E))))))
    ))


(check-sat)
(exit)
