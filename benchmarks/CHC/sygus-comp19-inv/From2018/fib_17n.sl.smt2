(set-logic HORN)

(declare-fun inv-f (Int Int Int Int Int) Bool)
(assert (forall ((A Int) (B Int) (C Int) (D Int) (E Int))
  (=> (and (inv-f D C B A E) (= (+ (- 3) E) 0) (< (- D A) 0)) false)
    ))
(assert (forall ((A Int) (B Int) (C Int) (D Int) (E Int))
  (=> (and (= B 0) (= (+ (- 1) C) 0) (= (+ (- 1) D) 0) (= E 0))
         (inv-f D C B A E))
    ))
(assert (forall ((A Int)
         (B Int)
         (C Int)
         (D Int)
         (E Int)
         (F Int)
         (G Int)
         (H Int)
         (I Int)
         (J Int))
  (let ((a!1 (and (= I 0)
                     (>= (+ (- (- 1) C) A) 0)
                     (= (- J D) 0)
                     (= (- H C) 0)
                     (= G 0)
                     (= (- F A) 0)
                     (= (+ (- 1) E) 0)))
           (a!2 (= (+ (- (- J D) C) B) 0))
           (a!3 (and (= (- F A) 0) (= (- E I) 0)))
           (a!5 (and (= (+ (- 2) I) 0)
                     (= (- J D) 0)
                     (= (- (+ (- 1) H) C) 0)
                     (= (- G B) 0)
                     (= (- F A) 0)
                     (= E 0))))
     (let ((a!4 (and (= (+ (- 1) I) 0)
                     (>= (- (+ (- 1) C) B) 0)
                     a!2
                     (= (- H C) 0)
                     (= (- (+ (- 1) G) B) 0)
                     a!3))
           (a!6 (and (= (- J D) 0) (= (- H C) 0) (= (- G B) 0) a!3)))
     (let ((a!7 (or a!1
                    (and (= I 0)
                         (>= (- C A) 0)
                         (= (- J D) 0)
                         (= (- H C) 0)
                         (= (- G B) 0)
                         (= (- F A) 0)
                         (= (+ (- 3) E) 0))
                    a!4
                    (and (= (+ (- 1) I) 0)
                         (>= (- B C) 0)
                         (= (- J D) 0)
                         (= (- H C) 0)
                         (= (- G B) 0)
                         (= (- F A) 0)
                         (= (+ (- 2) E) 0))
                    a!5
                    (and (>= (+ (- 3) I) 0) a!6)
                    (and (>= (- (- 1) I) 0) a!6))))
       (=> (and (inv-f D C B A I) a!7) (inv-f J H G F E)))))
    ))


(check-sat)
(exit)
