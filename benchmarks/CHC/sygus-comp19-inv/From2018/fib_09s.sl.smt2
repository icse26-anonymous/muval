(set-logic HORN)

(declare-fun inv-f (Int Int Int Int Int Int Int) Bool)
(assert (forall ((A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int))
  (=> (and (inv-f B A G F E D C) (< F 0)) false)))
(assert (forall ((A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int))
  (=> (and (= B 0) (= F 0) (= C 0)) (inv-f B A G F E D C))))
(assert (forall ((A Int)
         (B Int)
         (C Int)
         (D Int)
         (E Int)
         (F Int)
         (G Int)
         (H Int)
         (I Int)
         (J Int)
         (K Int)
         (L Int)
         (M Int)
         (N Int))
  (let ((a!1 (and (= I 0)
                     (= (- (+ (- 1) N) B) 0)
                     (= (- H A) 0)
                     (= (- G M) 0)
                     (= (- F L) 0)
                     (= (- E K) 0)
                     (= (- D J) 0)
                     (= C 0)))
           (a!2 (and (= I 0)
                     (= (- (+ (- 1) N) B) 0)
                     (= (- H A) 0)
                     (= (- G M) 0)
                     (= (- F L) 0)
                     (= (- E K) 0)
                     (= (- D J) 0)
                     (= (+ (- 1) C) 0)))
           (a!3 (and (= (- E K) 0) (= (- D J) 0) (= (+ (- 2) C) 0)))
           (a!7 (and (= (- E K) 0) (= (- D J) 0) (= (+ (- 3) C) 0))))
     (let ((a!4 (and (= (- G M) 0) (= (- F L) 0) a!3))
           (a!6 (and (= (+ (- 2) I) 0)
                     (= (- (+ (- 1) N) B) 0)
                     (= (- H A) 0)
                     (= (- G B) 0)
                     (= (+ (- (- 1) L) F) 0)
                     a!3))
           (a!8 (and (= (+ (- 2) I) 0)
                     (= (- (+ (- 1) N) B) 0)
                     (= (- H A) 0)
                     (= (- G B) 0)
                     (= (+ (- (- 1) L) F) 0)
                     a!7)))
     (let ((a!5 (and (= (+ (- 1) I) 0)
                     (>= (- (+ (- 1) B) A) 0)
                     (= N 0)
                     (= (- H B) 0)
                     a!4)))
     (let ((a!9 (or a!1
                    a!2
                    a!5
                    (and (= (+ (- 1) I) 0)
                         (>= (- A B) 0)
                         (= N 0)
                         (= (- H A) 0)
                         a!4)
                    a!6
                    a!8
                    (and (= (+ (- 3) I) 0)
                         (= (- N B) 0)
                         (= (- H A) 0)
                         (= (- G M) 0)
                         (= (- F L) 0)
                         a!7)
                    (and (= (+ (- 3) I) 0)
                         (= (- N B) 0)
                         (= (- H A) 0)
                         (= (- G M) 0)
                         (= (- F L) 0)
                         (= (- E K) 0)
                         (= (- D J) 0)
                         (= (+ (- 4) C) 0))
                    (and (= (+ (- 4) I) 0)
                         (= (- N B) 0)
                         (= (- H A) 0)
                         (= (- G M) 0)
                         (= (- F L) 0)
                         (= (- E B) 0)
                         (= D 0)
                         (= (+ (- 5) C) 0)))))
       (=> (and (inv-f B A M L K J I) a!9) (inv-f N H G F E D C))))))
    ))


(check-sat)
(exit)
