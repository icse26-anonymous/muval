(set-logic HORN)

(declare-fun inv-f
             (Int Int Int Int Int Int Int Int Int Int Int Int Int Int)
             Bool)
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
  (=> (and (inv-f N M L K J I H G F E D C B A)
              (= (- N I) 0)
              (= (- M G) 0)
              (= E 0)
              (= (- L E) 0)
              (not (= B 0))
              (= (- K B) 0)
              (= (- I G) 0))
         false)
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
         (J Int)
         (K Int)
         (L Int)
         (M Int)
         (N Int))
  (=> (and (= (- N I) 0)
              (= (- M G) 0)
              (= (- L F) 0)
              (= (- K C) 0)
              (= (- I F) 0)
              (= (- G C) 0))
         (inv-f N M L K J I H G F E D C B A))
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
         (J Int)
         (K Int)
         (L Int)
         (M Int)
         (N Int)
         (O Int)
         (P Int)
         (Q Int)
         (R Int)
         (S Int)
         (T Int)
         (U Int)
         (V Int)
         (W Int)
         (X Int)
         (Y Int)
         (Z Int)
         (A1 Int)
         (B1 Int))
  (let ((a!1 (and (= (- L T) 0) (= (- I S) 0))))
     (let ((a!2 (and a!1
                     (not (= L 0))
                     (= (+ (- 1 L) K) 0)
                     (= (+ (- 1 I) H) 0)
                     (= (- K G) 0)
                     (= (- H F) 0)
                     (= (- V P) 0)
                     (= (- B1 P) 0)
                     (= (- U N) 0)
                     (= (- Q N) 0))))
     (let ((a!3 (or (and a!1
                         (= (- L G) 0)
                         (= (- I F) 0)
                         (= (- V B1) 0)
                         (= (- U Q) 0)
                         (= (- S F) 0))
                    a!2)))
       (=> (and (inv-f V U T S R P O N M L K J I H) a!3)
           (inv-f B1 Q G F E D C B A A1 Z Y X W)))))
    ))


(check-sat)
(exit)
