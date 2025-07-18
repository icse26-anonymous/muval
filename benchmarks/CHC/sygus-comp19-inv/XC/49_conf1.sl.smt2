(set-logic HORN)

(declare-fun inv-f
             (Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int)
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
         (N Int)
         (O Int)
         (P Int))
  (=> (and (inv-f P O N M L K J I H G F E D C B A)
              (= (- P J) 0)
              (= (- O E) 0)
              (>= (- (- 1) A) 0)
              (= (- N A) 0)
              (= (- J A) 0))
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
         (N Int)
         (O Int)
         (P Int))
  (=> (and (= (- P K) 0)
              (= (- O F) 0)
              (= (- N A) 0)
              (= (+ (- 5) F) 0)
              (= K 0)
              (>= (+ (- 1) A) 0))
         (inv-f P O N M L K J I H G F E D C B A))
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
         (B1 Int)
         (C1 Int)
         (D1 Int)
         (E1 Int)
         (F1 Int))
  (let ((a!1 (and (= (- Q X) 0) (= (- L W) 0))))
     (let ((a!2 (and a!1 (not (= (- Q G) 0))))
           (a!4 (and (and a!1 (= (- Q G) 0))
                     (= (- O Q) 0)
                     (= (- I L) 0)
                     (= (- O F1) 0)
                     (= (- I U) 0)
                     (= (- V G) 0)
                     (= (- J G) 0)
                     (= (- T F) 0)))
           (a!5 (and (and a!1 (= (- Q G) 0))
                     (= (+ (- 1) N) 0)
                     (= (- H L) 0)
                     (= (- O N) 0)
                     (= (- I H) 0)
                     (= (- O F1) 0)
                     (= (- I U) 0)
                     (= (- V G) 0)
                     (= (- J G) 0)
                     (= (- T F) 0))))
     (let ((a!3 (and a!2
                     (= (+ (- (- 1) Q) P) 0)
                     (= (+ (- 770 L) K) 0)
                     (= (- O P) 0)
                     (= (- I K) 0)
                     (= (- O F1) 0)
                     (= (- I U) 0)
                     (= (- V G) 0)
                     (= (- J G) 0)
                     (= (- T F) 0))))
     (let ((a!6 (or (and a!1
                         (= (- Q F1) 0)
                         (= (- L U) 0)
                         (= (- X F1) 0)
                         (= (- W U) 0)
                         (= (- V J) 0)
                         (= (- T F) 0))
                    a!3
                    a!4
                    a!5
                    (and a!2
                         (= (- O Q) 0)
                         (= (- I L) 0)
                         (= (- O F1) 0)
                         (= (- I U) 0)
                         (= (- V G) 0)
                         (= (- J G) 0)
                         (= (- T F) 0)))))
       (=> (and (inv-f X W V T S R Q P O N M L K I H G) a!6)
           (inv-f F1 U J F E D C B A E1 D1 C1 B1 A1 Z Y))))))
    ))


(check-sat)
(exit)
