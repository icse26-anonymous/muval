(set-logic HORN)

(declare-fun inv-f
             (Int
              Int
              Int
              Int
              Int
              Int
              Int
              Int
              Int
              Int
              Int
              Int
              Int
              Int
              Int
              Int
              Int
              Int
              Int
              Int)
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
         (P Int)
         (Q Int)
         (R Int)
         (S Int)
         (T Int))
  (let ((a!1 (and (inv-f T S R Q P O N M L K J I H G F E D C B A)
                     (= (- T N) 0)
                     (= (- S J) 0)
                     (= (- R G) 0)
                     (< (- (+ (- 1) J) G) 0)
                     (= (- Q D) 0)
                     (>= (+ (- 1) J) 0)
                     (= (- P A) 0)
                     (< (- A D) 0))))
       (=> a!1 false))
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
         (T Int))
  (=> (and (= (- T O) 0) (= (- R H) 0) (= (+ (- 7) O) 0) (= H 0))
         (inv-f T S R Q P O N M L K J I H G F E D C B A))
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
         (F1 Int)
         (G1 Int)
         (H1 Int)
         (I1 Int)
         (J1 Int)
         (K1 Int)
         (L1 Int)
         (M1 Int)
         (N1 Int))
  (let ((a!1 (and (= (- U A1) 0) (= (- M Y) 0) (= (- J X) 0))))
     (let ((a!2 (and a!1
                     (>= (- (+ (- 1) P) M) 0)
                     (= (+ (- (- 1) M) L) 0)
                     (= (+ (- 381 U) T) 0))))
     (let ((a!3 (and a!2
                     (>= (- J F) 0)
                     (= (- I F) 0)
                     (= (+ (- 637 T) S) 0)
                     (= (- Q S) 0)
                     (= (- H I) 0)
                     (= (- Q N1) 0)
                     (= (- L R) 0)
                     (= (- H G) 0)
                     (= (- Z P) 0)
                     (= (- C1 P) 0)
                     (= (- W F) 0)
                     (= (- E F) 0))))
     (let ((a!4 (or (and a!1
                         (= (- U N1) 0)
                         (= (- M R) 0)
                         (= (- J G) 0)
                         (= (- Z P) 0)
                         (= (- C1 P) 0)
                         (= (- A1 N1) 0)
                         (= (- X G) 0)
                         (= (- W E) 0))
                    a!3
                    (and a!2
                         (< (- J F) 0)
                         (= (- Q T) 0)
                         (= (- H J) 0)
                         (= (- Q N1) 0)
                         (= (- L R) 0)
                         (= (- H G) 0)
                         (= (- Z P) 0)
                         (= (- C1 P) 0)
                         (= (- W F) 0)
                         (= (- E F) 0)))))
       (=> (and (inv-f A1 Z Y X W V U T S Q P O N M L K J I H F) a!4)
           (inv-f N1 C1 R G E D C B A M1 L1 K1 J1 I1 H1 G1 F1 E1 D1 B1))))))
    ))


(check-sat)
(exit)
