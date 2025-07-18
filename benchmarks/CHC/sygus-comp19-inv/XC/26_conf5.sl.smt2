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
         (S Int))
  (let ((a!1 (and (inv-f S R Q P O N M L K J I H G F E D C B A)
                     (= (- S L) 0)
                     (= (- R K) 0)
                     (= (- Q J) 0)
                     (= (- P H) 0)
                     (= (- O F) 0)
                     (< (+ (- 2) B) 0)
                     (= (- N E) 0)
                     (not (= (+ (- 1) B) 0))
                     (= (- M B) 0)
                     (< (- (- 1) E) 0))))
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
         (S Int))
  (=> (and (= (- S L) 0)
              (= (- R K) 0)
              (= (- Q J) 0)
              (= (- P I) 0)
              (= (- O F) 0)
              (= (- N E) 0)
              (= (- M C) 0)
              (= (+ (- 7) L) 0)
              (= (+ (- 8) K) 0)
              (= (+ (- 7) J) 0)
              (= (+ (- 6) I) 0)
              (= (+ (- 6) F) 0)
              (= (- C E) 0))
         (inv-f S R Q P O N M L K J I H G F E D C B A))
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
         (L1 Int))
  (let ((a!1 (and (= (- N W) 0) (= (- H T) 0))))
     (let ((a!2 (and a!1
                     (>= (+ (- 2) H) 0)
                     (= (+ (- 1 H) G) 0)
                     (= (+ (- 128) M) 0)
                     (= (- M F) 0)
                     (= (- G C) 0)
                     (= (- Z S) 0)
                     (= (- L1 S) 0)
                     (= (- Y R) 0)
                     (= (- A1 R) 0)
                     (= (- X Q) 0)
                     (= (- P Q) 0)
                     (= (- V L) 0)
                     (= (- E L) 0)
                     (= (- U K) 0)
                     (= (- D K) 0))))
     (let ((a!3 (or (and a!1
                         (= (- N F) 0)
                         (= (- H C) 0)
                         (= (- Z L1) 0)
                         (= (- Y A1) 0)
                         (= (- X P) 0)
                         (= (- W F) 0)
                         (= (- V E) 0)
                         (= (- U D) 0))
                    a!2)))
       (=> (and (inv-f Z Y X W V U T S R Q O N M L K J I H G) a!3)
           (inv-f L1 A1 P F E D C B A K1 J1 I1 H1 G1 F1 E1 D1 C1 B1)))))
    ))


(check-sat)
(exit)
