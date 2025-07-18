(set-logic HORN)

(declare-fun str_invariant
             (Bool
              Bool
              Bool
              Bool
              Bool
              Bool
              Bool
              Bool
              Int
              Int
              Int
              Bool
              Bool
              Bool
              Bool
              Bool
              Bool
              Bool
              Bool
              Bool)
             Bool)
(assert (forall ((A Bool)
         (B Bool)
         (C Bool)
         (D Bool)
         (E Bool)
         (F Bool)
         (G Bool)
         (H Bool)
         (I Bool)
         (J Int)
         (K Int)
         (L Int)
         (M Bool)
         (N Bool)
         (O Bool)
         (P Bool)
         (Q Bool)
         (R Bool)
         (S Bool)
         (T Bool))
  (=> (and (str_invariant T S R Q P O N M L K J I H G F E D C B A)
              (not (= R true)))
         false)
    ))
(assert (forall ((A Bool)
         (B Bool)
         (C Bool)
         (D Bool)
         (E Bool)
         (F Bool)
         (G Bool)
         (H Bool)
         (I Bool)
         (J Int)
         (K Int)
         (L Int)
         (M Bool)
         (N Bool)
         (O Bool)
         (P Bool)
         (Q Bool)
         (R Bool)
         (S Bool)
         (T Bool))
  (let ((a!1 (or (not (= (+ (- 10) L) 0)) (= M true)))
           (a!2 (or (and (= I true)
                         (not (= N true))
                         (not (= O true))
                         (not (= M true)))
                    (not (= C true)))))
     (let ((a!3 (and (or (>= (+ (- 3) K) 0) (not (= O true)))
                     (= K 0)
                     (or (< (+ (- 3) K) 0) (= O true))
                     (= I true)
                     (= J 0)
                     (or (= (+ (- 10) L) 0) (not (= M true)))
                     (= L 0)
                     (or (>= (+ (- 4) J) 0) (not (= N true)))
                     a!1
                     a!2
                     (or (< (+ (- 4) J) 0) (= N true))
                     (or (not (= I true))
                         (= N true)
                         (= O true)
                         (= M true)
                         (= C true))
                     (not (= H true))
                     (or (= F true) (not (= E true)))
                     (not (= G true))
                     (or (= F true) (and (= T true) (= S true)))
                     (or (not (= F true)) (= E true))
                     (= D true)
                     (or (not (= F true)) (not (= T true)) (not (= S true)))
                     (= B true)
                     (or (= P true) (not (= M true)))
                     (= R true)
                     (= A true)
                     (or (not (= P true)) (= M true))
                     (= Q true))))
       (=> a!3 (str_invariant T S R Q P O N M L K J I H G F E D C B A))))
    ))
(assert (forall ((A Int)
         (B Bool)
         (C Bool)
         (D Bool)
         (E Bool)
         (F Bool)
         (G Bool)
         (H Bool)
         (I Bool)
         (J Bool)
         (K Bool)
         (L Bool)
         (M Bool)
         (N Bool)
         (O Bool)
         (P Int)
         (Q Int)
         (R Bool)
         (S Int)
         (T Bool)
         (U Bool)
         (V Bool)
         (W Bool)
         (X Bool)
         (Y Bool)
         (Z Bool)
         (A1 Bool)
         (B1 Bool)
         (C1 Bool)
         (D1 Bool)
         (E1 Bool)
         (F1 Bool)
         (G1 Bool)
         (H1 Bool)
         (I1 Bool)
         (J1 Bool)
         (K1 Bool)
         (L1 Int)
         (M1 Int)
         (N1 Bool))
  (let ((a!1 (or (and (= N1 true) (not (= C1 true))) (not (= I1 true))))
           (a!2 (ite (or (not (= K1 true)) (= J1 true))
                     0
                     (ite (and (= K1 true) (= I1 true)) (+ 1 Q) Q)))
           (a!3 (= (- L1 (ite (= J1 true) (+ 1 P) P)) 0))
           (a!4 (- A (ite (and (= K1 true) (= I1 true)) (+ 1 S) S)))
           (a!5 (or (not (= (+ (- 10) A) 0)) (= B true)))
           (a!6 (or (and (= K1 true)
                         (not (= C true))
                         (not (= D true))
                         (not (= B true)))
                    (not (= E1 true)))))
     (let ((a!7 (and (str_invariant A1 Z Y X W V U T S Q P O N M L K J I H F)
                     a!1
                     (or (= J1 true) (not (= C1 true)))
                     (or (not (= N1 true)) (= C1 true) (= I1 true))
                     (or (= K1 true) (not (= I true)))
                     (or (not (= J1 true)) (= C1 true))
                     (or (not (= K1 true)) (= I true))
                     (or (>= (+ (- 3) M1) 0) (not (= D true)))
                     (= (- M1 a!2) 0)
                     (or (< (+ (- 3) M1) 0) (= D true))
                     a!3
                     (or (= (+ (- 10) A) 0) (not (= B true)))
                     (= a!4 0)
                     (or (>= (+ (- 4) L1) 0) (not (= C true)))
                     a!5
                     (or (not (= G1 true)) (not (= W true)) (not (= R true)))
                     a!6
                     (or (< (+ (- 4) L1) 0) (= C true))
                     (or (= E true) (not (= B true)))
                     (or (and (= G1 true) (= W true)) (= R true))
                     (or (and (= H1 true) (= K true)) (not (= G1 true)))
                     (or (not (= K1 true))
                         (= C true)
                         (= D true)
                         (= B true)
                         (= E1 true))
                     (or (not (= E true)) (= B true))
                     (or (= H1 true) (and (= N1 true) (= C1 true)))
                     (or (not (= H1 true)) (not (= K true)) (= G1 true))
                     (not (= F1 true))
                     (or (not (= H1 true)) (not (= N1 true)) (not (= C1 true)))
                     (not (= D1 true))
                     (not (= B1 true))
                     (not (= G true)))))
       (=> a!7
           (str_invariant N1 C1 R G E D C B A M1 L1 K1 J1 I1 H1 G1 F1 E1 D1 B1))))
    ))


(check-sat)
(exit)
