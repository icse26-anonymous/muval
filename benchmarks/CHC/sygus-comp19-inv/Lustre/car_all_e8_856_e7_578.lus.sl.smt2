(set-logic HORN)

(declare-fun str_invariant
             (Bool
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
         (J Bool)
         (K Int)
         (L Int)
         (M Int)
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
         (J Bool)
         (K Int)
         (L Int)
         (M Int)
         (N Bool)
         (O Bool)
         (P Bool)
         (Q Bool)
         (R Bool)
         (S Bool)
         (T Bool))
  (let ((a!1 (or (not (= (+ (- 10) M) 0)) (= N true)))
           (a!2 (or (and (= J true)
                         (not (= O true))
                         (not (= P true))
                         (not (= N true)))
                    (not (= C true))))
           (a!3 (or (not (= E true))
                    (and (>= M 0) (>= (- 10 M) 0) (>= (- 3 L) 0) (>= L 0))
                    (not (= R true))))
           (a!4 (and (= E true)
                     (or (< M 0) (< (- 10 M) 0) (< (- 3 L) 0) (< L 0))))
           (a!5 (or (and (= G true) (>= (- 32766 M) 0)) (not (= F true)))))
     (let ((a!6 (and (or (>= (+ (- 3) L) 0) (not (= P true)))
                     (= L 0)
                     (or (< (+ (- 3) L) 0) (= P true))
                     (= J true)
                     (= K 0)
                     (or (= (+ (- 10) M) 0) (not (= N true)))
                     (= M 0)
                     (or (>= (+ (- 4) K) 0) (not (= O true)))
                     a!1
                     a!2
                     (or (< (+ (- 4) K) 0) (= O true))
                     (or (not (= J true))
                         (= O true)
                         (= P true)
                         (= N true)
                         (= C true))
                     (not (= I true))
                     a!3
                     (or (= F true) (not (= E true)))
                     (not (= H true))
                     (or a!4 (= R true))
                     (or (= G true) (and (= T true) (= S true)))
                     (or (not (= F true)) (= E true))
                     (= D true)
                     (or (not (= G true)) (not (= T true)) (not (= S true)))
                     (= B true)
                     a!5
                     (= A true)
                     (or (not (= G true)) (< (- 32766 M) 0) (= F true))
                     (= Q true))))
       (=> a!6 (str_invariant T S R Q P O N M L K J I H G F E D C B A))))
    ))
(assert (forall ((A Int)
         (B Int)
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
         (P Bool)
         (Q Int)
         (R Bool)
         (S Int)
         (T Int)
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
         (L1 Bool)
         (M1 Int)
         (N1 Bool))
  (let ((a!1 (or (and (= N1 true) (not (= C1 true))) (not (= J1 true))))
           (a!2 (ite (and (not (= L1 true)) (= K1 true))
                     0
                     (ite (and (= L1 true) (= J1 true)) (+ 1 S) S)))
           (a!3 (= (- M1 (ite (= K1 true) (+ 1 Q) Q)) 0))
           (a!4 (- B (ite (and (= L1 true) (= J1 true)) (+ 1 T) T)))
           (a!5 (or (not (= (+ (- 10) B) 0)) (= C true)))
           (a!6 (or (and (= L1 true)
                         (not (= D true))
                         (not (= E true))
                         (not (= C true)))
                    (not (= E1 true))))
           (a!7 (or (not (= G1 true))
                    (and (>= B 0) (>= (- 10 B) 0) (>= (- 3 A) 0) (>= A 0))
                    (not (= R true))))
           (a!8 (and (= G1 true)
                     (or (< B 0) (< (- 10 B) 0) (< (- 3 A) 0) (< A 0))))
           (a!9 (or (and (not (= H1 true)) (not (= K true))) (= G1 true)))
           (a!10 (or (and (= I1 true) (>= (- 32766 B) 0)) (not (= H1 true)))))
     (let ((a!11 (and (str_invariant A1 Z Y X W V U T S Q P O N M L K J I H F)
                      a!1
                      (or (= K1 true) (not (= C1 true)))
                      (or (not (= N1 true)) (= C1 true) (= J1 true))
                      (or (= L1 true) (not (= I true)))
                      (or (not (= K1 true)) (= C1 true))
                      (or (not (= L1 true)) (= I true))
                      (or (>= (+ (- 3) A) 0) (not (= E true)))
                      (= (- A a!2) 0)
                      (or (< (+ (- 3) A) 0) (= E true))
                      a!3
                      (or (= (+ (- 10) B) 0) (not (= C true)))
                      (= a!4 0)
                      (or (>= (+ (- 4) M1) 0) (not (= D true)))
                      a!5
                      a!6
                      (or (< (+ (- 4) M1) 0) (= D true))
                      a!7
                      (or (= H1 true) (= K true) (not (= G1 true)))
                      (or (not (= L1 true))
                          (= D true)
                          (= E true)
                          (= C true)
                          (= E1 true))
                      (or a!8 (= R true))
                      (or (= I1 true) (and (= N1 true) (= C1 true)))
                      a!9
                      (not (= F1 true))
                      (or (not (= I1 true)) (not (= N1 true)) (not (= C1 true)))
                      (not (= D1 true))
                      a!10
                      (not (= B1 true))
                      (or (not (= I1 true)) (< (- 32766 B) 0) (= H1 true))
                      (not (= G true)))))
       (=> a!11
           (str_invariant N1 C1 R G E D C B A M1 L1 K1 J1 I1 H1 G1 F1 E1 D1 B1))))
    ))


(check-sat)
(exit)
