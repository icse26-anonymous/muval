(set-logic HORN)

(declare-fun str_invariant
             (Int
              Bool
              Bool
              Int
              Bool
              Bool
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
              Bool
              Int)
             Bool)
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
         (L Int)
         (M Bool)
         (N Bool)
         (O Int)
         (P Bool)
         (Q Bool)
         (R Int))
  (=> (and (str_invariant R Q P O N M L K J I H G F E D C B A)
              (not (= Q true)))
         false)
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
         (L Int)
         (M Bool)
         (N Bool)
         (O Int)
         (P Bool)
         (Q Bool)
         (R Int))
  (let ((a!1 (or (and (= I true) (>= O 0) (>= (- 15 O) 0)) (not (= H true))))
           (a!2 (or (= Q true) (and (= G true) (not (= F true)))))
           (a!3 (or (and (>= (+ 4 R) 0) (>= (- 4 R) 0) (>= (+ (- 1) R) 0))
                    (not (= I true)))))
     (let ((a!4 (and a!1
                     (= (- O L) 0)
                     a!2
                     (or (not (= I true)) (< O 0) (< (- 15 O) 0) (= H true))
                     (or (= N true) (not (= K true)))
                     (or (not (= Q true)) (not (= G true)) (= F true))
                     (or (>= (- 9 L) 0) (not (= K true)))
                     (= L 0)
                     (or (= H true) (not (= G true)))
                     (or (= M true) (not (= J true)))
                     (or (not (= N true)) (= K true))
                     (or (>= (+ (- 11) L) 0) (not (= J true)))
                     (or (< (- 9 L) 0) (= K true))
                     (or (not (= H true)) (= G true))
                     (or (not (= M true)) (= J true))
                     a!3
                     (or (< (+ (- 11) L) 0) (= J true))
                     (= E true)
                     (= F true)
                     (or (< (+ 4 R) 0)
                         (< (- 4 R) 0)
                         (< (+ (- 1) R) 0)
                         (= I true))
                     (= D true)
                     (= A 0)
                     (= C true)
                     (= B true)
                     (= P true))))
       (=> a!4 (str_invariant R Q P O N M L K J I H G F E D C B A))))
    ))
(assert (forall ((A Bool)
         (B Bool)
         (C Int)
         (D Bool)
         (E Bool)
         (F Int)
         (G Int)
         (H Bool)
         (I Bool)
         (J Bool)
         (K Bool)
         (L Bool)
         (M Bool)
         (N Bool)
         (O Bool)
         (P Bool)
         (Q Bool)
         (R Bool)
         (S Int)
         (T Bool)
         (U Bool)
         (V Int)
         (W Bool)
         (X Bool)
         (Y Bool)
         (Z Int)
         (A1 Int)
         (B1 Bool)
         (C1 Bool)
         (D1 Bool)
         (E1 Bool)
         (F1 Bool)
         (G1 Bool)
         (H1 Bool)
         (I1 Bool)
         (J1 Int))
  (let ((a!1 (or (and (= I1 true) (>= F 0) (>= (- 15 F) 0))
                    (not (= H1 true))))
           (a!2 (or (and (= G1 true) (not (= F1 true))) (= Y true)))
           (a!3 (and (>= (+ 4 J1) 0)
                     (>= (- 4 J1) 0)
                     (or (and (= U true) (>= J1 1)) (not (= U true)))
                     (or (and (= T true) (<= J1 (- 1))) (not (= T true)))))
           (a!4 (and (or (not (= U true)) (< J1 1)) (= U true)))
           (a!5 (and (or (not (= T true)) (> J1 (- 1))) (= T true)))
           (a!6 (ite (and (>= (+ (- 8) F) 0) (>= (- 12 F) 0)) 0 (+ 1 G))))
     (let ((a!7 (and (str_invariant Z X W V U T S R Q P O M L K J I H G)
                     a!1
                     (= (- F C) 0)
                     (or (not (= G1 true)) (= F1 true) (not (= Y true)))
                     (or (not (= I1 true)) (< F 0) (< (- 15 F) 0) (= H1 true))
                     (or (= E true) (not (= B true)))
                     a!2
                     (or (>= (- 9 C) 0) (not (= B true)))
                     (= (- C (+ J1 S)) 0)
                     (or (and (= H1 true) (= M true)) (not (= G1 true)))
                     (or (= D true) (not (= A true)))
                     (or (not (= E true)) (= B true))
                     (or (>= (+ (- 11) C) 0) (not (= A true)))
                     (or (< (- 9 C) 0) (= B true))
                     (or (not (= H1 true)) (not (= M true)) (= G1 true))
                     (or (not (= D true)) (= A true))
                     (or a!3 (not (= I1 true)))
                     (or (< (+ (- 11) C) 0) (= A true))
                     (not (= E1 true))
                     (or (>= (- 7 G) 0) (not (= F1 true)))
                     (or (< (+ 4 J1) 0) (< (- 4 J1) 0) a!4 a!5 (= I1 true))
                     (not (= D1 true))
                     (= (- A1 a!6) 0)
                     (or (< (- 7 G) 0) (= F1 true))
                     (not (= C1 true))
                     (not (= B1 true))
                     (not (= N true)))))
       (=> a!7 (str_invariant J1 Y N F E D C B A I1 H1 G1 F1 E1 D1 C1 B1 A1))))
    ))


(check-sat)
(exit)
